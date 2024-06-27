(* Concrete C *)

(* Instantiation of the Oracular Memory Model
   specialized to our target and compiler. *)

Require Integers Errors.
Require Import Defns Mem Compiler.
Import ListNotations.

Require ssreflect.

Module Functor (cparams: Compiler.CompilerParameters)
               (Import mparams : Mach.MachParameters). 

  Module Import Compiler := Compiler.Functor(cparams). 

  Local Open Scope Z_scope.
  Local Open Scope smem_scope.

  Definition olabel : Type := ident * RTL.code.

  (* Definition of the stack, as a list of frames, each containing
     function name and local array size *)
  Definition frame :=  (RTL.function * nat)%type.

  Definition size_of_frame (frm:frame) : nat :=
    let '(f,asize) := frm in
    (RTL.max_callee_params f) + length(RTL.locals f) + 1 + asize. 
  
  Definition stack := list frame.

  Definition initial_stack : stack := []. 

  Fixpoint sp_of_stack (st:stack) : Z :=
    match st with
    | [] => StkBase
    | f::fs => (sp_of_stack fs) - (size_of_frame f)
    end. 

  Lemma sp_bounded_above: forall st,
      sp_of_stack st <= StkBase.
  Proof.
    induction st. 
    - simpl. lia'.
    - simpl. unfold size_of_frame. destruct a. 
      lia'. 
  Qed.

  Definition sp_bounded_below (st:stack) : Prop :=
    sp_of_stack st >= StkLimit.

  Lemma sp_bounded_below_cons : forall frm st,
      sp_bounded_below (frm::st) -> 
      sp_bounded_below st.
  Proof.
    unfold sp_bounded_below.
    intros.
    simpl in H. lia'.
  Qed.

  (* The StkAllocated map is derived from the stack. Note that it can contain zero-sized regions. *)
  Definition region_of_frame (fbase:Z) (frm:frame) : region := 
    let '(f,asize) := frm in 
    let arr_ofs := ((RTL.max_callee_params f) + length(RTL.locals f) + 1)%nat in 
    (fbase + arr_ofs,asize).

  Definition amap := list region. 

  Lemma in_amap_dec: forall (r:region) (m:amap),
      {In r m} + {~ In r m}.
  Proof.
    induction m. 
    - right. intro. inv H. 
    - destruct IHm. 
      + left. right; auto.
      + simpl. destruct (reg_eq_dec a r); intuition. 
  Qed.

  Fixpoint amap_of_stack (st:stack) : amap :=
    match st with
    | [] => []
    | frm::st' => region_of_frame (sp_of_stack st) frm::amap_of_stack st'
    end.

  Remark amap_cons:
    forall stk frm,
      amap_of_stack (frm::stk) =
      (region_of_frame ((sp_of_stack stk) - (size_of_frame frm)) frm)::(amap_of_stack stk).
  Proof.
    intros.
    simpl. auto. 
  Qed.

  Fixpoint amap_sorted (am:amap) : Prop :=
    match am with
      [] => True
    | rtop::rest => (forall r', In r' rest -> base r' >= bound rtop) /\ amap_sorted rest
    end.

  Lemma amap_sorted_disjoint : forall am,
      amap_sorted am ->
      mutually_disjoint am.
  Proof.
    induction am; intros.
    - auto.
    - simpl. simpl in H. intuition.
      unfold disjoint_from. apply Forall_forall. intros.
      unfold disjoint.
      apply H0 in H2. 
      left. lia. 
  Qed.

  Lemma amap_of_stack_bounded_above: forall st r,
      In r (amap_of_stack st) -> bound r <= StkBase. 
  Proof.
    induction st; intros.
    - inv H.
    - simpl amap_of_stack in H. inv H; auto.
      unfold region_of_frame.  destruct a. simpl.
      pose proof (sp_bounded_above st).  lia'. 
  Qed.
  
  Lemma amap_of_stack_bounded_below  : forall st (SPB: sp_bounded_below st) r,
       In r (amap_of_stack st) -> base r >= sp_of_stack st. 
  Proof.
    induction st; intros. 
    - inv H. 
    - simpl in H.  simpl. 
      destruct H. 
      + unfold region_of_frame in H. destruct a as [info asize].  subst r.  simpl. lia'.  
      + apply sp_bounded_below_cons in SPB. 
        pose proof (IHst SPB r H). lia'. 
  Qed.   

  Lemma amap_of_stack_sorted: forall st (SPB: sp_bounded_below st),
      amap_sorted(amap_of_stack st). 
  Proof.
    induction st. 
    - simpl. auto.
    - simpl. intros.
      split; auto.
      + intros.
        unfold region_of_frame; destruct a as (i,s); simpl. 
        apply sp_bounded_below_cons in SPB.
        apply amap_of_stack_bounded_below in H; auto. 
        lia'. 
      + apply sp_bounded_below_cons in SPB; auto. 
  Qed.

  (* Definition of the heap *)

  (* Heap is represented as a list of object sizes (excluding header)
     paired with bool flags indicating whether object is allocated or not. *)

  Definition obj := (nat*bool)%type.

  Definition heap := list obj.

  Definition initial_heap : heap := [(Z.to_nat (HpLimit - HpBase - 1),false)].

  Fixpoint amap_of_heap' (afp: bool -> bool) (b:Z) (hp:heap) : amap :=
    match hp with
    | [] => []
    | (sz, af)::hp' =>
        if afp af then
          (b+1,sz) ::(amap_of_heap' afp (b + S sz) hp')
        else
          amap_of_heap' afp (b + S sz) hp'
    end.

    Lemma in_amap_of_heap'_dec : forall hp afp b a ,
        {exists r, In r (amap_of_heap' afp b hp) /\ within r a} + {~ exists r, In r (amap_of_heap' afp b hp) /\ within r a }.
    Proof.
      induction hp; intros. 
      - right. intro. destruct H as [r P].  inv P.  inv H. 
      - simpl.  destruct a. destruct (afp b0).
        + destruct (within_dec (b+1,n) a0).
          * simpl. left. exists (b+1,n). split; auto. 
          * destruct (IHhp afp (b + Z.pos (Pos.of_succ_nat n)) a0).
            -- left. destruct e as [r P].  exists r.  simpl. intuition.
            -- right. intro. destruct H as [r [P1 P2]]. simpl in P1. destruct P1. 
               ++ subst. intuition.
               ++ apply n1.  exists r.  intuition.
        + eapply IHhp. 
    Qed.

    Definition amap_of_heap := amap_of_heap' id HpBase.

    Lemma in_amap_of_heap_dec : forall hp a,
      {exists r, In r (amap_of_heap hp) /\ within r a} + {~ exists r, In r (amap_of_heap hp) /\ within r a}.
    Proof.
      intros.  unfold amap_of_heap. eapply in_amap_of_heap'_dec.
    Qed.

    Definition umap_of_heap := amap_of_heap' negb HpBase.


    (* size of object (including header) *)
    Definition obj_size (o:obj) : nat :=
      let '(sz,_) := o in S sz.
    
    (* Total size of heap (including headers) *)
    Definition heap_size (hp:heap) : nat := fold_right plus O (map obj_size hp). 
    
    Lemma heap_size_nil:
      heap_size nil = O.
    Proof.
      unfold heap_size.  simpl. auto.
    Qed.

    Lemma heap_size_cons : forall obj heap,
        heap_size(obj::heap) = (obj_size obj + heap_size heap)%nat. 
    Proof.
      intros.
      unfold heap_size. simpl. auto.
    Qed.

    Lemma heap_size_app: forall h1 h2,
        heap_size(h1++h2) = (heap_size h1 + heap_size h2)%nat. 
    Proof.
      unfold heap_size.
      induction h1; intros. 
      - simpl. auto.
      - simpl. rewrite IHh1. lia'.
    Qed.
    
    Lemma rev_heap_size: forall h,
        heap_size h = heap_size (rev h). 
    Proof.
      induction h; intros. 
      - auto.
      - rewrite heap_size_cons. simpl (rev (a::h)). rewrite heap_size_app.
        rewrite IHh. unfold heap_size at 3. simpl. lia'.
    Qed.

    #[global] Ltac hsize :=
      repeat (try rewrite heap_size_app;
              try rewrite heap_size_cons;
              try rewrite heap_size_nil;
              try rewrite <- rev_heap_size;
              try unfold obj_size).

    #[global] Ltac hsize_in H := 
      repeat (try rewrite heap_size_app in H;
              try rewrite heap_size_cons in H;
              try rewrite heap_size_nil in H;
              try rewrite <- rev_heap_size in H;
              try unfold obj_size in H).

    (* Invariant properties *)
    Definition heap_sizes_partition (hp:heap) : Prop :=
      Z.of_nat (heap_size hp) = HpLimit - HpBase.


    Lemma amap_of_heap'_cons0 : forall afp o hp b,
      amap_of_heap' afp b (o::hp) =
        if afp(snd o) then
          (b+1,fst o)::amap_of_heap' afp (b + obj_size o) hp
        else amap_of_heap' afp (b + obj_size o) hp.                     
    Proof.
      intros.
      unfold amap_of_heap'; fold amap_of_heap'. 
      destruct o as [sz af]. 
      destruct (afp af) eqn:?; simpl; rewrite Heqb0;  auto.
    Qed.
      
    Lemma amap_of_heap'_cons : forall afp o hp b r,
      In r (amap_of_heap' afp b (o::hp)) <->
      (r = (b+1,fst o) /\ afp (snd o) = true) \/ In r (amap_of_heap' afp (b+ obj_size o) hp). 
    Proof.
      intros.
      rewrite amap_of_heap'_cons0. 
      destruct o as [sz af]. simpl. 
      destruct (afp af) eqn:?; simpl; intuition.
    Qed.

    Lemma amap_of_heap'_app0 : forall afp hp1 hp2 b,
        amap_of_heap' afp b (hp1 ++ hp2) = 
        amap_of_heap' afp b hp1 ++ amap_of_heap' afp (b + heap_size hp1) hp2.
    Proof.
      induction hp1; intros.
      - simpl. f_equal. lia'.
      - simpl. destruct a as [sz af].
        destruct (afp af) eqn:?.
        + rewrite IHhp1; simpl; fold (heap_size hp1).
          f_equal; f_equal; f_equal; lia'. 
        + rewrite IHhp1. simpl. fold (heap_size hp1). 
          f_equal;  f_equal; lia'. 
    Qed.

    Lemma amap_of_heap'_app : forall afp hp1 hp2 b r,
        In r (amap_of_heap' afp b (hp1 ++ hp2)) <->
          In r (amap_of_heap' afp b hp1) \/ In r (amap_of_heap' afp (b+ heap_size hp1) hp2). 
    Proof.
      intros.
      rewrite amap_of_heap'_app0. 
      rewrite in_app. split; auto. 
    Qed.

    Lemma amap_of_heap'_bounds : forall h r afp b, 
        In r (amap_of_heap' afp b h) -> b < base r /\ bound r <= b + heap_size h. 
    Proof.
      induction h; intros.
      - inv H. 
      - apply amap_of_heap'_cons in H. destruct H as [[H1 H2]|H].
        +  subst r. simpl.  rewrite heap_size_cons. 
           unfold obj_size; destruct a; simpl; lia'. 
        + rewrite heap_size_cons. 
          pose proof (IHh _ _ _ H).  simpl. lia'.
    Qed.


    Lemma amap_of_heap'_all: forall h r b,
        In r (amap_of_heap' (fun _ : bool => true) b h) ->
        In r (amap_of_heap' id b h) \/ In r (amap_of_heap' negb b h). 
    Proof.
      induction h; intros.
      - inv H.
      - rewrite amap_of_heap'_cons in H. destruct H. 
        + destruct a as [sz af]. simpl in H. destruct af. 
          * left. rewrite amap_of_heap'_cons.  left; intuition.
          * right. rewrite amap_of_heap'_cons.  left; intuition.
        + destruct (IHh _ _ H). 
          * left. rewrite amap_of_heap'_cons; right; auto.
          * right.  rewrite amap_of_heap'_cons; right; auto.
    Qed.
    
   Lemma amap_of_heap'_bounded_above: forall afp hp b r
      (HS: Z.of_nat (heap_size hp) = HpLimit - b),
      In r (amap_of_heap' afp b hp) -> bound r <= HpLimit.
   Proof.
     intros. apply amap_of_heap'_bounds in H.  lia'. 
   Qed.
  
   Corollary amap_of_heap_bounded_above: forall hp r
      (HS: heap_sizes_partition hp),
      In r (amap_of_heap hp) -> bound r <= HpLimit.
   Proof.
     unfold amap_of_heap.
     intros. eapply amap_of_heap'_bounded_above; eauto.
   Qed.

   Corollary umap_of_heap_bounded_above: forall hp r
      (HS: heap_sizes_partition hp),
      In r (umap_of_heap hp) -> bound r <= HpLimit.
   Proof.
     unfold umap_of_heap.
     intros. eapply amap_of_heap'_bounded_above; eauto.
   Qed.

   Lemma amap_of_heap'_bounded_below : forall afp hp r b,
       In r (amap_of_heap' afp b hp) -> base r >= b.
   Proof.
     intros. apply amap_of_heap'_bounds in H.  lia'.
   Qed.

   Corollary amap_of_heap_bounded_below: forall hp r,
      In r (amap_of_heap hp) -> base r >= HpBase.  
   Proof.
     unfold amap_of_heap.
     intros. eapply amap_of_heap'_bounded_below; eauto. 
   Qed.

  Corollary umap_of_heap_bounded_below: forall hp r,
      In r (umap_of_heap hp) -> base r >= HpBase.  
  Proof.
    unfold umap_of_heap.
    intros. eapply amap_of_heap'_bounded_below; eauto. 
  Qed.


  Lemma amap_of_heap'_sorted: forall afp hp b,
      amap_sorted (amap_of_heap' afp b hp). 
  Proof.
    induction hp; intros.
    - simpl. auto.
    - simpl. destruct a. destruct (afp b0). 
      + simpl. split.
        * intros.  replace (b + Z.pos (Pos.of_succ_nat n)) with (b + 1 + n) in H by lia'.
          eapply amap_of_heap'_bounded_below; eauto. 
        * eauto.
      + eauto.
  Qed.

  Corollary amap_of_heap_sorted: forall hp,
      amap_sorted (amap_of_heap hp). 
  Proof.
    unfold amap_of_heap. 
    intros. eapply amap_of_heap'_sorted; eauto.
  Qed.

  (* The value memory *)

  Definition valmem     : Type := Z -> val. 

  Definition updvm (m:valmem) a v := fun (a':Z) => if Z.eq_dec a a' then v else m a'. 

  Lemma updvm_same : forall m a v, updvm m a v a = v. 
  Proof.
    intros.
    unfold updvm. 
    destruct (Z.eq_dec a a); intuition. 
  Qed.

  Lemma updvm_other : forall m a v a', a <> a' -> updvm m a v a' = m a'. 
  Proof.
    intros.
    unfold updvm.
    destruct (Z.eq_dec a a'); intuition.
  Qed. 

  (* The entire memory *)

  Record mem :=
    { stk : stack;
      hp: heap; 
      vmem : valmem;
    }.
  
  Record mem_invariant (m:mem) :=
    { SPB: sp_bounded_below m.(stk);
      HS : heap_sizes_partition m.(hp);
    }.

  Definition initial_mem :=
    Build_mem initial_stack initial_heap init_mmem_values. 

  Lemma initial_invariant : mem_invariant(initial_mem). 
  Proof. 
    unfold initial_mem, initial_stack, initial_heap.
    constructor; simpl. 
    - unfold sp_bounded_below. simpl. pose proof StkBaseLimit_WF. lia.
    - unfold heap_sizes_partition, heap_size. simpl. pose proof HpBaseLimit_WF. lia'.
  Defined. 

  Section WithProgram.

    Variable p:RTL.program.

    (* We now define the operations and prove their properties.*)
       
    (* Initially, we make the invariant explicit in the lemma statements.
       Later, we will package everything together into a dependent pair
       of memory with invariant. Doing it in stages this away helps 
       corral the Coq tedium of working with the dependent pair. *)

    Definition AllocatedStk (m:mem) := amap_of_stack (stk m). 

    Definition AllocatedHp (m:mem) := amap_of_heap (hp m). 

    Local Notation valid_regStk := (valid_regStk_ mem AllocatedStk). 
    Local Notation valid_regHp :=  (valid_regHp_ mem AllocatedHp).
    Local Notation valid_reg :=  (valid_reg_ mem AllocatedStk AllocatedHp). 
    Local Notation in_valid_region := (in_valid_region_ mem AllocatedStk AllocatedHp). 
    Local Notation stable_statusStk := (stable_statusStk_ mem AllocatedStk). 
    Local Notation stable_statusHp :=  (stable_statusHp_ mem AllocatedHp).
    Local Notation stable_status := (stable_status_ mem AllocatedStk AllocatedHp). 

    (* Initial heap *)

    Lemma initial_empty :
      AllocatedStk initial_mem = [] /\  
        AllocatedHp initial_mem = [].
    Proof.
      unfold initial_mem, AllocatedStk, AllocatedHp, initial_heap, amap_of_heap.   simpl. 
      split; auto. 
    Qed.

    (* Properties of Allocated *)

    Lemma AllocatedStk_bounds: forall m r
      (MI: mem_invariant m),
      In r (AllocatedStk m) -> 
      0 < base r /\ bound r < Int64.max_unsigned.
    Proof.
      unfold AllocatedStk.
      intros.
      inv MI. unfold sp_bounded_below in SPB0. 
      pose proof StkLimit_WF.
      pose proof StkBase_WF. 
      pose proof (amap_of_stack_bounded_above (stk m)).
      remember (stk m) as stk. 
      clear Heqstk. 
      generalize dependent stk.
      induction stk0; intros. 
      - inv H. 
      - pose proof (H2 r H).
        inv H. 
        + unfold region_of_frame. destruct a as [f asize]. simpl in *. lia'. 
        + eapply IHstk0; auto.
          * simpl in SPB0.  lia'.
          * intros.  apply H2.  right; auto.  
    Qed. 


    Lemma AllocatedStk_disjoint: forall m
      (MI: mem_invariant m),
        mutually_disjoint (AllocatedStk m).
    Proof.
      intros.
      inv MI. 
      destruct m. simpl in *. 
      epose proof (amap_of_stack_sorted (stk0) SPB0). 
      unfold AllocatedStk.  simpl. 
      eapply amap_sorted_disjoint; eauto.
    Qed.

    Lemma AllocatedHp_bounds: forall m r
      (MI: mem_invariant m),
      In r (AllocatedHp m) ->
      0 < base r /\ bound r < Int64.max_unsigned.
    Proof.
      unfold AllocatedHp. 
      intros.
      inv MI. 
      pose proof HpLimit_WF.
      pose proof HpBase_WF. 
      pose proof (amap_of_heap_bounded_above (hp m) r HS0 H). 
      pose proof (amap_of_heap_bounded_below _ _ H). 
      lia'. 
    Qed.
 
    Lemma AllocatedHp_disjoint: forall m
      (MI: mem_invariant m),
        mutually_disjoint (AllocatedHp m). 
    Proof.
      intros.
      inv MI. 
      eapply amap_sorted_disjoint; eauto. 
      eapply amap_of_heap_sorted; eauto.
    Qed.


    Lemma Allocated_bounds: forall m r
      (MI: mem_invariant m),
        In r (AllocatedStk m ++ AllocatedHp m) ->
        0 < base r /\  bound r < Int64.max_unsigned.
    Proof.
        intros.
        apply in_app in H. destruct H. 
        - eapply AllocatedStk_bounds; eauto.
        - eapply AllocatedHp_bounds; eauto.
    Qed.
      
    Lemma Allocated_disjoint: forall m
      (MI: mem_invariant m),
        mutually_disjoint (AllocatedStk m ++ AllocatedHp m).
    Proof.
      intros.
      apply mutually_disjoint_app. 
      - eapply AllocatedStk_disjoint; eauto. 
      - eapply AllocatedHp_disjoint; eauto.
      - unfold disjoint_lists.  intros.
        inv MI. 
        pose proof StkHp_disjoint. 
        pose proof (amap_of_stack_bounded_below _ SPB0 _ H). 
        unfold sp_bounded_below in *.
        unfold AllocatedHp. 
        unfold disjoint_from. rewrite Forall_forall. intros.
        pose proof (amap_of_heap_bounded_above _ _ HS0 H2).  
        unfold disjoint.
        lia'. 
    Qed.    

    
    Lemma AllocatedHp_distinct: forall m,
      NoDup (map (fun r => base r) (AllocatedHp m)).
    Proof.
      destruct m. 
      unfold AllocatedHp, amap_of_heap; simpl. 
      remember HpBase as b. clear Heqb. generalize dependent b. 
      induction hp0. 
      - simpl. constructor.
      - simpl. destruct a as [sz af].
        destruct (id af). 
        + simpl. econstructor; eauto.
          intro.
          destruct (list_in_map_inv _ _ _ H) as [r [P1 P2]].
          destruct r as [bs sz']. 
          apply amap_of_heap'_bounds in P2. 
          simpl in *. lia'. 
        + intros; eauto. 
    Qed.

    (* Stack operations *)
    Definition stkAlloc (m:mem) (lbl:olabel) (size:nat) : option (region*mem) :=
          let fid := fst lbl in 
          match RTL.lookup_function fid p with
          | Some f => 
              let new_frame := (f,size) in 
              let new_sp := sp_of_stack(new_frame::m.(stk)) in 
              if negb (size =? RTL.sz_a f) || (new_sp <? StkLimit) then
                None
              else
                Some (region_of_frame new_sp new_frame,
                    Build_mem (new_frame::m.(stk))
                              m.(hp)
                                  m.(vmem))
          | None => None
          end.

    Lemma stkAlloc_invariant : forall {m lbl size r m'}
        (MI: mem_invariant m),
        stkAlloc m lbl size = Some(r,m') -> 
        mem_invariant m'. 
    Proof.
      intros. inv MI. 
      unfold stkAlloc in H. 
      allInv. 
      apply orb_false_elim in Heqb; destruct Heqb as [_ Heqb].
      rewrite Z.ltb_ge in Heqb. simpl in *. 
      constructor; simpl; eauto. 
      unfold sp_bounded_below. simpl. lia'. 
    Defined.

    (* Set the private portions of frame to 0 *)
    Definition clear_frame_private (fbase:Z) (frm:frame) vmem :=
      fun (a:Z) => if (fbase <=? a) && (a <? fbase + size_of_frame frm) then
                       if within_dec (region_of_frame fbase frm) a then
                         vmem a
                       else
                         Int64.zero
                     else
                       vmem a.

    Definition stkFree (m:mem) : option mem :=
      match m.(stk) with
      | [] => None
      | frm ::rest =>
          let vmem' := clear_frame_private (sp_of_stack m.(stk)) frm m.(vmem) in 
          Some (Build_mem rest m.(hp) vmem')
      end.

    Lemma stkFree_invariant : forall m m'
        (MI: mem_invariant m),
        stkFree m  = Some m' -> 
        mem_invariant m'. 
    Proof.
      intros.
      inv MI. 
      unfold stkFree in H.
      allInv.
      constructor; simpl; auto. 
      eapply sp_bounded_below_cons; eauto.
    Defined.
    
    (* HEAP OPERATIONS *)

    (* The heap is organized as a sorted list of regions, allocated using first fit.
       We reserve an extra word as a meta-data header to match the expected concrete implementation. *)

   Fixpoint split_heap (h: heap) (s0:nat) : option (heap*obj*heap*heap) :=
      match h with
      | [] => None
      | (s,af)::rest =>
          if af || (s <? s0)%nat then
            match split_heap rest s0 with
              Some(before,new,slop,after) => Some((s,af)::before,new,slop,after)
            | None => None
            end
          else 
            if (s0 =? s)%nat then
              Some ([],(s,true),[],rest)
            else
              Some ([],(s0,true),[((s-s0-1)%nat,false)],rest)
      end.
            
    Lemma split_heap_spec: forall h size left new slop right,
        split_heap h size = Some (left,new,slop,right) -> 
        exists old,
        h = left ++ old::right /\
        obj_size new = S size /\
        (obj_size new + heap_size slop = obj_size old)%nat /\
        snd old = false /\ snd new = true /\ forall o, In o slop -> snd o = false.
    Proof.
      induction h; intros. 
      - inv H.  
      - simpl in H. 
        destruct a as [s af].
        destruct (af || (s <? size)%nat) eqn:?.
        + maybeMonadInv H. 
          destruct (IHh _ _ _ _ _ Heqo) as [old [P1 [P2 [P3 P4]]]].
          subst h. 
          eexists; split; eauto. simpl.  auto.
        + rewrite orb_false_iff in Heqb. destruct Heqb. subst af. rewrite Nat.ltb_ge in H1.
          maybeMonadInv H. 
          * apply Nat.eqb_eq in Heqb. subst s.
            eexists; split. 
            -- simpl; eauto.
            -- unfold heap_size; simpl; intuition. 
          * apply Nat.eqb_neq in Heqb.
            eexists; split. 
            -- simpl; eauto.
            -- unfold heap_size; simpl. intuition. subst o; auto.
    Qed.


    Lemma split_heap_disjoint: forall h size left new slop right b,
        split_heap h size = Some (left,new,slop,right) -> 
        disjoint_from 
          (b + heap_size left+1,size)
          (amap_of_heap' id b h). 
    Proof.
      intros.
      destruct (split_heap_spec _ _ _ _ _ _ H) as [old [P2 [P3 [P4 [P5 [P6 P7]]]]]]. 
      rewrite P2. 
      unfold disjoint_from.  apply Forall_forall. intros r Q.
      apply amap_of_heap'_app in Q. destruct Q.
      - apply amap_of_heap'_bounds in H0.
        unfold disjoint; simpl; lia'.
      - apply amap_of_heap'_cons in H0.  destruct H0 as [[H0 H1]|H0]. 
        + unfold id in H1. rewrite H1 in P5. discriminate.
        + apply amap_of_heap'_bounds in H0. 
          unfold disjoint; simpl; lia'. 
    Qed.


    Lemma split_heap_size_eq : forall hp s before new slop after,
        split_heap hp s = Some(before,new,slop,after) -> 
        heap_size hp = heap_size (before++new::slop++after). 
    Proof.
      intros.
      destruct (split_heap_spec _ _ _ _ _ _ H) as [old [P1 [P2 [P3 _]]]].
      subst hp0.
      repeat rewrite heap_size_app. repeat rewrite heap_size_cons. 
      repeat rewrite heap_size_app.
      lia'.
    Qed.

    
    Definition insert_in_heap (h:heap) (size:nat) : option (region*heap) :=
      match split_heap h size with
      | None => None
      | Some (before, new, slop, after) => Some((HpBase + Z.of_nat (heap_size before) + 1,size),before ++ new::slop ++ after)
      end.

    Lemma insert_in_heap_sizes_partition: forall h s r h'
        (HS: heap_sizes_partition h), 
        insert_in_heap h s = Some(r,h')  ->
        heap_sizes_partition h'.
    Proof.
      unfold heap_sizes_partition, insert_in_heap. 
      intros.
      maybeMonadInv H. 
      pose proof (split_heap_size_eq h s _ _ _ _ Heqo).  
      lia'. 
    Qed.


    Definition hpAlloc (m:mem) (lbl:olabel) (size:nat) : option (region*mem) :=
      match insert_in_heap m.(hp) size with
      | None => None
      | Some (r,h') => Some(r,
                           Build_mem m.(stk) h' m.(vmem))
      end.
          
    Lemma hpAlloc_stk: forall m lbl s r m',
        hpAlloc m lbl s = Some(r,m') ->
        m'.(stk) = m.(stk). 
    Proof.
      unfold hpAlloc. intros.
      maybeMonadInv H.  auto.
    Qed.

    Lemma hpAlloc_partitions: forall m lbl s r m' 
      (HS : heap_sizes_partition m.(hp)), 
        hpAlloc m lbl s = Some(r,m') ->
        heap_sizes_partition m'.(hp). 
    Proof.
      unfold hpAlloc. intros.
      maybeMonadInv H. 
      eapply insert_in_heap_sizes_partition; eauto. 
    Qed.

    Lemma hpAlloc_vmem: forall m lbl s r m', 
        hpAlloc m lbl s = Some(r,m') ->
        m'.(vmem) = m.(vmem). 
      unfold hpAlloc. intros.
      maybeMonadInv H.  auto.
    Qed.

    Lemma hpAlloc_invariant : forall {m lbl size r m'}
        (MI: mem_invariant m),
        hpAlloc m lbl size = Some(r,m') -> 
        mem_invariant m'. 
    Proof.
      intros.
      inv MI. constructor.  
      - erewrite hpAlloc_stk; eauto.
      - eapply hpAlloc_partitions; eauto.
    Qed. 

    (* minimalist and tail-recursive, but rather primitive *)
    Fixpoint locate_in_heap (prev:heap) (h:heap) (a:Z) : option(heap * nat * heap) :=
      match h with
      | [] => None
      | (s,af)::rest =>
          if a =? HpBase + (heap_size prev) + 1 then
            if af then
              Some(prev,s,rest)
            else
              None  
          else 
            locate_in_heap((s,af)::prev) rest a
      end. 

    Lemma locate_in_heap_spec : forall h prev a before s after,
        locate_in_heap prev h a = Some(before,s,after) ->
        List.rev prev ++ h = List.rev before ++ [(s,true)] ++ after.
    Proof.
      induction h; intros.
      - simpl in H.  inv H.
      - simpl in H. destruct a as [s' af]. 
        maybeMonadInv H. 
        +  auto. 
        +  pose proof (IHh _ _ _ _ _ H).
           simpl in H0. rewrite <- app_assoc in H0. simpl in H0. simpl.  auto.
    Qed.

    Lemma locate_in_heap_spec1 : forall h prev a before s after,
        locate_in_heap prev h a = Some(before,s,after) ->
        a = HpBase + (heap_size before) + 1.
    Proof.
      induction h; intros.
      - simpl in H.  inv H.
      - simpl in H. destruct a as [s' af]. 
        maybeMonadInv H. 
        +  lia'. 
        +  eapply IHh. eauto. 
    Qed.

    Lemma locate_in_heap_spec2 : forall h prev r,
        In r (amap_of_heap' id (HpBase + heap_size prev) h) ->
        exists before after, locate_in_heap prev h (base r) = Some(before, size_r r, after).
    Proof.
      induction h; intros. 
      - inv H. 
      - simpl in H. destruct a as [sf af].
        destruct af. 
        + simpl in H. 
          destruct H. 
          * subst r. simpl. 
            destruct (HpBase + heap_size prev + 1 =? HpBase + heap_size prev + 1) eqn:?; try lia.
            do 3 eexists; eauto. 
          * simpl. 
            destruct (base r =? HpBase + heap_size prev + 1) eqn:?. 
            -- apply Z.eqb_eq in Heqb. pose proof (amap_of_heap'_bounds _ _ _ _ H).  lia.
            -- eapply IHh. rewrite heap_size_cons. simpl. 
               replace (HpBase + Z.pos (Pos.of_succ_nat (sf + heap_size prev)))
                         with (HpBase + heap_size prev + Z.pos (Pos.of_succ_nat sf)) by lia; auto.
        + simpl in H. 
          pose proof (IHh ((sf,false):: prev) r). 
          rewrite heap_size_cons in H0 at 1. unfold obj_size in H0 at 1. 
          replace (HpBase + (S sf + heap_size prev)%nat) with (HpBase + heap_size prev + Z.pos (Pos.of_succ_nat sf)) in H0 by lia'.
          destruct (H0 H)  as [before [after Q]].
          simpl. 
          destruct (Z.eqb_spec (base r) (HpBase + heap_size prev + 1)).
          -- pose proof (amap_of_heap'_bounds _ _ _ _ H). lia'.  
          -- eauto. 
    Qed.

    Definition clear_word (b:Z) vmem :=
      fun (a:Z) => if (a =? b) then Int64.zero else vmem a .



    Definition hpFree (m:mem) (a:Z) : option mem :=
      match locate_in_heap [] m.(hp) a  with
      | None => None
      | Some((sp,false)::init,s,(sn,false)::rest) => 
          Some(Build_mem m.(stk) (List.rev init ++ ((s+sp+1+sn+1)%nat,false)::rest) (clear_word (HpBase + (heap_size init) + sp + 1 + s + 1) (clear_word (HpBase + (heap_size init) + sp + 1) m.(vmem))))
      | Some((sp,false)::init,s,rest) => 
          Some(Build_mem m.(stk) (List.rev init ++ ((s+sp+1)%nat,false)::rest) (clear_word (HpBase + (heap_size init) + sp + 1) m.(vmem)))
      | Some(init,s,(sn,false)::rest) => 
          Some(Build_mem m.(stk) (List.rev init ++ ((s+sn+1)%nat,false)::rest) (clear_word ((HpBase + heap_size init) + s + 1) m.(vmem)))
      | Some(init,s,rest) => 
          Some (Build_mem m.(stk) (List.rev init ++ (s,false)::rest) m.(vmem))
      end.

    Lemma hpFree_partitions: forall m a  m' 
      (HS : heap_sizes_partition m.(hp)), 
        hpFree m a = Some m' -> 
        heap_sizes_partition m'.(hp). 
    Proof.
      unfold hpFree, heap_sizes_partition. intros.
      maybeMonadInv H; simpl;
      apply locate_in_heap_spec in Heqo; simpl in Heqo; rewrite Heqo in *; auto;
        rewrite <- HS0; repeat rewrite heap_size_app; unfold heap_size;  simpl; lia. 
    Qed.


    Lemma hpFree_stk: forall m a m',
        hpFree m a = Some m' ->
        m'.(stk) = m.(stk). 
    Proof.
      unfold hpFree. intros.
      maybeMonadInv H;  auto.
    Qed.



    Lemma hpFree_vmem: forall m a0 a  m'
        (HSP : heap_sizes_partition m.(hp)), 
        hpFree m a0 = Some m' ->
        (a < HpBase \/ a >= HpLimit) ->
        m'.(vmem) a = m.(vmem) a. 
      Opaque heap_size.
      pose proof HpBaseLimit_WF as HB. 
      intros.
      unfold hpFree in H. 
      unfold clear_word in H. 
      maybeMonadInv H; hsize; simpl; auto;
        pose proof (locate_in_heap_spec1 _ _ _ _ _ _ Heqo) as H; hsize_in H; simpl in H; 
        pose proof (locate_in_heap_spec _ _ _ _ _ _ Heqo) as H1; simpl in H1; 
        rewrite H1 in HSP; 
        unfold heap_sizes_partition in HSP; hsize_in HSP; 
        match goal with |- (if ?X =? ?Y then _ else _) = _  =>
                          (destruct (Z.eqb_spec X Y); try lia; auto)
        end.
        match goal with |- (if ?X =? ?Y then _ else _) = _  =>
                          (destruct (Z.eqb_spec X Y); try lia; auto)
        end.
      Transparent heap_size.
    Qed.
    
    Lemma hpFree_invariant : forall {m a m'}
        (MI: mem_invariant m),
        hpFree m a = Some m' -> 
        mem_invariant m'. 
    Proof.
      intros.
      inv MI. 
      constructor. 
      - erewrite hpFree_stk; eauto.
      - eapply hpFree_partitions; eauto.
    Qed.


    Lemma hpFree_charact_success: forall m r                       
        (MI: mem_invariant m),                                         
        In r (AllocatedHp m) -> 
        hpFree m (base r) <> None.
    Proof.
      unfold AllocatedHp, amap_of_heap. 
      intros. 
      inv MI. 
      intro. 
      pose proof (locate_in_heap_spec2 (hp m) [] r).  simpl in H1.  rewrite Z.add_0_r in H1. 
      destruct (H1 H) as [before [after P]].
      unfold hpFree in H0. 
      rewrite P in H0. destruct before; inv H0. destruct after; inv H3. 
      destruct o as [sn b].  destruct b; inv H2. 
      destruct o as [sn b].  destruct b; inv H3. destruct after; inv H2. 
      destruct o as [sn0 b0].  destruct b0; inv H3. destruct after; inv H2. 
      destruct o as [sn0 b0].  destruct b0; inv H3. 
    Qed.
      


    Lemma hpFree_charact: forall m m' a
      (MI: mem_invariant m), 
      hpFree m a = Some m' ->
       exists r, base r = a /\
      Permutation (r::AllocatedHp m') (AllocatedHp m) /\
      AllocatedStk m' = AllocatedStk m.
   Proof.
      unfold AllocatedHp, amap_of_heap, AllocatedStk.  
      intros.
      unfold hpFree in H. 
      maybeMonadInv H; simpl;  
      pose proof (locate_in_heap_spec _ _ _ _ _ _ Heqo) as P; simpl in P; rewrite P in *; clear P; 
      pose proof (locate_in_heap_spec1 _ _ _ _ _ _ Heqo) as Q. 
      - rewrite Z.add_0_r in Q. 
        unfold amap_of_heap'; simpl. 
        exists (a,n); split; auto; split; auto.
        subst a. eapply Permutation_refl. 
      - rewrite Z.add_0_r in Q. 
        unfold amap_of_heap'; simpl. 
        exists (a,n); split; auto; split; auto.
        subst a. eapply Permutation_refl. 
      - rewrite Z.add_0_r in Q. 
        unfold amap_of_heap'; simpl. 
        exists (a,n); split; auto; split; auto.
        subst a. replace (HpBase + Z.pos (Pos.of_succ_nat n) + Z.pos (Pos.of_succ_nat n0))
                   with (HpBase + Z.pos (Pos.of_succ_nat (n + n0 + 1))) by lia. eapply Permutation_refl. 
      - repeat rewrite amap_of_heap'_app0. simpl. 
        exists (a,n); split; auto; split; auto.
        subst a. repeat rewrite heap_size_app. repeat rewrite heap_size_cons. simpl. 
        rewrite app_nil_r. rewrite Permutation_middle.
        rewrite <- app_assoc. eapply Permutation_app_head.  simpl. 
        unfold heap_size at 5; simpl. 
        rewrite <- rev_heap_size. 
        replace (HpBase + Z.pos (Pos.of_succ_nat (n0 + heap_size h1)) + 1) with (HpBase + (heap_size h1 + S (n0 + 0))%nat + 1) by lia.
        eapply perm_swap. 
      - repeat rewrite amap_of_heap'_app0. simpl. 
        exists (a,n); split; auto; split; auto.
        subst a. repeat rewrite heap_size_app. repeat rewrite heap_size_cons. simpl. 
        repeat rewrite <- app_assoc. simpl.  
        rewrite Permutation_middle.
        eapply Permutation_app_head. 
        repeat rewrite <- rev_heap_size.  
        unfold heap_size at 9; simpl. 
        replace (HpBase + (heap_size h1 + S (n0 + 0))%nat + 1) with
              (HpBase + Z.pos (Pos.of_succ_nat (n0 + heap_size h1)) + 1) by lia. 
        eapply perm_swap.
      - repeat rewrite amap_of_heap'_app0. simpl. 
        exists (a,n); split; auto; split; auto.
        subst a. repeat rewrite heap_size_app. repeat rewrite heap_size_cons. simpl. 
        repeat rewrite <- app_assoc. simpl.  
        repeat rewrite <- rev_heap_size. 
        rewrite heap_size_nil. 
        replace
             (HpBase + (heap_size h1 + S (n0 + 0))%nat + Z.pos (Pos.of_succ_nat n) +
              Z.pos (Pos.of_succ_nat n1))
          with 
          (HpBase + (heap_size h1 + S (n0 + 0))%nat + Z.pos (Pos.of_succ_nat (n + n1 + 1))) by lia.
        rewrite Permutation_middle.
        eapply Permutation_app_head.
        replace (HpBase + (heap_size h1 + S (n0 + 0))%nat + 1) with
         (HpBase + Z.pos (Pos.of_succ_nat (n0 + heap_size h1)) + 1) by lia.
        eapply perm_swap.
      - repeat rewrite amap_of_heap'_app0. simpl. 
        exists (a,n); split; auto; split; auto.
        subst a. repeat rewrite heap_size_app. repeat rewrite heap_size_cons. simpl. 
        repeat rewrite <- app_assoc. simpl.  
        repeat rewrite <- rev_heap_size. 
        rewrite <- Permutation_middle.
        rewrite heap_size_nil.
        replace (HpBase + (heap_size h1 + S (n0 + 0))%nat + 1)
                  with (HpBase + Z.pos (Pos.of_succ_nat (n0 + heap_size h1)) + 1) by lia.
        eapply Permutation_refl.
      - repeat rewrite amap_of_heap'_app0. simpl. 
        exists (a,n); split; auto; split; auto.
        subst a. repeat rewrite heap_size_app. repeat rewrite heap_size_cons. simpl. 
        repeat rewrite <- app_assoc. simpl.  
        repeat rewrite <- rev_heap_size. 
        rewrite heap_size_nil. 
        rewrite Permutation_middle.
        eapply Permutation_app_head.
        replace (HpBase + (heap_size h1 + S (n0 + 0))%nat + 1) with
          (HpBase + Z.pos (Pos.of_succ_nat (n0 + heap_size h1)) + 1) by lia.
        apply perm_skip.
        replace (HpBase + (heap_size h1 + S (n0 + 0))%nat + Z.pos (Pos.of_succ_nat n) + 1)
                  with (HpBase + heap_size h1 + Z.pos (Pos.of_succ_nat (n + n0 + 1)) + 1) by lia.
        apply perm_skip.
        replace (HpBase + (heap_size h1 + S (n0 + 0))%nat + Z.pos (Pos.of_succ_nat n) + Z.pos (Pos.of_succ_nat n1)) with (HpBase + heap_size h1 + Z.pos (Pos.of_succ_nat (n + n0 + 1)) + Z.pos (Pos.of_succ_nat n1)) by lia. 
        eapply Permutation_refl.
      - repeat rewrite amap_of_heap'_app0. simpl. 
        exists (a,n); split; auto; split; auto.
        subst a. repeat rewrite heap_size_app. repeat rewrite heap_size_cons. simpl. 
        repeat rewrite <- app_assoc. simpl.  
        repeat rewrite <- rev_heap_size. 
        rewrite heap_size_nil. 
        replace (HpBase + (heap_size h1 + S (n0 + 0))%nat + Z.pos (Pos.of_succ_nat n) + Z.pos (Pos.of_succ_nat n1)) with (HpBase + heap_size h1 + Z.pos (Pos.of_succ_nat (n + n0 + 1 + n1 + 1))) by lia. 
        replace (HpBase + (heap_size h1 + S (n0 + 0))%nat + 1) with (HpBase + Z.pos (Pos.of_succ_nat (n0 + heap_size h1)) + 1) by lia. 
        apply Permutation_middle. 
   Qed.

    Corollary hpFree_validity: forall m a m' 
      (MI: mem_invariant m), 
      hpFree m a = Some m' -> 
      forall r a,
        in_valid_region m' r a -> 
        in_valid_region m r a.
    Proof.
      intros.
      destruct (hpFree_charact _ _ _ MI H) as [r' [P1 [P2 P3]]].
      unfold in_valid_region, valid_reg, valid_regStk, valid_regHp in *.
      destruct H0. split; auto.
      destruct H1.
      - left.  rewrite <- P3. auto. 
      - right. eapply Permutation_in in P2; eauto. right. auto.
    Qed.

    (** PERTURB **)     

    (* For this implementation, perturb does nothing. *)
    Definition perturb (m:mem) (lbl:olabel) : option mem := Some m. 

    Lemma perturb_invariant : forall m lbl m',
        mem_invariant m ->
        perturb m lbl = Some m' ->
        mem_invariant m'.
    Proof.
      intros.
      unfold perturb in *. 
      inv H0; auto. 
    Defined.

    (** LOAD AND STORE **)

    (* Other operations are done directly on memory. 
       We just check that address is accessible. *)

    (* Accessible regions correspond to those tagged public in the target. *)

    Definition allocated (s:stack) (h:heap) (a:Z) := 
      (exists r, In r (amap_of_stack s ++ amap_of_heap h) /\ within r a).

    Lemma allocated_dec : forall s h a,
        {allocated s h a} + {~ allocated s h a}. 
    Proof.
      unfold allocated.
      intros. 
      induction s.
      - simpl. 
        eapply in_amap_of_heap_dec. 
      - destruct IHs. 
        + left. destruct e as [r [P1 P2]].
          exists r. split; auto.
          right; auto. 
        + simpl. destruct (within_dec (region_of_frame ((sp_of_stack s) - (size_of_frame a0)) a0) a). 
          * left. exists (region_of_frame ((sp_of_stack s) - (size_of_frame a0)) a0). 
            split; auto.  
          * right. intros [r [P1 P2]]. 
            apply n. 
            inv P1; try contradiction. 
            exists r; auto.
    Qed. 

    Definition beyond_sp (s:stack) (a:Z) :=
      StkLimit <= a < (sp_of_stack s).

    Definition in_unallocated_hp (h:heap) (a:Z) := 
      (exists r, In r (umap_of_heap h) /\ within r a).

    Lemma in_unallocated_hp_dec : forall hp a,
      {in_unallocated_hp hp a} + {~ in_unallocated_hp hp a}.
    Proof.
      unfold in_unallocated_hp, umap_of_heap. 
      intros.
      eapply in_amap_of_heap'_dec.
    Qed.

    Definition accessible (s:stack) (h:heap) (a:Z) :=
      allocated s h a \/ beyond_sp s a \/ in_unallocated_hp h a.  

    Lemma accessible_dec : forall s h a,  {accessible s h a} + {~accessible s h a}.
    Proof.
      intros.
      unfold accessible. 
      unfold beyond_sp.
      destruct (Z_le_gt_dec StkLimit a).  
      -  destruct (Z_lt_ge_dec a (sp_of_stack s)). 
        + left. right. lia.
        + destruct (allocated_dec s h a). 
          * left. left. auto.
          * destruct (in_unallocated_hp_dec h a).  
            -- left. intuition.
            -- right. intuition lia. 
      - destruct (allocated_dec s h a). 
        * left. left. auto.
        * destruct (in_unallocated_hp_dec h a).
          -- left. intuition.
          -- right.  intuition lia. 
    Defined.

    Lemma in_valid_region_accessible: forall m r (a:Z),
        in_valid_region m r a ->
        accessible (stk m) (hp m) a. 
    Proof.  
      intros.
      unfold in_valid_region in H. destruct H as [H1 H2].
      unfold accessible. left.
      exists r. 
      unfold valid_regStk in H2; intuition. 
    Qed.
      
    Definition load (m:mem) (a:Z) : option val :=  
      if accessible_dec m.(stk) m.(hp) a then 
        Some (m.(vmem) a)
      else None.

    Local Notation stable_Allocated := (stable_Allocated_ mem AllocatedStk AllocatedHp load).

    Definition store (m:mem) (a:Z) (v:val) : option mem := 
      if accessible_dec m.(stk) m.(hp) a then
        Some (Build_mem m.(stk) m.(hp) (updvm m.(vmem) a v))
      else
        None.

    Lemma store_invariant : forall m a v m',
        mem_invariant m ->
        store m a v = Some m' ->
        mem_invariant m'.
    Proof.
      unfold store.
      intros. inv H. 
      allInv.
      simpl in *. 
      constructor; auto.
    Defined.
    
    (** PROOFS OF MEMORY PROPERTIES *)

    (* properties of stkAlloc *)
    Lemma stkAlloc_charact : forall m m' lbl sz r, 
        stkAlloc m lbl sz = Some (r, m') ->
        AllocatedStk m' = r::AllocatedStk m
        /\ AllocatedHp m' = AllocatedHp m.
    Proof.
      intros.
      unfold stkAlloc in H.
      allInv. 
      unfold AllocatedStk. simpl.  auto.
    Qed. 

    Corollary stkAlloc_validity : forall m m' lbl sz r',
        stkAlloc m lbl sz = Some (r', m') ->
        forall r a,
          in_valid_region m r a ->
          in_valid_region m' r a. 
    Proof.
      intros.
      apply stkAlloc_charact in H. 
      unfold in_valid_region in *.  intuition.
      unfold valid_reg, valid_regStk, valid_regHp  in *. 
      rewrite H1.  rewrite H2. 
      intuition.
   Qed.
    
    Lemma stkAlloc_charact_size : forall m m' lbl sz r, 
      stkAlloc m lbl sz = Some (r, m') ->
      size_r r = sz.
    Proof.
      intros.
      unfold stkAlloc in H. 
      allInv.
      auto.
    Qed. 

    Lemma stkAlloc_stable_Allocated :
      forall m m' lbl sz r
        (MI: mem_invariant m), 
        stkAlloc m lbl sz = Some (r, m') ->
        stable_Allocated m m'. 
    Proof.
      unfold stable_Allocated. 
      intros.
      unfold load. 
      pose proof (stkAlloc_validity _ _ _ _ _ H _ _ H0). 
      pose proof (in_valid_region_accessible _ _ _ H0). 
      pose proof (in_valid_region_accessible _ _ _ H1). 
      destruct (accessible_dec (stk m) (hp m) a); try contradiction.
      destruct (accessible_dec (stk m') (hp m') a); try contradiction.
      unfold stkAlloc in H.  
      allInv. auto.
    Qed.



    (* properties of stkFree *)

    Lemma stkFree_charact_success:
      forall m,
        AllocatedStk m <> [] -> 
        stkFree m <> None.
    Proof.
      unfold AllocatedStk in *. 
      intros.
      unfold stkFree.
      destruct (stk m).
      - simpl in H. exfalso. apply H; auto.
      - intro. inv H0. 
    Qed.
      

    Lemma stkFree_charact :
      forall m m',
        stkFree m = Some m' ->
        exists r, AllocatedStk m = r::AllocatedStk m' /\
                    AllocatedHp m' = AllocatedHp m.
    Proof.
      unfold AllocatedStk.
      unfold stkFree.
      intros.
      maybeMonadInv H. simpl. 
      eexists. split.
      f_equal; auto.
      simpl. 
      destruct m; auto.
    Qed.
      
    Corollary stkFree_validity : forall m m',
        stkFree m  = Some m' -> 
        forall r a,
          in_valid_region m' r a ->
          in_valid_region m r a. 
    Proof.
      intros.
      destruct (stkFree_charact  _ _ H) as [r' [P1 P2]].
      unfold in_valid_region, valid_reg, valid_regStk, valid_regHp in *.  intuition.
      - left.  rewrite P1.  right; auto.
      - right. rewrite P2 in H0.  auto.
    Qed.


    Lemma stkFree_stable_Allocated:
      forall m m'
      (MI: mem_invariant m),
      stkFree m = Some m' -> 
      stable_Allocated m' m.
    Proof.
      unfold stable_Allocated.
      intros.
      pose proof (stkFree_validity _ _ H _ _ H0). 
      unfold load. 
      pose proof (in_valid_region_accessible _ _ _ H0). 
      pose proof (in_valid_region_accessible _ _ _ H1). 
      destruct (accessible_dec (stk m) (hp m) a); try contradiction.
      destruct (accessible_dec (stk m') (hp m') a); try contradiction. clear a0 a1. 
      unfold stkFree in H.  
      allInv. simpl in *. 
      f_equal. 
      unfold clear_frame_private.
      replace (sp_of_stack s - size_of_frame f + size_of_frame f) with (sp_of_stack s) by lia. 
      destruct (Z.leb_spec (sp_of_stack s - size_of_frame f) a); simpl; auto. 
      destruct (Z.ltb_spec a (sp_of_stack s)); simpl; auto.   
      destruct H0. unfold valid_reg, valid_regStk in H5. unfold AllocatedStk in H5. simpl in H5. 
      destruct H5. 
      - exfalso.
        assert (B: a >= sp_of_stack s). 
        {  destruct r as [bs sz].
           eapply amap_of_stack_bounded_below in H5.  simpl in H5.
           - unfold within in H0. simpl in H0. lia'. 
           - inv MI. rewrite Heqs in SPB0. eapply sp_bounded_below_cons; eauto. 
        } 
        lia'.                
      - exfalso.
        unfold within in H0. unfold valid_regHp, AllocatedHp in H5. simpl in H5. inv MI.
        pose proof (amap_of_heap_bounded_above _ _ HS0 H5). 
        pose proof StkHp_disjoint. rewrite Heqs in SPB0. unfold sp_bounded_below in  SPB0. simpl in SPB0. lia'. 
    Qed. 
      
    
    (* properties of hpAlloc *)

    Remark amap_of_heap'_afp : forall h afp,
        (forall o:obj, In o h -> afp(snd o) = false) ->
        forall b, amap_of_heap' afp b h = []. 
    Proof.
      induction h; intros. 
      - auto. 
      - simpl. 
        destruct a as [sz zf].  simpl in *.
        assert (afp zf = false).
        { eapply (H (sz,zf)).  left; auto. } rewrite H0. 
        rewrite IHh; auto. 
    Qed.


    Lemma  hpAlloc_charact: forall m lbl sz r m'
      (MI: mem_invariant m),                                    
      hpAlloc m lbl sz = Some(r, m') ->
      Permutation (r::AllocatedHp m) (AllocatedHp m') /\
        AllocatedStk m' = AllocatedStk m. 
    Proof.
      intros.
      unfold hpAlloc in H. maybeMonadInv H. 
      unfold insert_in_heap in Heqo.
      maybeMonadInv Heqo.
      destruct (split_heap_spec _ _ _ _ _ _ Heqo0) as [old [P2 [P3 [P4 [P5 [P6 P7]]]]]]. 
      inv MI.
      unfold AllocatedHp. 
      split; auto. 
      simpl. 
      rewrite P2. 
      unfold amap_of_heap. 
      rewrite amap_of_heap'_app0.
      rewrite amap_of_heap'_app0.
      repeat rewrite -> amap_of_heap'_cons0.
      unfold id at 2 6 . rewrite P5.  rewrite P6.
        unfold obj_size in *. destruct o as [bs' sz']. inv P3. simpl in *. 
        destruct old as [bs'' sz'']. inv P4; simpl in *. 
        rewrite amap_of_heap'_app0. 
        pose proof (amap_of_heap'_afp _ id P7).
        rewrite H. simpl. 
        replace (HpBase + heap_size h2 + Z.pos (Pos.of_succ_nat (sz + heap_size h1))) with
          (HpBase + heap_size h2 + Z.pos (Pos.of_succ_nat sz) + heap_size h1) by lia'. 
        eapply Permutation_middle.
    Qed.

    Corollary hpAlloc_validity: forall m lbl sz r0 m'
      (MI: mem_invariant m),
      hpAlloc m lbl sz = Some(r0,m') -> 
      forall r a,
        in_valid_region m r a -> 
        in_valid_region m' r a.
    Proof.
      intros.
      apply hpAlloc_charact in H; auto. destruct H as [P1 P2]. 
      unfold in_valid_region, valid_reg, valid_regStk, valid_regHp in *.
      rewrite P2. 
      destruct H0; split; auto.
      destruct H0;[(left; auto)|].
      right.
      eapply Permutation_in in P1; eauto.  right; auto.
    Qed.

    Lemma hpAlloc_charact_size: forall m lbl m'  sz r,
     (*  (MI: mem_invariant m), *)
      hpAlloc m lbl sz = Some(r, m') -> 
      sz <= size_r r.
    Proof.
      intros.
      unfold hpAlloc in H.  maybeMonadInv H. 
      unfold insert_in_heap in Heqo. 
      maybeMonadInv Heqo. simpl. lia'. 
    Qed.
      

    Lemma hpAlloc_stable_Allocated : forall m lbl m' sz r
      (MI: mem_invariant m),
      hpAlloc m lbl sz = Some(r, m') -> 
      stable_Allocated m m'.
    Proof.
      intros.
      unfold stable_Allocated; intros.
      pose proof (hpAlloc_validity _ _ _ _ _ MI H _ _ H0). 
      unfold load.
      pose proof (in_valid_region_accessible _ _ _ H0). 
      pose proof (in_valid_region_accessible _ _ _ H1). 
      destruct (accessible_dec (stk m) (hp m) a); try contradiction.
      destruct (accessible_dec (stk m') (hp m') a); try contradiction. clear a0 a1. 
      unfold hpAlloc in H. 
      allInv. simpl.  auto.
    Qed.


    (* properties of hpFree *)

    Lemma hpFree_stable_Allocated : forall m a m'
      (MI: mem_invariant m),                                           
      hpFree m a = Some m' -> 
      stable_Allocated m' m.
    Proof.
      intros.
      unfold stable_Allocated; intros.
      pose proof (hpFree_validity _ _ _  MI H _ _ H0).
      unfold load.
      pose proof (in_valid_region_accessible _ _ _ H0). 
      pose proof (in_valid_region_accessible _ _ _ H1). 
      destruct (accessible_dec (stk m') (hp m') a0); try contradiction.
      destruct (accessible_dec (stk m) (hp m) a0); try contradiction. clear a1 a2. 
      inv MI. 
      unfold hpFree in H;  allInv; unfold clear_word; auto. 
      - simpl in *.
        destruct (Z.eqb_spec a0 (HpBase + 0 + n + 1)); auto. 
        exfalso.
        pose proof (locate_in_heap_spec _ _ _ _ _ _ Heqo) as H; simpl in H. 
        unfold in_valid_region in H1. destruct H1. unfold valid_reg, valid_regHp, valid_regStk in H4. 
        destruct H4. 
        + unfold heap_sizes_partition in HS0. rewrite H in HS0.
          repeat rewrite heap_size_cons in HS0.  simpl in HS0. 
          unfold AllocatedStk in H4. 
          pose proof (amap_of_stack_bounded_below _ SPB0 _ H4). 
          unfold sp_bounded_below in SPB0. 
          assert (a0 < HpLimit) by lia.
          pose proof StkHp_disjoint.
          unfold within in H1. 
          lia.
        + unfold AllocatedHp, amap_of_heap in H4. 
          rewrite H in H4.  simpl in H4. 
          destruct H4. 
          * subst r. unfold within in H1. simpl in H1. lia.
          * apply amap_of_heap'_bounded_below in H4. unfold within in H1. lia.
      - simpl in *. 
        destruct (Z.eqb_spec a0 (HpBase + Z.pos (Pos.of_succ_nat (n0 + fold_right Init.Nat.add 0%nat (map obj_size h1))) + n + 1)); auto.
        exfalso.
        pose proof (locate_in_heap_spec _ _ _ _ _ _ Heqo) as H; simpl in H. 
        unfold in_valid_region in H1. destruct H1. unfold valid_reg, valid_regHp, valid_regStk in H4. 
        destruct H4. 
        + unfold heap_sizes_partition in HS0. rewrite H in HS0.
          repeat rewrite heap_size_app in HS0.  repeat rewrite heap_size_cons in HS0.  simpl in HS0. 
          unfold AllocatedStk in H4. 
          pose proof (amap_of_stack_bounded_below _ SPB0 _ H4). 
          unfold sp_bounded_below in SPB0. 
          rewrite <- rev_heap_size in HS0.  unfold heap_size at 1 2 in HS0. simpl in HS0. 
          assert (a0 < HpLimit) by lia.
          pose proof StkHp_disjoint.
          unfold within in H1. 
          lia.
        + unfold AllocatedHp, amap_of_heap in H4. 
          rewrite H in H4. rewrite <- app_assoc in H4. 
          rewrite amap_of_heap'_app0 in H4.  apply in_app in H4.  simpl in H4.
          fold (heap_size h1) in e.
          rewrite rev_heap_size in e.
          unfold within in H1. 
          destruct H4 as [P | [P | [P | P]]].
          * pose proof (amap_of_heap'_bounds _ _ _ _ P). lia.
          * subst r. simpl in H1. lia. 
          * subst r. simpl in H1. lia.
          * pose proof (amap_of_heap'_bounds _ _ _ _ P). lia.
      - simpl in *. 
        destruct (Z.eqb_spec a0 (HpBase + heap_size h1 + n0 + 1)); auto.
        exfalso.
        pose proof (locate_in_heap_spec _ _ _ _ _ _ Heqo) as H; simpl in H. 
        unfold in_valid_region in H1. destruct H1. unfold valid_reg, valid_regHp, valid_regStk in H4. 
        destruct H4. 
        + unfold heap_sizes_partition in HS0. rewrite H in HS0.
          repeat rewrite heap_size_app in HS0.  repeat rewrite heap_size_cons in HS0.  simpl in HS0.
          unfold heap_size at 2 3 in HS0. simpl in HS0. 
          unfold AllocatedStk in H4. 
          pose proof (amap_of_stack_bounded_below _ SPB0 _ H4). 
          unfold sp_bounded_below in SPB0. 
          rewrite <- rev_heap_size in HS0.  
          assert (a0 < HpLimit) by lia.
          pose proof StkHp_disjoint.
          unfold within in H1. 
          lia.
        + unfold AllocatedHp, amap_of_heap in H4. 
          rewrite H in H4. rewrite <- app_assoc in H4. 
          rewrite amap_of_heap'_app0 in H4.  apply in_app in H4.  simpl in H4.
          unfold within in H1. 
          destruct H4 as [P | [P | ?]]; auto. 
          * pose proof (amap_of_heap'_bounds _ _ _ _ P). rewrite <- rev_heap_size in H4. lia.
          * subst r. simpl in H1. rewrite <- rev_heap_size in H1. lia. 
      - simpl in *. 
        destruct (Z.eqb_spec a0 (HpBase + heap_size h1 + n0 + 1)); auto.
        exfalso.
        pose proof (locate_in_heap_spec _ _ _ _ _ _ Heqo) as H; simpl in H. 
        unfold in_valid_region in H1. destruct H1. unfold valid_reg, valid_regHp, valid_regStk in H4. 
        destruct H4. 
        + unfold heap_sizes_partition in HS0. rewrite H in HS0.
          repeat rewrite heap_size_app in HS0.  repeat rewrite heap_size_cons in HS0.  simpl in HS0.
          unfold heap_size at 2 3 in HS0. simpl in HS0. 
          unfold AllocatedStk in H4. 
          pose proof (amap_of_stack_bounded_below _ SPB0 _ H4). 
          unfold sp_bounded_below in SPB0. 
          rewrite <- rev_heap_size in HS0.  
          assert (a0 < HpLimit) by lia.
          pose proof StkHp_disjoint.
          unfold within in H1. 
          lia.
        + unfold AllocatedHp, amap_of_heap in H4. 
          rewrite H in H4. rewrite <- app_assoc in H4. 
          rewrite amap_of_heap'_app0 in H4.  apply in_app in H4.  simpl in H4.
          unfold within in H1. 
          destruct H4 as [P | [P | [P | P]]].
          * pose proof (amap_of_heap'_bounds _ _ _ _ P). rewrite <-  rev_heap_size in H4. lia.
          * subst r. simpl in H1. rewrite <- rev_heap_size in H1. lia. 
          * subst r. simpl in H1. rewrite <- rev_heap_size in H1. lia.
          * pose proof (amap_of_heap'_bounds _ _ _ _ P). rewrite <- rev_heap_size in H4. lia.
      - simpl in *. 
        destruct (Z.eqb_spec a0 (HpBase + heap_size h1 + n0 + 1 + n + 1));
          [| destruct (Z.eqb_spec a0 (HpBase + heap_size h1 + n0 + 1))]; auto; exfalso. 
        + pose proof (locate_in_heap_spec _ _ _ _ _ _ Heqo) as H; simpl in H. 
          unfold in_valid_region in H1. destruct H1. unfold valid_reg, valid_regHp, valid_regStk in H4. 
          destruct H4. 
          * unfold heap_sizes_partition in HS0. rewrite H in HS0.
            repeat rewrite heap_size_app in HS0.  repeat rewrite heap_size_cons in HS0.  simpl in HS0.
            unfold heap_size at 2 in HS0. simpl in HS0.  
            rewrite <- rev_heap_size in HS0.  
            unfold AllocatedStk in H4. 
            pose proof (amap_of_stack_bounded_below _ SPB0 _ H4). 
            unfold sp_bounded_below in SPB0. 
            assert (a0 < HpLimit) by lia.
            pose proof StkHp_disjoint.
            unfold within in H1. 
            lia.
          * unfold AllocatedHp, amap_of_heap in H4. 
            rewrite H in H4. rewrite <- app_assoc in H4. 
            rewrite amap_of_heap'_app0 in H4.  apply in_app in H4.  simpl in H4.
            unfold within in H1. 
            destruct H4 as [P | [P | P]]. 
            -- pose proof (amap_of_heap'_bounds _ _ _ _ P). rewrite <- rev_heap_size in H4. lia.
            -- subst r. simpl in H1. rewrite <- rev_heap_size in H1. lia. 
            -- pose proof (amap_of_heap'_bounds _ _ _ _ P). rewrite <- rev_heap_size in H4. lia.
        + pose proof (locate_in_heap_spec _ _ _ _ _ _ Heqo) as H; simpl in H. 
          unfold in_valid_region in H1. destruct H1. unfold valid_reg, valid_regHp, valid_regStk in H4. 
          destruct H4. 
          * unfold heap_sizes_partition in HS0. rewrite H in HS0.
            repeat rewrite heap_size_app in HS0.  repeat rewrite heap_size_cons in HS0.  simpl in HS0.
            unfold heap_size at 2 in HS0. simpl in HS0.  
            rewrite <- rev_heap_size in HS0.  
            unfold AllocatedStk in H4. 
            pose proof (amap_of_stack_bounded_below _ SPB0 _ H4). 
            unfold sp_bounded_below in SPB0. 
            assert (a0 < HpLimit) by lia.
            pose proof StkHp_disjoint.
            unfold within in H1. 
            lia.
          * unfold AllocatedHp, amap_of_heap in H4. 
            rewrite H in H4. rewrite <- app_assoc in H4. 
            rewrite amap_of_heap'_app0 in H4.  apply in_app in H4.  simpl in H4.
            unfold within in H1. 
            destruct H4 as [P | [P | P]]. 
            -- pose proof (amap_of_heap'_bounds _ _ _ _ P). rewrite <- rev_heap_size in H4. lia.
            -- subst r. simpl in H1. rewrite <- rev_heap_size in H1. lia. 
            -- pose proof (amap_of_heap'_bounds _ _ _ _ P). rewrite <- rev_heap_size in H4. lia.
    Qed.



    (* properties of compiler perturbations *)
    Lemma perturb_stable_status :
      forall m lbl m', 
        perturb m lbl = Some m' -> 
        stable_status m m'.
    Proof.
      unfold perturb, stable_status, stable_statusStk, stable_statusHp.
      intros.
      inv H; auto.
    Qed.

    Corollary perturb_validity: forall m lbl m',
      perturb m lbl = Some m' ->
      forall r a,
        in_valid_region m r a <-> 
        in_valid_region m' r a.
    Proof.
      intros.
      apply perturb_stable_status in H. unfold stable_status, stable_statusStk, stable_statusHp in H.  destruct H. 
      unfold in_valid_region, valid_reg, valid_regStk, valid_regHp in *.
      rewrite H.  rewrite H0. intuition.  
    Qed.


    Lemma perturb_stable_Allocated :
      forall m lbl m', 
        perturb m lbl = Some m' -> 
        stable_Allocated m m' /\
        stable_Allocated m' m. 
    Proof.
      intros.
      unfold perturb in H. 
      inv H. 
      split; unfold stable_Allocated; intros; auto. 
    Qed.

    (* properties of store *)

    Lemma store_stable_status : forall m a v m',
      store m a v = Some m' ->
      stable_status m m'.
    Proof.
      unfold stable_status, stable_statusStk, stable_statusHp, store. 
      intros.
      maybeMonadInv H.   simpl.  intuition.
    Qed. 

    Lemma store_can_write_Allocated :
      forall m a r v
      (MI: mem_invariant m), 
      in_valid_region m r a -> 
      store m a v <> None.
    Proof.
      intros.
      apply in_valid_region_accessible  in H; auto. 
      unfold store.
      destruct (accessible_dec (stk m) (hp m) a); try contradiction.
      intro X. inv X. 
    Qed.

    (* properties of load *)
    Lemma load_can_read_Allocated :
      forall m a r
      (MI: mem_invariant m), 
      in_valid_region m r a -> 
      load m a <> None.
    Proof.
      intros.
      apply in_valid_region_accessible in H; auto. 
      unfold load.
      destruct (accessible_dec (stk m) (hp m) a); try contradiction.
      intro X. inv X. 
    Qed.


    (* read after write properties *)
    Lemma store_post_accessible:
      forall m m' a v,
        store m a v = Some m' ->
        forall a', 
        accessible (stk m) (hp m) a' <-> 
        accessible (stk m') (hp m')  a'. 
    Proof.
      intros.
      unfold store in H. 
      allInv.
      unfold accessible in *. 
      unfold AllocatedStk in *.  simpl. 
      intuition.
    Qed.

    Lemma store_accessible:
      forall m m' a v,
        store m a v = Some m' ->
        accessible (stk m) (hp m) a. 
    Proof.
      intros.
      unfold store in H. 
      allInv.
      auto.
    Qed.

    Lemma store_charact_read_back :
      forall m m' a v,
        store m  a v = Some m' ->
        load  m' a   = Some v.
    Proof.
      intros.
      unfold load,store in *. 
      pose proof (store_accessible _ _ _ _ H). 
      destruct (store_post_accessible _ _ _ _ H a).  pose proof (H1 H0). 
      inv H. 
      destruct (accessible_dec (stk m) (hp m) a); try contradiction. 
      inv H5.  simpl. 
      destruct (accessible_dec (stk m) (hp m) a);  try contradiction. 
      f_equal. simpl. apply updvm_same. 
    Qed.
      
    Lemma store_stable_everywhere_else_value :
      forall m m' a r v,
      store m a v = Some m' ->
      in_valid_region m r a -> 
      forall a', a' <> a -> load m a' = load m' a'.
    Proof.
      intros. 
      pose proof (store_accessible _ _ _ _ H). 
      unfold load. 
      destruct (accessible_dec (stk m)  (hp m) a'). 
      - destruct (store_post_accessible _ _ _ _  H a'). pose proof (H3 a0). 
        unfold store in *. 
        destruct (accessible_dec (stk m) (hp m) a); try contradiction. 
        inv H. 
        simpl. 
        destruct (accessible_dec (stk m) (hp m) a'); try contradiction. 
        f_equal.
        rewrite updvm_other; auto. 
      - destruct (accessible_dec (stk m') (hp m') a'); eauto. 
        rewrite <- (store_post_accessible _ _ _ _ H) in a0. 
        contradiction.
    Qed.

    (** Whew. 
        Finally, redefine everything in terms of a memory that carries the invariants with it. *)

    Import ssreflect.

    (* Arthur's trick: https://stackoverflow.com/questions/63027162/abstraction-typing-error-resulting-from-case-eq-and-rewriting-in-coq  *)
    Ltac monadInvDep H :=
      match type of H  with
      | (((match ?E as _ return _ with _ => _ end) _ = _)) => 
        (revert H;
         generalize (eq_refl E);
         case: {2 3} E;
         intros;
         try discriminate)
      end.

    Definition mem' := { m:mem | mem_invariant m }. 
    Definition initial_mem' : mem' := exist _ initial_mem initial_invariant.

    Definition AllocatedStk' (m':mem') : list region := AllocatedStk (proj1_sig m').
    Definition AllocatedHp' (m':mem') : list region := AllocatedHp (proj1_sig m').

    Definition valid_regStk' m' r := In r (AllocatedStk' m').
    Definition valid_regHp' m' (r:region) := In r (AllocatedHp' m'). 
    Definition valid_reg' m' r := valid_regStk' m' r \/ valid_regHp' m' r. 

    Definition in_valid_region' m' r a := within r a /\ valid_reg' m' r.

    Definition stable_statusStk' m' m1' := AllocatedStk' m' = AllocatedStk' m1'.
    Definition stable_statusHp' m' m1' := Permutation (AllocatedHp' m') (AllocatedHp' m1'). 
    Definition stable_status' m' m1' := stable_statusStk' m' m1' /\ stable_statusHp' m' m1'.
    

    Definition allocated' (m':mem') := allocated (stk (proj1_sig m')) (hp (proj1_sig m')). 

    Definition beyond_sp' (m':mem') := beyond_sp (stk (proj1_sig m')). 

    Definition in_unallocated_hp' (m':mem') := in_unallocated_hp (hp (proj1_sig m')).

    Definition accessible' (m':mem') := accessible (stk (proj1_sig m')) (hp (proj1_sig m')).

    Lemma accessible_spec': forall m' a,
        accessible' m' a <-> allocated' m' a \/ beyond_sp' m' a \/ in_unallocated_hp' m' a. 
    Proof.
      unfold accessible', allocated', beyond_sp', in_unallocated_hp'. 
      unfold accessible. 
      intros; split; intros; auto.
    Qed.

    Lemma accessible_dec' : forall m' a,  {accessible' m' a} + {~accessible' m' a}.
    Proof.
      intros.
      unfold accessible'.  eapply accessible_dec; eauto.
    Defined.


    Definition stkAlloc' (m':mem') (lbl:olabel) (size:nat) : option (region * mem') :=  
      let m := proj1_sig m' in
      let inv := proj2_sig m' in
      let x := stkAlloc m lbl size in
      (match x as y return (x = y -> _) with
       | None => fun H : x = None => None
       | Some (r,m1) => fun H: x = Some(r,m1) => Some(r,exist _ m1 (stkAlloc_invariant inv H))
       end) (eq_refl x). 


    Definition stkFree' (m':mem') : option mem' :=
      let m := proj1_sig m' in
      let inv := proj2_sig m' in
      let x := stkFree m in
      (match x as y return (x = y -> _) with
       | None => fun H : x = None => None
       | Some m1 => fun H : x = Some m1 => Some(exist _ m1 (stkFree_invariant _ _ inv H))
       end) (eq_refl x). 

    (* This seems easier to work with externally. *)
    Definition load' (m':mem') (a:Z) :=
      if accessible_dec' m' a then 
        Some ((proj1_sig m').(vmem) a)
      else None.

    Definition naive_load' (m':mem') := load (proj1_sig m'). 

    Lemma equiv_naive_load' : forall m' a, load' m' a = naive_load' m' a. 
    Proof.
      unfold load',naive_load',load.
      intros.
      destruct (accessible_dec' m' a); simpl; destruct (accessible_dec (stk (proj1_sig m')) _ a); try (unfold accessible' in *; contradiction); auto.
    Qed. 

   Definition stable_Allocated' m' m1' := forall a r,
        in_valid_region' m' r a ->
        load' m' a = load' m1' a.

   
    Definition store' (m':mem') (a:Z) (v:val) : option mem'. 
      refine(
      match accessible_dec' m' a with
      | left _ => let m := proj1_sig m' in
                  let inv := proj2_sig m' in 
                  Some (exist _ (Build_mem m.(stk) m.(hp) (updvm m.(vmem) a v)) _) 
      | right _ => None
      end).
      inversion inv. 
      constructor; simpl; auto.
    Defined.
   
    (* adds a weird sumbool
    Definition store' (m':mem') (a:addr) (v:val) : option mem' :=
      if accessible_dec' m' a then
        let m := proj1_sig m' in
        let inv := proj2_sig m' in 
        Some (exist _ (Build_mem m.(stk) (updvm m.(vmem) a v)) inv) 
      else
        None.
     *)

    Definition naive_store' (m':mem') (a:Z) (v:val) : option mem' :=
      let m := proj1_sig m' in
      let inv := proj2_sig m' in
      let x := store m a v in
      (match x as y return (x = y -> _) with
       | None => fun H : x = None => None
       | Some m1 => fun H: x = Some m1 => Some(exist _ m1 (store_invariant _ _ _ _ inv H))
       end) (eq_refl x).

    Lemma equiv_naive_store': forall m' a v, store' m' a v = naive_store' m' a v. 
    Proof.
      intros.
      unfold store', naive_store', store.
      unfold store_invariant. 
      unfold accessible_dec'. 
      destruct (accessible_dec (stk (proj1_sig m')) (hp (proj1_sig m')) a); auto.
    Qed.      



    Definition perturb' (m':mem') (lbl:olabel) : option mem' :=
      let m := proj1_sig m' in
      let inv := proj2_sig m' in
      let x := perturb m lbl in 
      (match x as y return (x = y -> _) with
       | None => fun H : x = None => None
       | Some m1 => fun H: x = Some m1 => Some(exist _ m1 (perturb_invariant _ lbl _ inv H))
       end) (eq_refl x).

    Lemma initial_empty' :
      AllocatedStk' initial_mem' = [] /\  
      AllocatedHp' initial_mem'= [].
    Proof.
      unfold initial_mem', AllocatedStk', AllocatedHp'.  simpl. 
      eapply initial_empty.
    Qed.

    Lemma Allocated_disjoint': forall m',
        mutually_disjoint (AllocatedStk' m' ++ AllocatedHp' m').
    Proof.
      unfold AllocatedStk', AllocatedHp'. 
      intros.  
      eapply Allocated_disjoint; eauto.
      destruct m' as [m inv]. 
      simpl; auto.
    Qed.

    Lemma Allocated_bounds': forall m' r,
      In r (AllocatedStk' m' ++ AllocatedHp' m') -> 
      0 < base r /\ bound r < Int64.max_unsigned.
    Proof.
      unfold AllocatedStk', AllocatedHp'. 
      intros.
      eapply Allocated_bounds; eauto.
      destruct m' as [m inv]. 
      simpl; auto.
    Qed.

    
    Lemma AllocatedHp_distinct': forall m',
      NoDup (map (fun r => base r) (AllocatedHp' m')).
    Proof.
      unfold AllocatedHp'. 
      intros.
      eapply AllocatedHp_distinct.
    Qed.

    
    Lemma stkAlloc_charact' :
      forall (m' m1' : mem') (lbl : olabel) (sz : nat) (r : region),
        stkAlloc' m' lbl sz = Some (r, m1') ->
        AllocatedStk' m1' = r :: AllocatedStk' m' /\
        AllocatedHp' m1' = AllocatedHp' m'.
    Proof.
      unfold stkAlloc', AllocatedStk', AllocatedHp'. 
      intros.
      destruct m' as [m inv].
      destruct m1' as [m1 inv1].
      simpl in *. 
      monadInvDep H. 
      destruct a. inv H. 
      eapply stkAlloc_charact; eauto.
    Qed.


    Lemma stkAlloc_charact_size': 
      forall (m' m1' : mem') (lbl : olabel) (sz : nat) (r : region),
        stkAlloc' m' lbl sz = Some (r, m1') ->
        size_r r = sz.
    Proof.
      unfold stkAlloc'. 
      intros.
      monadInvDep H. 
      destruct a.  inv H.
      eapply stkAlloc_charact_size; eauto.
    Qed.


    Lemma stkAlloc_stable_Allocated' :
      forall (m' m1' : mem') (lbl: olabel) (sz : nat) (r : region),
        stkAlloc' m' lbl sz = Some (r, m1') ->
        stable_Allocated' m' m1'.
    Proof.
      unfold stkAlloc', stable_Allocated'.  
      intros.
      repeat rewrite equiv_naive_load'. unfold naive_load'.  
      destruct m' as [m inv].
      destruct m1' as [m1 inv1].
      simpl in *. 
      monadInvDep H.
      destruct a0.  inv H. 
      eapply stkAlloc_stable_Allocated; eauto.
    Qed.


    Lemma stkFree_charact_success':
      forall m',
        AllocatedStk' m' <> [] -> 
        stkFree' m' <> None.
    Proof.
      unfold AllocatedStk', stkFree'. 
      intros.
      destruct m' as [m inv].
      simpl in *. 
      apply stkFree_charact_success in H. 
      intro. 
      apply H. 
      monadInvDep H0. auto.
    Qed.

    Lemma stkFree_charact' :
      forall m' m1',
        stkFree' m' = Some m1' ->
        exists r, AllocatedStk' m' = r::AllocatedStk' m1' /\
                    AllocatedHp' m1' = AllocatedHp' m'.
    Proof.
      unfold AllocatedStk', AllocatedHp', stkFree'. 
      intros.
      destruct m' as [m inv].
      simpl in *. 
      monadInvDep H. inv H. 
      destruct (stkFree_charact _ _ e) as [m1 [P1 P2]].
      exists m1. split; auto.
    Qed.

    
    Lemma stkFree_stable_Allocated' :
      forall m' m1',
      stkFree' m' = Some m1' -> 
      stable_Allocated' m1' m'.
    Proof.
      unfold stable_Allocated', stkFree'.
      intros.
      repeat rewrite equiv_naive_load'.
      unfold naive_load', in_valid_region', valid_regStk' in *.
      destruct m' as [m inv].
      destruct m1' as [m1 inv1].
      simpl in *. 
      monadInvDep H.  inv H. 
      eapply stkFree_stable_Allocated; eauto.
    Qed.


    Definition hpAlloc' (m':mem') (lbl:olabel) (size:nat) : option (region * mem') :=
      let m := proj1_sig m' in
      let inv := proj2_sig m' in
      let x := hpAlloc m lbl size in
      (match x as y return (x = y -> _) with
       | None => fun H : x = None => None
       | Some (r,m1) => fun H: x = Some(r,m1) => Some(r,exist _ m1 (hpAlloc_invariant inv H))
       end) (eq_refl x).


    Definition hpFree' (m':mem') (a:Z) : option mem' :=
      let m := proj1_sig m' in
      let inv := proj2_sig m' in
      let x := hpFree m a in
      (match x as y return (x = y -> _) with
       | None => fun H : x = None => None
       | Some m1 => fun H : x = Some m1 => Some(exist _ m1 (hpFree_invariant inv H))
       end) (eq_refl x). 

    Lemma  hpAlloc_charact': forall m' lbl sz r m1',
      hpAlloc' m' lbl sz = Some(r, m1') ->
      Permutation (r::AllocatedHp' m') (AllocatedHp' m1') /\
      AllocatedStk' m1' = AllocatedStk' m'. 
    Proof.
      unfold hpAlloc', AllocatedStk', AllocatedHp'.  
      intros.
      destruct m' as [m inv].
      destruct m1' as [m1 inv1].
      simpl in *. 
      monadInvDep H. 
      destruct a. inv H. 
      eapply hpAlloc_charact; eauto.
    Qed.

    Lemma hpAlloc_charact_size': forall m' m1'  lbl sz r,
      hpAlloc' m' lbl sz = Some(r, m1') -> 
      sz <= size_r r.
    Proof.
      unfold hpAlloc'. 
      intros.
      monadInvDep H. 
      destruct a.  inv H.
      eapply hpAlloc_charact_size; eauto.
    Qed.


   Lemma hpAlloc_stable_Allocated' : forall m' lbl m1' sz r,
      hpAlloc' m' lbl sz = Some(r, m1') -> 
      stable_Allocated' m' m1'.
   Proof.
     unfold stable_Allocated', hpAlloc'.
     intros.
     repeat rewrite equiv_naive_load'. unfold naive_load'.  
     destruct m' as [m inv].
     destruct m1' as [m1 inv1].
     simpl in *. 
     monadInvDep H.
     destruct a0.  inv H. 
     eapply hpAlloc_stable_Allocated; eauto.
    Qed.

   Lemma hpFree_charact_success': forall m' r,                       
     In r (AllocatedHp' m') -> 
     hpFree' m' (base r) <> None.
   Proof.
     unfold AllocatedStk', AllocatedHp', hpFree'. 
     intros.
     destruct m' as [m inv].
     simpl in *. 
     intro.
     monadInvDep H0. 
     eapply hpFree_charact_success; eauto.
   Qed.

   Lemma hpFree_charact': forall m' m1' a,                       
     hpFree' m' a = Some m1' -> 
     exists r, base r = a /\
     Permutation (r::AllocatedHp' m1') (AllocatedHp' m') /\
     AllocatedStk' m1' = AllocatedStk' m'.
   Proof.
     unfold AllocatedStk', AllocatedHp', hpFree'. 
     intros.
     destruct m' as [m inv].
     simpl in *. 
     monadInvDep H. inv H. 
     simpl. 
     apply hpFree_charact; auto.
   Qed.
     


   Lemma hpFree_stable_Allocated' : forall m' a m1',
      hpFree' m' a = Some m1' -> 
      stable_Allocated' m1' m'.
   Proof.
     unfold stable_Allocated', hpFree'. 
     intros.
     repeat rewrite equiv_naive_load'. unfold naive_load'.  
     destruct m' as [m inv].
     destruct m1' as [m1 inv1].
     simpl in *. 
     monadInvDep H.  inv H. 
     eapply hpFree_stable_Allocated; eauto.
   Qed.


    Lemma store_stable_status' : 
      forall m' m1' a v, 
      store' m' a v = Some m1' ->
      stable_status' m' m1'.
    Proof.
      unfold stable_status', stable_statusStk', stable_statusHp', AllocatedStk', store', accessible_dec'.
      intros.
      destruct m' as [m inv].
      destruct m1' as [m1 inv1].
      simpl in *. 
      destruct (accessible_dec (stk m) (hp m) a); inv H; auto.
    Qed. 

   Lemma store_can_write_Allocated' :
      forall m' a r v, 
      in_valid_region' m' r a -> 
      store' m' a v <> None.
    Proof.
      unfold in_valid_region', store', valid_regStk', AllocatedStk', accessible_dec'. 
      intros.
      destruct m' as [m inv].
      simpl in *. 
      intro.
      destruct (accessible_dec (stk m) (hp m) a); inv H0. 
      unfold accessible in n.  unfold allocated in n. 
      apply n. 
      left. 
      destruct r as [b sz].
      exists (b,sz). intuition.
    Qed.


    Lemma load_can_read_Allocated' :
      forall m' a r, 
      in_valid_region' m' r a -> 
      load' m' a <> None.
    Proof.
      unfold in_valid_region'.
      intros.
      rewrite equiv_naive_load'.
      unfold naive_load', valid_regStk', AllocatedStk'.
      destruct m' as [m inv]. 
      simpl in *. 
      eapply load_can_read_Allocated; eauto.
    Qed.



    Lemma store_stable_everywhere_else_value' :
      forall m m' a r v,
      store' m a v = Some m' ->
      in_valid_region' m r a -> 
      forall a', a' <> a -> load' m a' = load' m' a'.
    Proof.
      intros.
      repeat rewrite equiv_naive_load'. 
      rewrite equiv_naive_store' in H.
      unfold naive_store',naive_load' in *. 
      eapply store_stable_everywhere_else_value; eauto. 
      monadInvDep H. 
      inv H. 
      simpl. 
      eauto.
    Qed.

    Lemma store_charact_read_back' :
      forall m' m1' a v,
        store' m' a v = Some m1' ->
        load' m1' a   = Some v.
    Proof.
      intros.
      rewrite equiv_naive_store' in H.
      rewrite equiv_naive_load'.
      unfold naive_store' in H.
      unfold naive_load'. 
      destruct m' as [m inv].
      destruct m1' as [m1 inv1].
      simpl in *. 
      monadInvDep H.  inv H. 
      eapply store_charact_read_back; eauto.
    Qed.
    
    Lemma perturb_stable_status' :
      forall m' lbl m1', 
        perturb' m' lbl = Some m1' -> 
        stable_status' m' m1'.
    Proof.
      unfold perturb', stable_status', stable_statusStk', stable_statusHp', AllocatedStk'.
      intros.
      destruct m' as [m inv].
      destruct m1' as [m1 inv1].
      simpl in *. 
      inv H; auto. 
    Qed.

    Lemma perturb_stable_Allocated' :
      forall m' lbl m1', 
        perturb' m' lbl = Some m1' ->
        stable_Allocated' m' m1' /\
          stable_Allocated' m1' m'. 
    Proof.
      unfold perturb', stable_Allocated', in_valid_region', valid_regStk', AllocatedStk'.
      intros.
      repeat rewrite equiv_naive_load'.  unfold naive_load'.
      destruct m' as [m inv].
      destruct m1' as [m1 inv1].
      simpl in *. 
      inv H; auto. 
    Qed.
    

    Definition omem := mem'. 

    Definition oracle: Oracle olabel := 
      {|  Mem.mem := mem';
          Mem.initial_mem := initial_mem';
          Mem.AllocatedStk := AllocatedStk';
          Mem.AllocatedHp := AllocatedHp';
          Mem.stkAlloc := stkAlloc';
          Mem.stkFree := stkFree'; 
          Mem.hpAlloc := hpAlloc';
          Mem.hpFree := hpFree';
          Mem.load := load';
          Mem.store := store';
          Mem.perturb := perturb'; 
          Mem.initial_empty := initial_empty';
          Mem.Allocated_disjoint := Allocated_disjoint';
          Mem.Allocated_bounds := Allocated_bounds'; 
          Mem.AllocatedHp_distinct := AllocatedHp_distinct';           
          Mem.stkAlloc_charact := stkAlloc_charact';
          Mem.stkAlloc_charact_size := stkAlloc_charact_size';
          Mem.stkAlloc_stable_Allocated := stkAlloc_stable_Allocated';
          Mem.stkFree_charact_success := stkFree_charact_success';
          Mem.stkFree_charact := stkFree_charact';
          Mem.stkFree_stable_Allocated := stkFree_stable_Allocated';
          Mem.hpAlloc_charact := hpAlloc_charact';
          Mem.hpAlloc_charact_size := hpAlloc_charact_size';
          Mem.hpAlloc_stable_Allocated := hpAlloc_stable_Allocated';
          Mem.hpFree_charact_success := hpFree_charact_success';
          Mem.hpFree_charact := hpFree_charact';
          Mem.hpFree_stable_Allocated := hpFree_stable_Allocated';
          Mem.store_stable_status := store_stable_status';
          Mem.store_can_write_Allocated := store_can_write_Allocated';
          Mem.load_can_read_Allocated := load_can_read_Allocated';
          Mem.store_charact_read_back := store_charact_read_back';
          Mem.store_stable_everywhere_else_value := store_stable_everywhere_else_value';
          Mem.perturb_stable_status := perturb_stable_status';
          Mem.perturb_stable_Allocated := perturb_stable_Allocated';
      |}.
    


    (* Some useful lemmas on invariance of stack and heap structures under store. *)

    Lemma stack_store': forall m' a v m'',
        store' m' a v = Some m'' ->
        stk (proj1_sig m') = stk (proj1_sig m''). 
    Proof.
      intros.
      destruct m'. 
      destruct m''. 
      simpl. 
      unfold store', accessible_dec' in H. simpl in H. 
      destruct (accessible_dec (stk x) (hp x) a); inv H. 
      auto.
    Qed.
    
    Lemma heap_store' : forall m' a v m'',
        store' m' a v = Some m'' ->
        hp (proj1_sig m') = hp (proj1_sig m''). 
    Proof.
      intros.
      destruct m'. 
      destruct m''. 
      simpl. 
      unfold store', accessible_dec' in H. simpl in H. 
      destruct (accessible_dec (stk x) (hp x) a); inv H. 
      auto.
    Qed.

  End WithProgram.

End Functor.

