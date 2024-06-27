(* Concrete C
   Oracular Memory Model Specification
*)

Require Import List.
Import ListNotations.
Require Export Permutation.
Require Import Lia.
Require Import PeanoNat.
Require Import Relations.
Require Import RelationClasses.
Require Import Defns.

Local Open Scope Z_scope.
Declare Scope smem_scope.
Delimit Scope smem_scope with smem.
Local Open Scope smem_scope.

(** Regions **)

Definition region := (Z * nat)%type.
Notation "'base' r"     := (fst r)         (at level 1) : smem_scope.
Notation "'size_r' r"   := (snd r)         (at level 1) : smem_scope.
Notation "'bound' r"    := (fst r + snd r) (at level 1) : smem_scope.

Definition disjoint (r1 r2: region) : Prop :=
  bound r1 <= base r2 \/ bound r2 <= base r1 \/
  size_r r1 = O \/ size_r r2 = O.

Lemma disjoint_comm : forall r1 r2, disjoint r1 r2 <-> disjoint r2 r1. 
  unfold disjoint; intros.
  destruct r1 as [r1b r1s]; destruct r2 as [r2b r2s]; simpl; split; intro; lia.
Qed.

Definition disjoint_from (r: region) (rs:list region) : Prop :=
  Forall (disjoint r) rs. 

Lemma disjoint_from_cons: forall r r0 rs,
    disjoint_from r (r0::rs) <->
    disjoint r r0 /\ disjoint_from r rs. 
Proof.
  split.
  - unfold disjoint_from in *. 
    split.
    + eapply Forall_inv; eauto.
    + eapply Forall_inv_tail; eauto.
  - intros. unfold disjoint_from in *. 
    destruct H. 
    rewrite Forall_forall in *.  intros.
    destruct H1. 
    + subst. auto.
    + eapply H0; eauto.
Qed.

Lemma disjoint_from_app: forall rs1 r rs2,
    disjoint_from r rs1 ->
    disjoint_from r rs2 ->
    disjoint_from r (rs1 ++ rs2).
Proof.
  induction rs1; intros.
  - auto.
  - simpl. 
    unfold disjoint_from. rewrite Forall_forall; intros. simpl in H1. destruct H1.
    + subst. eapply disjoint_from_cons in H. intuition. 
    + assert (disjoint_from r rs1). 
      {  eapply disjoint_from_cons in H. intuition. } 
      pose proof (IHrs1 r rs2 H2 H0). 
      unfold disjoint_from in H3. 
      rewrite Forall_forall in H3.  eauto.
Qed.

Lemma disjoint_from_app_inv: forall rs1 r rs2,
    disjoint_from r (rs1 ++ rs2) -> 
    disjoint_from r rs1 /\
    disjoint_from r rs2. 
Proof.
  induction rs1; intros.
  - simpl in H. intuition. unfold disjoint_from. rewrite Forall_forall.
    intros. inv H0.
  - assert (disjoint_from r (rs1 ++ rs2)).
    { unfold disjoint_from in H|-*. rewrite Forall_forall in *. intros.
      eapply H. simpl.  right; auto. }
    destruct (IHrs1 _ _ H0). 
    unfold disjoint_from in H. rewrite Forall_forall in H. 
    split.
    + unfold disjoint_from in H1|-*.  rewrite Forall_forall in *. intros. 
      destruct H3. 
      * subst. eapply H. rewrite in_app. left.  left. auto.
      * eapply H1; auto.
    + auto. 
Qed.
      
Fixpoint mutually_disjoint (rs:list region) : Prop :=
  match rs with
    [] => True
  | r::rs => disjoint_from r rs /\ mutually_disjoint rs
  end.

Definition disjoint_lists (rs1 rs2: list region) : Prop :=
  forall r, In r rs1 -> disjoint_from r rs2. 

Lemma disjoint_lists_comm : forall rs1 rs2,
    disjoint_lists rs1 rs2 ->
    disjoint_lists rs2 rs1. 
Proof.
  induction rs1; intros.
  - unfold disjoint_lists. intros. unfold disjoint_from. apply Forall_nil. 
  - unfold disjoint_lists in *. intros.
    erewrite disjoint_from_cons. split. 
    + assert (disjoint_from a rs2).  { eapply H. left; auto.  }
      unfold disjoint_from in H1. 
      rewrite Forall_forall in H1.  
      apply disjoint_comm. eapply H1. auto.
    + eapply IHrs1; eauto. 
      intros.
      eapply H. right; auto.
Qed.

Lemma mutually_disjoint_app: forall rs1 rs2,
    mutually_disjoint rs1 ->
    mutually_disjoint rs2 ->
    disjoint_lists rs1 rs2 -> 
    mutually_disjoint (rs1 ++ rs2).              
Proof.
  induction rs1; intros. 
  - simpl. auto. 
  - simpl. split.
    + eapply disjoint_from_app.
      * unfold mutually_disjoint in H.  intuition.
      * unfold disjoint_lists in H1. eapply H1. left; auto.
    + eapply IHrs1; eauto. 
      * unfold mutually_disjoint in H. intuition. 
      * unfold disjoint_lists in H1 |-*. intros.
        eapply H1; intuition.
Qed.

Lemma mutually_disjoint_app_inv: forall rs1 rs2,
    mutually_disjoint (rs1 ++ rs2) ->               
    mutually_disjoint rs1 /\
    mutually_disjoint rs2 /\
    disjoint_lists rs1 rs2. 
Proof.
  induction rs1; intros.
  - simpl in *. intuition. unfold disjoint_lists. intros.  inv H0.
  - simpl. simpl in H.  destruct H as [P1 P2].
    destruct (IHrs1 _ P2) as [Q1 [Q2 Q3]].
    eapply disjoint_from_app_inv in P1. destruct P1 as [P11 P12].
    intuition.
    unfold disjoint_lists. intros.
    destruct H; subst; auto. 
Qed.

Lemma mutually_disjoint_perm : forall rs1 rs2,
    Permutation rs1 rs2 -> 
    mutually_disjoint rs1 ->
    mutually_disjoint rs2. 
Proof.
  induction 1; intros. 
  - auto.
  - simpl in *. intuition. 
    unfold disjoint_from in *; rewrite Forall_forall in *.  intros.
    eapply H1. apply Permutation_sym in H. eapply Permutation_in; eauto.
  - simpl in *. unfold disjoint_from in *; rewrite Forall_forall in *.
    intuition.
    + destruct H1. 
      * subst. apply disjoint_comm. eapply H0. left; auto.
      * rewrite Forall_forall in *. auto.
    + rewrite Forall_forall.  intros.
      eapply H0; right; auto.
  - eauto.
Qed.

Definition within (r:region) (a:Z) := base r <= a < bound r.

Theorem reg_eq_dec : forall (r1 r2: region),
  { r1 = r2 } + { r1 <> r2 }.
Proof with auto.
  decide equality.
  decide equality.
  apply Z.eq_dec. 
Qed.     

Lemma within_dec : forall r a,
  {within r a} + {~ within r a}.
Proof. unfold within.
  intros [b s] a; simpl.
  destruct (Z_le_dec b a)     as [X|X],
           (Z_lt_dec a (b+s)) as [Y|Y];
  try solve [right; intro; lia|auto].
Qed.


(** Definitions of properties. **)

Section WithOracleFunctions.

  Variable mem : Type.
  Variable AllocatedStk: mem -> list region.
  Variable AllocatedHp: mem -> list region.
  Variable load : mem -> Z  -> option val.

  Definition valid_regStk_ m r := In r (AllocatedStk m).
  Definition valid_regHp_ m r := In r (AllocatedHp m). 
  Definition valid_reg_ m r := valid_regStk_ m r \/ valid_regHp_ m r.
  Definition in_valid_region_ m r a := within r a /\ valid_reg_ m r.
  Definition stable_statusStk_ m m' := AllocatedStk m = AllocatedStk m'.
  Definition stable_statusHp_ m m' :=  Permutation (AllocatedHp m) (AllocatedHp m'). 
  Definition stable_status_ m m' :=  stable_statusStk_ m m' /\ stable_statusHp_ m m'.   (* paper: "equivalent allocations" *)
  Definition stable_Allocated_ m m' := forall a r,                                      (* paper: "m' is value-stable on m" *)
     in_valid_region_ m r a -> load m a = load m' a .
End WithOracleFunctions.

(** The type of oracular memories **)
Record Oracle (label: Type) :=
  { mem : Type
  ; initial_mem : mem

  (* operations *)
  ; stkAlloc : mem -> label -> nat -> (* alignment -> *) option (region * mem)
  ; stkFree  : mem -> option mem    

  ; hpAlloc  : mem -> label -> nat -> (* alignment -> *) option (region * mem)
  ; hpFree   : mem -> Z -> option mem 

  ; perturb  : mem ->  label -> option mem 

  ; load     : mem -> Z  -> option val  
  ; store    : mem -> Z -> val -> option mem 

  ; AllocatedStk : mem -> list region
  ; AllocatedHp : mem -> list region 

  (* auxiliary definitions *)
  ; valid_regStk := valid_regStk_ mem AllocatedStk
  ; valid_regHp := valid_regHp_ mem AllocatedHp
  ; valid_reg := valid_reg_ mem AllocatedStk AllocatedHp 
  ; in_valid_region := in_valid_region_ mem AllocatedStk AllocatedHp 
  ; stable_statusStk := stable_statusStk_ mem AllocatedStk
  ; stable_statusHp := stable_statusHp_ mem AllocatedHp
  ; stable_status := stable_status_ mem AllocatedStk AllocatedHp 
  ; stable_Allocated := stable_Allocated_ mem AllocatedStk AllocatedHp load
        
  (** Axiomatization *)

  (* initial memory *)
  ; initial_empty: AllocatedStk initial_mem = [] /\   (* paper: init *)
                 AllocatedHp initial_mem = []  

  (* properties of Allocated regions *)
  ; Allocated_disjoint: forall m,       (* paper: RDisj *)
      mutually_disjoint (AllocatedStk m ++ AllocatedHp m)
  ; Allocated_bounds: forall m r,       (* paper: RWF *)
      In r (AllocatedStk m ++ AllocatedHp m)  -> 
      0 < base r /\ bound r < Int64.max_unsigned  
  ; AllocatedHp_distinct: forall m,     (* paper: HpRDist *)
      NoDup (map (fun r => base r) (AllocatedHp m))

  (* properties of stkAlloc *)
  ; stkAlloc_charact: forall m m' lbl sz r, 
      stkAlloc m lbl sz (* a *) = Some (r, m') ->
      AllocatedStk m' = r::AllocatedStk m /\ AllocatedHp m' = AllocatedHp m  (* paper: StkA *)
  ; stkAlloc_charact_size : forall m m' lbl sz r,                            (* paper: StkAR *)
      stkAlloc m lbl sz (* a *) = Some (r, m') ->
      size_r r = sz  (* /\ base a % a = 0 *)
  ; stkAlloc_stable_Allocated : forall m m' lbl sz r,                        (* paper: StkAV *)
      stkAlloc m lbl sz (* a *) = Some (r, m') ->
      stable_Allocated m m'

  (* properties of stkFree *)
  ; stkFree_charact_success: forall m,                                       (* paper: StkFOK *)
      AllocatedStk m <> [] -> 
      stkFree m <> None
  ; stkFree_charact : forall m m',                                           (* paper: Stkf *)
      stkFree m = Some m' ->
      exists r, AllocatedStk m = r::AllocatedStk m' /\
      AllocatedHp m' = AllocatedHp m 
  ; stkFree_stable_Allocated : forall m m',                                  (* paper: StkFV *)
      stkFree m = Some m' -> 
      stable_Allocated m' m

  (* properties of hpAlloc *)
  ; hpAlloc_charact: forall m lbl sz r m',                                   (* paper: HpA *)
      hpAlloc m lbl sz (* a *) = Some(r, m') ->
      Permutation (r::AllocatedHp m) (AllocatedHp m') /\
      AllocatedStk m' = AllocatedStk m
  ; hpAlloc_charact_size: forall m m' lbl sz r,                              (* paper: HpAR *)
      hpAlloc m lbl sz (* a *) = Some(r, m') -> 
      sz <= size_r r (* /\ base r % a = 0 *)
  ; hpAlloc_stable_Allocated : forall m lbl m' sz r,                         (* paper: HpAV *)
      hpAlloc m lbl sz  (* a *) = Some(r, m') -> 
      stable_Allocated m m'
                      
  (* properties of hpFree *)
  ; hpFree_charact_success: forall m r,                                      (* paper: HpAFOK *)
     In r (AllocatedHp m) -> 
     hpFree m (base r) <> None 
  ; hpFree_charact: forall m m' a,                                           (* paper: HpF *)
      hpFree m a = Some m' ->
      exists r, base r = a /\
     Permutation (r::AllocatedHp m') (AllocatedHp m) /\
     AllocatedStk m' = AllocatedStk m
  ; hpFree_stable_Allocated : forall m a m',                                 (* paper: HpFV *)
      hpFree m a = Some m' -> 
      stable_Allocated m' m

  (* properties of compiler perturbations *)
  ; perturb_stable_status : forall m l m',                                   (* paper: Pert *)
        perturb m l = Some m' -> 
        stable_status m m'
  ; perturb_stable_Allocated: forall m l m',                                 (* paper: Per *)
        perturb m l = Some m' ->
        stable_Allocated m m' /\
        stable_Allocated m' m 

  (* properties of store *)
  ; store_stable_status : forall m m' a v,                                   (* paper: StR *)                       
      store m a v = Some m' ->
      stable_status m m'
  ; store_can_write_Allocated : forall m a r v,                              (* paper: StOK *)
      in_valid_region m r a -> 
      store m a v <> None

  (* properties of load *)
  ; load_can_read_Allocated : forall m a r,                                  (* paper: LdOK *)
      in_valid_region m r a -> 
      load m a <> None

  (* read after write properties *)
  ; store_charact_read_back : forall m m' a v,                               (* paper: LdStEq *)
      store m  a v = Some m' ->
      load  m' a   = Some v
  ; store_stable_everywhere_else_value : forall m m' a r v,                  (* paper: LdStNeq *)
      store m a v = Some m' ->
      in_valid_region m r a -> 
      forall a', a' <> a -> load m a' = load m' a'             
 }.


(* Facts that are admissible from oracle axioms. *)

Section MemFacts.
  Variable olabel: Type.
  Local Notation lab     := olabel.

  Variable oracle: Oracle lab.
  Local Notation mem          := oracle.(mem lab).
  Local Notation initial_mem  := oracle.(initial_mem lab).
  Local Notation stkAlloc     := oracle.(stkAlloc lab).
  Local Notation stkFree      := oracle.(stkFree lab).
  Local Notation hpAlloc      := oracle.(hpAlloc lab).
  Local Notation hpFree       := oracle.(hpFree lab).
  Local Notation load         := oracle.(load lab).
  Local Notation store        := oracle.(store lab).
  Local Notation perturb      := oracle.(perturb lab).
  Local Notation AllocatedStk := oracle.(AllocatedStk lab).
  Local Notation AllocatedHp  := oracle.(AllocatedHp lab).

  Local Notation valid_regStk := (valid_regStk_ mem AllocatedStk). 
  Local Notation valid_regHp :=  (valid_regHp_ mem AllocatedHp).
  Local Notation valid_reg :=  (valid_reg_ mem AllocatedStk AllocatedHp). 
  Local Notation in_valid_region := (in_valid_region_ mem AllocatedStk AllocatedHp). 
  Local Notation stable_statusStk := (stable_statusStk_ mem AllocatedStk). 
  Local Notation stable_statusHp :=  (stable_statusHp_ mem AllocatedHp).
  Local Notation stable_status := (stable_status_ mem AllocatedStk AllocatedHp). 
  Local Notation stable_Allocated := (stable_Allocated_ mem AllocatedStk AllocatedHp load).

  (* these are needed in contexts where arguments aren't fully inferred *)
  Local Notation Allocated_disjoint := (oracle.(Allocated_disjoint lab)).
  Local Notation Allocated_bounds := (oracle.(Allocated_bounds lab)). 
  Local Notation stkAlloc_charact := (oracle.(stkAlloc_charact lab)).  
  Local Notation stkFree_charact_success := (oracle.(stkFree_charact_success lab)).
  Local Notation stkFree_charact := (oracle.(stkFree_charact lab)). 
  Local Notation hpAlloc_charact := (oracle.(hpAlloc_charact lab)). 
  Local Notation hpFree_charact_success:=  (oracle.(hpFree_charact_success lab)). 
  Local Notation hpFree_charact :=  (oracle.(hpFree_charact lab)). 
  Local Notation store_stable_status := (oracle.(store_stable_status lab)). 
  Local Notation perturb_stable_status := (oracle.(perturb_stable_status lab)). 

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



  Corollary hpAlloc_validity: forall m lbl sz r0 m',
      hpAlloc m lbl sz = Some(r0,m') -> 
      forall r a,
        in_valid_region m r a -> 
        in_valid_region m' r a.
  Proof.
    intros.
    apply hpAlloc_charact in H. destruct H as [P1 P2]. 
    unfold in_valid_region, valid_reg, valid_regStk, valid_regHp in *.  intuition.
    - left.  rewrite P2.  auto. 
    - right. eapply Permutation_in in P1; eauto. right. auto.
  Qed.



  Corollary hpFree_validity: forall m a m', 
      hpFree m a = Some m' -> 
      forall r a,
        in_valid_region m' r a -> 
        in_valid_region m r a.
  Proof.
    intros.
    destruct (hpFree_charact _ _ _ H) as [r' [P1 [P2 P3]]].
    unfold in_valid_region, valid_reg, valid_regStk, valid_regHp in *.  intuition.
    - left.  rewrite <- P3. auto. 
    - right. eapply Permutation_in in P2; eauto. right. auto.
  Qed.
  

  Corollary store_validity: forall m a v m',
      store m a v = Some m' ->
      forall r a,
        in_valid_region m r a <-> 
          in_valid_region m' r a.
  Proof.
    intros.
    apply store_stable_status in H. unfold Mem.stable_status, Mem.stable_statusStk, Mem.stable_statusHp in H. 
    unfold in_valid_region, valid_reg, valid_regStk, valid_regHp in *.  destruct H.
    rewrite H.
    intuition.
    - right; unfold stable_statusHp in H0; eapply Permutation_in; eauto. 
    - right.  unfold stable_statusHp in H0. apply Permutation_sym in H0.  eapply Permutation_in; eauto. 
  Qed.


  Corollary perturb_validity: forall m m' l,
      perturb m l = Some m' ->
      forall r a,
        in_valid_region m r a <-> 
          in_valid_region m' r a.
  Proof.
    intros.
    apply perturb_stable_status in H. unfold Mem.stable_status, Mem.stable_statusStk, Mem.stable_statusHp in H. 
    unfold in_valid_region, valid_reg, valid_regStk, valid_regHp in *.  destruct H.
    rewrite H. intuition.  
    - right; unfold stable_statusHp in H0; eapply Permutation_in; eauto. 
    - right.  unfold stable_statusHp in H0. apply Permutation_sym in H0.  eapply Permutation_in; eauto. 
  Qed.



  Lemma stkFree_charact_failure:
    forall m,
      stkFree m = None <->
        AllocatedStk m = [].
  Proof.
    split; intros.
    - destruct (AllocatedStk m) eqn:?; auto. 
      exfalso.
      assert (AllocatedStk m <> []). 
      { intro. rewrite Heql in H0. inv H0. }
      apply stkFree_charact_success in H0. 
      rewrite H in H0. apply H0; auto. 
    - destruct (stkFree m) eqn:?; auto.
      exfalso.
      apply stkFree_charact in Heqo. destruct Heqo as [r [P1 P2]].
      rewrite H in P1.  inv P1. 
  Qed.


  Lemma hpFree_charact_failure:
    forall m a, 
      hpFree m a = None <->
        (forall r, In r (AllocatedHp m) -> base r <> a).
  Proof.
    split; intros.
    - destruct r as [a' s']. simpl. 
      destruct (Z.eq_dec a' a); auto. 
      subst. exfalso.
      apply hpFree_charact_success in H0.  simpl in H0. rewrite H in H0. apply H0; auto.
    - destruct (hpFree m a) eqn:?; auto. 
      exfalso.
      apply hpFree_charact in Heqo. 
      destruct Heqo as [r [P1 [P2 P3]]].
      eapply H; eauto. 
      eapply Permutation_in; eauto.  left; auto.
  Qed.


  (* Some trivial facts about new regions that follow from invariants on all regions. *)

  Lemma stkAlloc_disjoint: forall m m' lbl sz r,
      stkAlloc m lbl sz = Some (r, m') ->
      disjoint_from r (AllocatedStk m ++ AllocatedHp m).
  Proof.
    intros.
    destruct (stkAlloc_charact _ _ _ _ _ H). 
    pose proof (Allocated_disjoint m'). 
    rewrite H0  in H2. rewrite H1 in H2. simpl in H2.  intuition.
  Qed.

  Lemma stkAlloc_bounds: forall m m' lbl sz r,  
      stkAlloc m lbl sz = Some(r, m') ->
      0 < base r /\ bound r < Int64.max_unsigned.
  Proof.
    intros.
    destruct (stkAlloc_charact _ _ _ _ _ H). 
    eapply Allocated_bounds.
    erewrite H0. left. auto.
  Qed.

  Lemma hpAlloc_bounds: forall m lbl m' sz r,  
      hpAlloc m lbl sz = Some(r, m') ->
      0 < base r /\ bound r < Int64.max_unsigned.
  Proof.
    intros.
    destruct (hpAlloc_charact _ _ _ _ _ H) as [P1 P2]. 
    eapply Allocated_bounds.
    rewrite in_app. right.
    eapply Permutation_in in P1; eauto.  left. auto.
  Qed.

  Lemma hpAlloc_disjoint:  forall m lbl m' sz r,
      hpAlloc m lbl sz = Some(r, m') ->
      disjoint_from r (AllocatedHp m). 
  Proof.
    intros.
    destruct (hpAlloc_charact _ _ _ _ _ H) as [P _]. 
    pose proof (Allocated_disjoint m'). 
    destruct (mutually_disjoint_app_inv _ _ H0) as [_ [Q _]]. 
    eapply Permutation_sym in P. 
    eapply mutually_disjoint_perm in Q; eauto. simpl in Q. intuition.
  Qed.

  Lemma hpAlloc_distinct: forall m lbl m' sz r,
      hpAlloc m lbl sz = Some(r, m') ->
      ~ In (base r) (map (fun r => base r) (AllocatedHp m)). 
  Proof.
    intros.
    destruct (hpAlloc_charact _ _ _ _ _ H) as [P _].
    pose proof (AllocatedHp_distinct _ _ m'). 
    intro.
    eapply Permutation_sym in P. 
    eapply Permutation_map with (f:= fun r => base r) in P.
    eapply Permutation_NoDup in P; auto. 
    clear H0. 
    inv P. apply H3; auto.
  Qed.
  
End MemFacts. 


