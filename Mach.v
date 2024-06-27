(* Concrete C *)

(* Target Machine definition *)

Require Import Program String.
Require Import List.
Import ListNotations.
Require Import Maps.
Require Import Defns Smallstep.
Import Int64.

(* EQUATIONS *)

From Equations Require Import Equations. 

(* This is altered by Equations; try just resetting it. *)
Arguments eq_refl {A}%type_scope {x}, [_] _.  

(* Equations also seems to mess with inversion in some corner cases. *)
Set Keep Proof Equalities. 

Local Open Scope Z.

Section Language.

  Definition Tag := bool.
  Definition t_pro : Tag :=  true.  (* "protected"  , equivalently "privileged"/"hi" *)
  Definition t_unp : Tag := false.  (* "unprotected", equivalently "unprivileged"/"lo" *)
  Definition Priv := bool. 
  Definition hi : Priv := true. 
  Definition lo : Priv := false.

  Definition mreg := positive.
  Local Open Scope positive_scope.
  Definition SP  : mreg := 1.
  Definition RV  : mreg := 2.
  Definition RA  : mreg := 3.
  Definition GP1 : mreg := 4.
  Definition GP2 : mreg := 5.
  Definition GP3 : mreg := 6.
  Local Close Scope positive_scope.

  Definition reladdr := (reg * val)%type.

  Inductive builtin :=
  | Bmalloc 
  | Bfree.

  (* Note: destination last *)
  Inductive instr : Type :=
    | Mmov   : mreg -> mreg -> instr
    | Mmovi  : val -> mreg -> instr
    | Mop    : operation -> mreg -> mreg -> mreg -> instr
    | Mload  : forall (privilege: Priv),
                  reladdr -> mreg -> instr
    | Mstore : forall (privilege: Priv) (destination_tag: Tag),
                  mreg -> reladdr -> instr
    | Mjal  : ident -> instr   (* jumps to top of a function *)
    | Mbuiltin : builtin -> instr                         
    .

  Definition code: Type := list instr.

  Record function : Type := mkfunction {
    f_id : ident                                
  ; body: code
  }.

  Definition program : Type := list function. 

  Fixpoint lookup_function (i: ident) (fs: program) : option function := 
    match fs with
    | [] => None
    | f::fs' => if Pos.eqb i (f_id f) then Some f else lookup_function i fs'
    end.

  Lemma lookup_function_spec: forall i p f,
      lookup_function i p = Some f -> f_id f = i. 
  Proof.
    induction p; intros. 
    -  inv H. 
    - inv H. destruct (Pos.eqb_spec i (f_id a)). 
      + subst. inv H1. auto.
      + eapply IHp; eauto. 
  Qed.

  (* Identifiers for (temporarily) built-in functions. *)

  Definition Bmalloc_id := 1%positive.
  Definition Bfree_id := 2%positive.

End     Language.

Declare Scope mach_scope.
Delimit Scope mach_scope with mach.

Class SPPlus A : Type := { SPplus : A -> reladdr }.
(* Some ad-hoc polymorphism for easier writing and reading... *)
Global Notation "'SP+' n" := (SPplus n) (at level 1) : mach_scope.

Definition SPplus_val (x: val) : reladdr := (SP,      x).
Definition SPplus_nat (x: nat) : reladdr := (SP, repr x).
Definition SPplus_Z   (x: Z  ) : reladdr := (SP, repr x).
#[export] Instance SPP_val : SPPlus val := {SPplus := SPplus_val}.
#[export] Instance SPP_nat : SPPlus nat := {SPplus := SPplus_nat}.
#[export] Instance SPP_Z   : SPPlus Z   := {SPplus := SPplus_Z  }.

Module Type MachParameters.

  Parameter init_mmem_values: Z -> val. 

  (* Stack grows down *)

  (* Max accessible stack address + 1. *)
  Parameter StkBase:  Z.

  (* Min accessible stack address. *)
  Parameter StkLimit : Z.

  (* Heap grows up *)

  (* Min acessible heap address. *)
  Parameter HpBase: Z.

  (* Max accessible heap address + 1. *)
  Parameter HpLimit: Z. 

  Axiom StkBase_WF: StkBase < Int64.max_unsigned.
  Axiom StkLimit_WF: 0 < StkLimit.
  Axiom StkBaseLimit_WF : StkLimit <= StkBase.

  Axiom HpBase_WF: 0 < HpBase.

  Axiom HpBaseLimit_WF: 0 < HpLimit - HpBase <= max_signed.  (* our heap bookkeeping scheme requires at least one word,
                                                          and also that any block size fits in a signed word *)

  Axiom StkHp_disjoint: StkLimit >= HpLimit.   (* A stronger separation is actually needed for our compilation scheme; see comment at top of Compiler.v *)

  Lemma HpLimit_WF: HpLimit < Int64.max_unsigned.
  Proof.
    pose proof StkBase_WF. pose proof StkBaseLimit_WF. pose proof StkHp_disjoint. lia'. 
  Qed.

End MachParameters.

Module Semantics (Export mparams : MachParameters).

  (* NB: we seem to need at least two constructors to avoid bizarre problems with inversion on outcomes later. *)
  Inductive failure :=
  | BadMemAccess         (* machine-level failures *)
  | BadHeapOperation.    (* alloc/free failures *)

  (* Custom error monad for these semantics. *)
  Inductive outcome (A:Type): Type :=
  | Normal : A -> outcome A
  | Stuck : string -> outcome A  (* these might eventually go away *)
  | Failure : failure -> outcome A
  .

  Arguments Normal [A].
  Arguments Stuck [A]. 
  Arguments Failure [A].

  Declare Scope outcome_monad_scope.

  Definition bind {A B: Type} (f: outcome A) (g: A ->  outcome B) : outcome B :=
    match f with
    | Normal x => g x
    | Stuck s => Stuck s
    | Failure c => Failure c
    end.

  Definition bind2 {A B C: Type} (f: outcome (A * B)) (g: A -> B -> outcome C) : outcome C :=
    match f with
    | Normal (x,y) => g x y
    | Stuck s => Stuck s
    | Failure c => Failure c
    end.


  Definition bind3 {A B C D: Type} (f: outcome (A * B * C)) (g: A -> B -> C -> outcome D) : outcome D :=
    match f with
    | Normal (x,y,z) => g x y z
    | Stuck s => Stuck s
    | Failure c => Failure c
    end.

  Remark bind_inversion:
    forall (A B: Type) (f: outcome A) (g: A -> outcome B) (y: B),
      bind f g = Normal y ->
      exists x, f = Normal x /\ g x = Normal y.
  Proof.
    intros until y. destruct f; simpl; intros.
    exists a; auto.
    discriminate.
    discriminate.
  Qed.

  Remark bind2_inversion:
    forall (A B C: Type) (f: outcome (A*B)) (g: A -> B -> outcome C) (z: C),
      bind2 f g = Normal z ->
      exists x, exists y, f = Normal (x, y) /\ g x y = Normal z.
  Proof.
    intros until z. destruct f; simpl.
    destruct p; simpl; intros. exists a; exists b; auto.
    intros; discriminate.
    intros; discriminate.
  Qed.

  Notation "'do' X <- A ; B" := (bind A (fun X => B))
   (at level 200, X name, A at level 100, B at level 200)
   : outcome_monad_scope.

  Notation "'do' ( X , Y ) <- A ; B" := (bind2 A (fun X Y => B))
   (at level 200, X name, Y name, A at level 100, B at level 200)
   : outcome_monad_scope.

  Notation "'do' ( X , Y , Z ) <- A ; B" := (bind3 A (fun X Y Z => B))
   (at level 200, X name, Y name, Z name, A at level 100, B at level 200)
   : outcome_monad_scope.

  Ltac machMonadInv1 H :=
  match type of H with
  | (Normal _ = Normal _) =>
      inv H (* inversion H; clear H; try subst *)
  | (bind ?F ?G = Normal ?X) =>
      let x := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind_inversion F G H) as [x [EQ1 EQ2]];
      clear H;
      try (machMonadInv1 EQ2))))
  | (bind2 ?F ?G = Normal ?X) =>
      let x1 := fresh "x" in (
      let x2 := fresh "x" in (
      let EQ1 := fresh "EQ" in (
      let EQ2 := fresh "EQ" in (
      destruct (bind2_inversion F G H) as [x1 [x2 [EQ1 EQ2]]];
      clear H;
      try (machMonadInv1 EQ2)))))
  | (match ?X with Normal _ => _ | _ => _ end = Normal _) =>
      destruct X eqn:?; try (machMonadInv1 H) 
  | (match ?X with Some _ => _ | _ => _ end = Normal _) =>
      destruct X eqn:?; try (machMonadInv1 H) 
  | ((if ?E then _ else _) = Normal _) =>
      destruct E eqn:?; try (machMonadInv1 H)
  | (_ = _) =>
      try discriminate
  end.

  Ltac machMonadInv H :=
  machMonadInv1 H ||
  match type of H with
  | (?F _ _ _ _ _ _ _ _ = Normal _) =>
      ((progress simpl in H) || unfold F in H); machMonadInv1 H
  | (?F _ _ _ _ _ _ _ = Normal _) =>
      ((progress simpl in H) || unfold F in H); machMonadInv1 H
  | (?F _ _ _ _ _ _ = Normal _) =>
      ((progress simpl in H) || unfold F in H); machMonadInv1 H
  | (?F _ _ _ _ _ = Normal _) =>
      ((progress simpl in H) || unfold F in H); machMonadInv1 H
  | (?F _ _ _ _ = Normal _) =>
      ((progress simpl in H) || unfold F in H); machMonadInv1 H
  | (?F _ _ _ = Normal _) =>
      ((progress simpl in H) || unfold F in H); machMonadInv1 H
  | (?F _ _ = Normal _) =>
      ((progress simpl in H) || unfold F in H); machMonadInv1 H
  | (?F _ = Normal _) =>
      ((progress simpl in H) || unfold F in H); machMonadInv1 H
  end.

  Open Scope outcome_monad_scope.

  Section MachineMem.
    
    Inductive mval :Type :=
    | Vint : val -> mval
    | VCP  : code -> mval.
    Global Coercion Vint : val >-> mval.

    Definition mregbank : Type := Regmap.t mval.
    Definition mmem     : Type := Z -> (mval * Tag).

    Definition updm dst_t M a mv : mmem :=
      fun a' => if a =? a' then (mv,dst_t)  else M a'.


    Definition access_in_bounds (a : Z) : bool :=
      (StkLimit <=? a) && (a <? StkBase)
    || (HpBase <=? a) && (a <? HpLimit). 

    (* access is allowed if security is low (false) or
       privilege is high (true) i.e.
       ~ sec \/ priv *)
    Definition access_allowed (privilege:Priv) (security : Tag) := implb security privilege.

    Definition in_bounds (a:Z) : Prop :=
      (StkLimit <= a) /\ (a < StkBase)
      \/ (HpBase <= a) /\ (a < HpLimit).

    Lemma in_bounds_access: forall a,
        in_bounds a <-> access_in_bounds a = true.
    Proof.
      unfold in_bounds, access_in_bounds.
      split; intros.
      - destruct H. 
        + apply orb_true_intro. left.  apply andb_true_intro. split.
          * apply Zle_imp_le_bool. lia. 
          * apply Zlt_is_lt_bool. lia.
        + apply orb_true_intro. right. apply andb_true_intro. split. 
          * apply Zle_imp_le_bool. lia.
          * apply Zlt_is_lt_bool. lia.
      - apply orb_true_elim  in H. destruct H.
        + apply andb_prop in e. destruct e. 
          left.  apply Zle_bool_imp_le in H. apply Z.ltb_lt in H0. lia.
        + apply andb_prop in e.  destruct e. 
          right. apply Zle_bool_imp_le in H. apply Z.ltb_lt in H0. lia.
    Qed.

    Inductive allowed : Priv -> Tag -> Prop :=
    | allowed_true : forall t, allowed hi t
    | allowed_false : allowed lo t_unp
    .                             

    Lemma allowed_access: forall p t,
        allowed p t <-> access_allowed p t = true .
    Proof.
      unfold access_allowed.
      intros; split; intros.
      - inv H; auto. destruct t; auto.
      - destruct p.
        + constructor.
        + destruct t; inv H; constructor. 
    Qed.

    Lemma in_bounds_WF: forall a,
        in_bounds a -> 0 <= a <= Int64.max_unsigned.  
    Proof.
      pose proof StkLimit_WF. 
      pose proof StkBase_WF.
      pose proof HpBase_WF.
      pose proof HpLimit_WF.
      unfold in_bounds. 
      lia.
    Qed.


    Definition lookup priv M a : outcome mval :=
      match M a with
      | (mv,sec) => if access_in_bounds a && access_allowed priv sec
                    then Normal mv
                    else Failure BadMemAccess
      end.
    Definition writedown priv dst_t M a mv : outcome mmem :=
      match M a with
      |  (_,sec) => if access_in_bounds a && access_allowed priv sec
                    then Normal (updm dst_t M a mv)
                    else Failure BadMemAccess
      end.
    Definition initm : mmem := fun a =>
      if a =? HpBase then
        (Vint (val_of_Z (HpBase - HpLimit)), t_pro)  (* the initial heap free region *)
     else
        (Vint (init_mmem_values a),t_unp).

  End  MachineMem.

  Create HintDb machdb.

    Set Printing Coercions.

    Remark aa_hi : forall x,
      access_allowed hi x = true.
    Proof.
      unfold access_allowed, hi, implb.
      intros []; auto.
    Qed. #[export] Hint Rewrite aa_hi: machdb.

    Remark lookup_hi_OK : forall M a,
      access_in_bounds a = true -> 
      lookup hi M a = Normal (fst (M a)).
    Proof.
      unfold lookup. intros. destruct (M a).
      rewrite aa_hi. rewrite H. simpl; auto.
    Qed.


    (* Properties of machine memory *)

    Remark writedown_hi_OK : forall t M a mv,
      access_in_bounds a = true -> 
      writedown hi t M a mv = Normal (updm t M a mv).
    Proof.
      intros. unfold writedown. destruct (M a).
      rewrite aa_hi. rewrite H. auto.
    Qed.

    Lemma mupdate_gss : forall dst_t M a mv,
        (updm dst_t M a mv) a = (mv,dst_t).
    Proof.
      intros. unfold updm.
      destruct (Z.eqb_spec a a); try lia; auto.  
    Qed.

    Corollary update_gss : forall dst_t M a mv t,
      access_in_bounds a = true -> 
      access_allowed t dst_t = true -> 
      lookup t (updm dst_t M a mv) a = Normal mv.
    Proof.
      intros. unfold lookup. rewrite mupdate_gss. 
      rewrite H0, H. auto. 
    Qed. #[export] Hint Rewrite update_gss: machdb.

    Lemma mupdate_gso: forall dst_t M a a' mv,
        a <> a' -> 
        (updm dst_t M a mv) a' = M a'. 
    Proof.
      intros. unfold updm. 
      destruct (Z.eqb_spec a a'); try lia; auto. 
    Qed.

    Corollary update_gso : forall dst_t M a a' mv t,
        a <> a' ->
        lookup t (updm dst_t M a mv) a' = lookup t M a'.
    Proof.
      intros. unfold lookup.  
      rewrite mupdate_gso; auto. 
    Qed. #[export] Hint Rewrite update_gso: machdb.

    
    Corollary mupdate_commute: forall t t' M a a' mv mv',
        a <> a' ->
        updm t' (updm t M a mv) a' mv' = updm t (updm t' M a' mv') a mv. 
    Proof.
      intros.
      apply functional_extensionality.
      intros.
      destruct (Z.eq_dec a' x). 
      - subst.
        rewrite mupdate_gss.
        rewrite mupdate_gso; try lia.
        rewrite mupdate_gss; auto.
      - rewrite mupdate_gso; try lia'. 
        destruct (Z.eq_dec a x). 
        + subst.
          rewrite mupdate_gss. 
          rewrite mupdate_gss.
          auto.
        + rewrite mupdate_gso; try lia'. 
          rewrite mupdate_gso; try lia'. 
          rewrite mupdate_gso; try lia'. 
          auto.
    Qed.

    
  (* Machine Definition *)

  Inductive state : Type :=
    | State : code -> mregbank -> mmem -> state
    | Failstop : failure -> state.

  Inductive initial_state (p: program) : state -> Prop :=
    | initial_state_intro : forall  main,
        List.hd_error p = Some main -> 
        let B0 : mregbank :=
                  (Regmap.init (Vint zero))
                   # RA <- (Vint zero)  (* (VCP [])*)
                   # SP <- (Vint (val_of_Z StkBase)) in 
        initial_state p (State main.(body) B0 initm).

  Inductive final_state : state -> mval -> Prop :=
    | final_state_intro : forall B xx,
        B#RA = Vint zero -> 
        B#SP = Vint (val_of_Z StkBase) ->
        final_state (State [] B xx) (B # RV).

  Inductive failstop_state : state -> failure -> Prop :=
    | failstop_state_intro: forall failure,
        failstop_state (Failstop failure) failure.

  Definition check_val (mv : mval) : outcome val :=
    match mv with
    | Vint v => Normal v
    | VCP _ => Stuck "Unexpected code pointer in builtin argument"
    end.

  Definition eval_op' op B (r1 r2 : mreg) : outcome val :=
    match B#r1, B#r2 with
    | Vint v1, Vint v2 => Normal (eval_op op v1 v2)
    | _ , _ => Stuck "Unexpected code pointer in an operation."
    end.

  Definition lea B (rofs: reladdr) : outcome val :=
    match B#(fst rofs) with
    | Vint v => Normal (add (snd rofs) v)
    | _ => Stuck "Unexpected code pointer in address calculation "
    end.


  (** Malloc/free builtins.
      Short-term hackery.
      Ultimately, these should be ordinary code, but for now we just
      give Gallina specifications. *)

  Definition decp (p:Z) := Z.to_nat (HpLimit - p). 

  Equations hpAlloc_loop (M : mmem) (sz: nat) (p: Z)  : outcome (val * mmem) by wf (decp p) :=
    hpAlloc_loop M sz p :=  
      if Z_lt_ge_dec p  HpLimit then 
        do mpmv <- lookup hi M p;
        do mp <- check_val mpmv; 
        if Z.eq_dec (signed mp) 0 then
          Failure BadHeapOperation (* just for termination; can't happen in well-formed heap *)
        else if Z_lt_ge_dec (signed mp) 0 then 
          let n := - (signed mp) in
          if n >=? sz + 1 then 
            do M' <- writedown hi t_pro M p (val_of_Z (sz + 1));
            do M'' <- if n >? sz + 1 then
                        writedown hi t_pro M' (p + sz + 1) (val_of_Z (sz + 1 - n))
                     else Normal M';
            Normal(val_of_Z(p+1),M'')
          else hpAlloc_loop M sz (p + n)
        else hpAlloc_loop M sz (p + (signed mp))                               
      else Failure BadHeapOperation.
  Next Obligation.
    unfold decp; lia'.  Defined.
  Next Obligation.
    unfold decp; lia'. Defined.


  Definition hpAlloc_impl (M : mmem) (sz: nat) : outcome (val * mmem) :=
    hpAlloc_loop M sz HpBase. 


  Definition Bmalloc_impl (B: mregbank) (M: mmem) : outcome (mregbank * mmem) :=
    let spmv := B # SP in
    do sp <- check_val spmv; 
    do arg <- lookup hi M (unsigned sp);
    do sz <- check_val arg;
    do (rv,M') <- hpAlloc_impl M (Z.to_nat (unsigned sz));
    Normal(B # RV <- (Vint rv), M').
    


  (* try to find block with address a, starting from p, with previous block b;
     returning previous block, size, and next block *)
  Equations hpFree_loop (M : mmem) (a: Z) (p: Z) (b: Z) : outcome (Z*Z*Z) by wf (decp p) :=
  hpFree_loop M a p b := 
    if Z_lt_ge_dec p HpLimit then
      (* block exists; get the header *)
      do mp <- lookup hi M p;
      do n <- check_val mp;                          
      if Z.eq_dec a (p+1) then
        (* found the target block *)
        if Z_gt_le_dec (signed n) 0 then
          (* target block is allocated; we're done *)
          Normal(b,signed n,p + signed n)
        else
          (* target block is already free *)
          Failure BadHeapOperation
      else   
        (* this is not the block we want to free; advance to next header *)
        if Z.eq_dec (signed n) 0 then
          (* impossible for WF heap; just here to keep termination checker happy *)
          Failure BadHeapOperation
        else if Z_gt_le_dec (signed n) 0 then
            hpFree_loop M a (p + signed n) p
        else 
            hpFree_loop M a (p - signed n) p
    else                  
      (* target block does not exist *)
      Failure BadHeapOperation.
  Next Obligation.
  unfold decp; lia'.  Defined.
  Next Obligation.
  unfold decp; lia'.  Defined.

  Remark hpFree_loop_charact : forall M a p b l sz r,
    b < p -> 
    hpFree_loop M a p b = Normal(l,sz,r) ->
    sz > 0 /\ l < a - 1 /\ a - 1 + sz = r. 
  Proof.
    intros.
    funelim (hpFree_loop M a p b). 
    rewrite <- Heqcall  in H2. 
    repeat machMonadInv H2. 
    - lia'.
    -  simpl in Heqcall. rewrite Heqo0 in Heqcall; simpl in Heqcall.
       rewrite Heqs2 in Heqcall; simpl in Heqcall.
       rewrite Heqs1 in Heqcall; simpl in Heqcall.
       eapply H with (p := (p + signed v)); eauto; try lia.
    - simpl in Heqcall. rewrite Heqo0 in Heqcall; simpl in Heqcall.
      rewrite Heqs1 in Heqcall. rewrite Heqs2 in Heqcall.
      eapply H0 with (p := (p - signed v)); eauto; try lia.
  Qed.



  Definition hpFree_impl (M : mmem) (a: Z) : outcome mmem := 
    do (l,sz,r) <- hpFree_loop (M :mmem) (a:Z) HpBase (HpBase-1)%Z;
    let p := a - 1 in  
    if Z_lt_ge_dec l HpBase then
      (* no left neighbor *)
      if Z_ge_lt_dec r HpLimit then
        (* no right neighbor *)
        (* no merge *)
        writedown hi t_pro M p (val_of_Z (- sz))
      else
        (* right neighbor exists *)
        do mr <- lookup hi M r;
        do nr <- check_val mr;                          
        if Z_ge_lt_dec (signed nr) 0 then
          (* right neighbor allocated *)
          (* no merge *)
          writedown hi t_pro M p (val_of_Z (- sz))
        else
          (* right neighbor free *)
          (* merge right *)
          do M' <- writedown hi t_pro M p (val_of_Z (- sz + (signed nr)));
          writedown hi t_unp M' r (Vint zero)
    else
      (* left neighbor exists *)
      do ml <- lookup hi M l;
      do nl <- check_val ml;
      if Z_ge_lt_dec (signed nl) 0 then
        (* left neighbor allocated *)
        if Z_ge_lt_dec r HpLimit then
          (* no right neighbor *)
          (* no merge*)
          writedown hi t_pro M p (val_of_Z (- sz))
        else
          (* right neighbor exists *)
          do mr <- lookup hi M r;
          do nr <- check_val mr;                          
          if Z_ge_lt_dec (signed nr) 0 then
            (* right neighbor allocated *)
            (* no merge *)
            writedown hi t_pro M p (val_of_Z (- sz))
          else
            (* right neighbor free *)
            (* merge right *)
            do M' <- writedown hi t_pro M p (val_of_Z (- sz + (signed nr)));
            writedown hi t_unp M' r (Vint zero)
      else
        (* left neighbor free *)
        if Z_ge_lt_dec r HpLimit then
          (* no right neighbor *)
          (* merge left *)
          do M' <- writedown hi t_pro M l (val_of_Z (- sz + (signed nl)));
          writedown hi t_unp M' p (Vint zero)                             
        else
          (* right neighbor exists *)
          do mr <- lookup hi M r;
          do nr <- check_val mr;                          
          if Z_ge_lt_dec (signed nr) 0 then
            (* right neighbor allocated *)
            (* merge left *)
            do M' <- writedown hi t_pro M l (val_of_Z (- sz + (signed nl)));
            writedown hi t_unp M' p (Vint zero)
          else
            (* right neighbor free *)
            (* merge left and right *)
            do M' <- writedown hi t_pro M l (val_of_Z (- sz + (signed nl) + (signed nr)));
            do M'' <- writedown hi t_unp M' p (Vint zero);
            writedown hi t_unp M'' r (Vint zero).                               


  Definition Bfree_impl (B : mregbank) (M: mmem) : outcome(mregbank * mmem) :=
    let spmv := B # SP in
    do sp <- check_val spmv; 
    do arg <- lookup hi M (unsigned sp);
    do a <- check_val arg;
    do (rv,M') <- 
      if (unsigned a =? 0)%Z  then
        Normal (NULL,M)            
      else
        do M' <- hpFree_impl M (unsigned a);
        Normal (NULL,M');
   Normal (B # RV <- (Vint rv), M').


  Definition perform_builtin (b: builtin) (B: mregbank) (M: mmem) : outcome(mregbank * mmem) :=
        (* these each take one integer argument from the usual stack location *)
    match b with
    | Bmalloc => Bmalloc_impl B M
    | Bfree => Bfree_impl B M
    end. 


  Section Transitions.
    Variable p: program.

    (* Executable semantics/transitions *)
  Definition next_state pc B M : outcome state :=
    let GS  a b c  := Normal (State a b c) in
    match pc with
    | Mmov  s d      :: pc' => GS pc' (B # d <- (B#s)   ) M
    | Mmovi v d      :: pc' => GS pc' (B # d <- (Vint v)) M
    | Mop op r1 r2 d :: pc' => do v <- eval_op' op B r1 r2;
                               GS pc' (B # d <- (Vint v)) M
    | Mjal fid       :: pc' => match lookup_function fid p with 
                               | Some f => GS f.(body) (B#RA <- (VCP pc')) M
                               | _ => Stuck "no such function"
                               end
    | Mload priv s d :: pc' => do a <- lea B s;
                               do mv <- lookup priv M (unsigned a);
                               GS pc' (B # d <- mv) M
    | Mstore priv dst_t s d :: pc' => do a <- lea B d; 
                                      do M' <- writedown priv dst_t M (unsigned a) (B#s);
                                      GS pc' B M'
    | Mbuiltin b    :: pc' => do (B',M') <- perform_builtin b B M;
                              GS pc' B' M'                                                        
    | [] (* return *) =>  match B#RA with
                          | VCP pc => GS pc B M
                          | _ => Stuck "non code pointer found in RA at function exit"
                          end
    end.

  Local Close Scope outcome_monad_scope.

  (* the executable semantics ([next_state]) cast into a relation *)
  Inductive step : state -> state -> Prop :=
  | step_Mmov : forall s d pc B M B',
      (B # d <- (B#s)) = B' ->
      step (State (Mmov s d :: pc) B  M)
           (State              pc  B' M)
  | step_Mmovi : forall v d pc B M B',
      (B # d <- (Vint v)) = B' ->
      step (State (Mmovi v d :: pc) B  M)
        (State               pc  B' M)
  | step_Mop : forall v d pc B M B' op r1 r2,
      eval_op' op B r1 r2 =  Normal v ->
      (B # d <- (Vint v)) = B' ->
      step (State (Mop op r1 r2 d :: pc) B  M)
        (State                    pc  B' M)
  | step_Mload : forall priv s d pc B M B' a mv,
      lea B s = Normal a ->
      lookup priv M (unsigned a) = Normal mv ->
      B # d <- mv = B' ->
      step (State (Mload priv s d :: pc) B  M)
        (State                    pc  B' M)
  | step_Mload_FS_lkup : forall priv s d pc B M c a,
      lea B s = Normal a ->
      lookup priv M (unsigned a) = Failure c ->
      step (State (Mload priv s d :: pc) B  M)
        (Failstop c)
  | step_Mstore : forall priv dst_t s d pc B M M' a,
      lea B d = Normal a ->
      writedown priv dst_t M (unsigned a) (B#s) = Normal M' ->
      step (State (Mstore priv dst_t s d :: pc) B M )
        (State                           pc  B M')
  | step_Mstore_FS : forall priv dst_t s d pc B M c a,
      lea B d = Normal a ->
      writedown priv dst_t M (unsigned a) (B#s) = Failure c ->
      step (State (Mstore priv dst_t s d :: pc) B M )
        (Failstop c)
  | step_Mjal : forall fid pc B M f,
      lookup_function fid p = Some f ->
      step (State (Mjal fid :: pc)  B                  M)
        (State f.(body)          (B#RA <- (VCP pc)) M)
  | step_Mbuiltin : forall b pc B M B' M',
      perform_builtin b B M = Normal(B',M') -> 
      step (State (Mbuiltin b :: pc) B M)
           (State pc B' M')
  | step_Mbuiltin_FS : forall b pc B M c,
      perform_builtin b B M = Failure c ->
      step (State (Mbuiltin b :: pc) B M)
           (Failstop c) 
  | step_return : forall B M pc,
      B#RA = (VCP pc) ->
      step (State [] B M)
        (State pc B M).

  
  Inductive step_ex : state -> state -> Prop :=
  | step_normal : forall pc B M n_state,
      next_state pc B M = Normal n_state ->
      step_ex (State pc B M) n_state
  | step_fs: forall pc B M c,
      next_state pc B M = Failure c ->
      step_ex (State pc B M) (Failstop c).
  

    Remark step__ex : forall s1 s2,
      step s1 s2 <-> step_ex s1 s2.
    Proof with eauto.
      split.
      - induction 1;
        try solve [
          econstructor;             
          unfold next_state;
          repeat (match goal with
          | H : ?a = ?b
            |- _ => progress (rewrite H)
          end; try unfold bind); auto].
      - revert s2.
        destruct s1 as [pc B M|];[|inversion 1].
        destruct pc as [|i pc]; intros * A; inv A.
        + simpl in H3.
          destruct (B # RA) as [v|pc] eqn:A.
          * inv H3. 
          * inv H3; econstructor...
        + simpl in H3.
          destruct (B # RA) as [v|pc] eqn:A.
          * inv H3. 
          * inv H3; econstructor...
        + destruct i; simpl in *.
          * rename m into s, m0 into d.
            destruct (B # d <- (B !! s))
              eqn:A; inv H3;
              try econstructor...
          *  rename m into d.
             inv H3. 
             econstructor...
          *  rename m  into r1,
                 m0 into r2, 
                 m1 into d.
             destruct (eval_op' o B r1 r2) eqn:X;
               simpl in *; inv H3; econstructor...
          * unfold lea in *. destruct r as [r ofs]; simpl in *.
             destruct (B#r) eqn:Br; simpl in *; try inv H3. 
             machMonadInv H0. 
             econstructor...
             unfold lea. simpl. rewrite Br...
          * unfold lea in *. destruct r as [r ofs]; simpl in *.
             destruct (B#r) eqn:Br; simpl in *; try inv H3. 
             machMonadInv H0. 
             econstructor...
             unfold lea. simpl. rewrite Br...
          * machMonadInv H3. 
            econstructor...
          * machMonadInv H3. 
            destruct p0. inv H3. 
            econstructor...
        + destruct i; simpl in *; try machMonadInv H3.
          *  rename m  into r1,
                 m0 into r2, 
                 m1 into d.
             destruct (eval_op' o B r1 r2) eqn:X; simpl in *; inv H3.
             unfold eval_op' in X; destruct o; simpl in X. 
             -- destruct (B # r1).
                ++ destruct (B # r2); inv X.
                ++ inv X. 
             -- destruct (B # r1).
                ++ destruct (B # r2); inv X.
                ++ inv X. 
          * unfold lea in *.  destruct r as [r ofs]; simpl in *. 
            destruct (B#r) eqn:Br; simpl in *; try inv H3.
            destruct (lookup privilege M (unsigned (add ofs v))) eqn:X;  simpl in H0; inv H0. 
            econstructor...
            unfold lea.  simpl.  rewrite Br. auto.
          * unfold lea in *.  destruct r as [r ofs]; simpl in *. 
            destruct (B#r) eqn:Br; simpl in *;  try inv H3. 
            destruct (writedown privilege destination_tag M (unsigned (add ofs v)) (B !! m)) eqn: X; simpl in H0; inv H0. 
            econstructor...
            unfold lea. simpl. rewrite Br. auto. 
          * destruct (lookup_function i p); inv H3. 
          * destruct (perform_builtin b B M) eqn:?; try destruct p0; inv H3. 
            econstructor...
    Qed.

  End  Transitions.

  Definition Mach_semantics (p:program) : semantics.
  Proof.
    refine (@Semantics_gen 
            state
            program
            mval
            failure 
            step 
            (initial_state p) 
            final_state
            failstop_state
            _
            p). 
    intros.
    intro. destruct H. inv H.  inv H0. 
  Defined.

  Lemma deterministic: forall p,
      determinate (Mach_semantics p).
  Proof.
    intros p. 
    refine (@Determinate _ _ _ _ _ _ _).
    - induction 1; intros STEP2; inv STEP2;
         progress (repeat
        (match goal with
        | H : ?x::?xt = ?y::?yt |- _ => try inv H; eauto
        | H : ?x::?xt = [] |-  _ => try inv H; eauto
        | H : [] = ?x::?xt |-  _ => try inv H; eauto
        | H1 : ?x = ?y,
          H2 : ?x = ?z |- _ => rewrite H1 in H2; try inv H2; auto
        | _ => auto 
        end)).
    - intros. inv H.  inv H0. rewrite H1 in H. inv H. auto. 
    - intros. intro. intro. inv H. inv H0.  rewrite H5 in H1.  inv H1.  
    - intros.  inv H.  inv H0.  auto. 
    - intros. intro. intro. inv H.  inv H0. 
    - intros. inv H.  inv H0.  auto.
  Qed.



End    Semantics.

