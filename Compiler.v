(* Concrete C *)

(* Compiler from RTL to Mach *)

Require Import Errors.
Require Integers.
Import Integers.Int64.
Require Import Defns RTL Mach.
Import ListNotations.
Local Open Scope Z.

Module Type CompilerParameters.

  Parameter maxFrameSize : Z. 

  Axiom maxFrameSizeBounded1 : maxFrameSize + maxFrameSize <= max_unsigned.  
  (* This ensures that all offsets from the sp into our own frame (for locals, etc.)
     and into our caller's frame (for parameters) are expressible in Int64.
     It's slightly stronger than needed, but simple. *)

  (* If the frame is going to overflow the stack, we want to detect this eagerly at function
     entry, in order to match the source memory signature. We achieve this as a by-product of
     doing the initializing writes to the protected parts of the frame.
     This motivates the positioning of the RA _below_ the array (because the RA slot is the
     only thing we can be certain will exist and be initialized).
     In order for this to work, we must ensure a large enough "guard region" below the stack,
     so that SP-maxFrameSize doesn't end up in the heap by accident, i.e. 
     end up in the heap, i.e.

     maxFrameSizeBounded2:  maxFrameSize <= StkLimit - HpLimit.

     (This also indirectly guarantees that SP-maxFrameSize doesn't underflow.)

     Since the StkLimit and HpLimit are Mach parameters, we make this a side-condition on the proof itself. *)

End CompilerParameters.

Module Functor (Import parameters: CompilerParameters).
  Declare Scope compiler_scope.
  Delimit Scope compiler_scope with compiler.
  Local Open Scope mach_scope.
  Local Open Scope compiler_scope.
  Local Open Scope error_monad_scope.


  (*******************************************)
  (**                                       **)
  (**              Layout                   **)
  (**                                       **)
  (*******************************************)

  
  Definition locals_ofs f := max_callee_params f.
  Definition ra_ofs f := (locals_ofs f + length (locals f))%nat.
  Definition arr_ofs f :=  (ra_ofs f + 1)%nat.
  Definition frame_size f := (arr_ofs f + f.(sz_a))%nat.
  Definition params_ofs f := frame_size f. 

  Ltac unfold_layout :=
    try unfold params_ofs in *;
    try unfold frame_size in *;
    try unfold arr_ofs in *;
    try unfold ra_ofs in *;
    try unfold locals_ofs in *.


  (* The Mach tags that will form the basis of our protection *)
  (* in the comments "protects" should be understood as "tags [object] with t_pro" *)
  Local Definition Madd := Mop Oadd.
  Local Definition Msub := Mop Osub.
  (**)

  (*******************************************)
  (**                                       **)
  (**              Stack maps               **)
  (**                                       **)
  (*******************************************)

  (* Stack maps tell us where RTL locals (& params) are
       in the a Mach fn's AR, as offsets from the SP. They
       are (then obviously) defined on a per-function
       basis. *)
  Definition stkmap := Regset.t nat.

  Definition new_stkmap := Regset.empty nat.

  (* The -1 here is of course bogus, but may be helpful to avoid handling nonsense cases *)
  Definition getofs (map: stkmap) r : Z := match map ! r with Some x => x | _ => -1 end.
  Notation "m '@' s" := (getofs m s) (at level 1) : compiler_scope.
  Notation "r 'in_map' m" := (m @ r >= 0) (at level 60).

  Remark in_map_dec : forall r (m: stkmap),
    { r in_map m } + { ~ (r in_map m) }.
  Proof.
    intros. destruct (m ! r) eqn: X.
    - left. unfold getofs. rewrite X. lia'. 
    - right. intro. unfold getofs in H.  rewrite X in H. lia'.
  Qed.

  Lemma in_map_exists : forall m r,
      r in_map m ->
      exists n, m ! r = Some n.
  Proof.
    intros.
    unfold getofs in H.
    destruct (m!r) eqn:Q; try lia'.
    exists n; auto.
  Qed.
  
  Fixpoint add_regs map_acc (n: nat) (regs: list reg) : stkmap :=
    match regs with
    | h :: t => (add_regs map_acc (S n) t) ! h <- n
    | []     => map_acc
    end.

  Lemma add_regs_in : forall regs m0 n r,
      In r regs ->
      r in_map (add_regs m0 n regs).
  Proof.
    unfold getofs. 
    induction regs; intros.
    - inv H.
    - destruct H. 
      + subst. simpl. 
        rewrite Regset.gss.  lia'. 
      + simpl. 
        destruct (Pos.eq_dec r a). 
        * subst. rewrite Regset.gss. lia'. 
        * rewrite Regset.gso; auto.
  Qed.

  Lemma add_regs_not_in : forall regs m0 n r,
      ~ In r regs ->
      r in_map (add_regs m0 n regs) = r in_map m0. 
  Proof.
    unfold getofs. 
    induction regs; intros.
    - auto.
    - destruct (Pos.eq_dec r a). 
      + subst. 
        exfalso. apply H. left. auto.
      + simpl. rewrite Regset.gso; auto.
        eapply IHregs. intro. apply H. right. auto.
  Qed.

  Definition make_map (f: RTL.function) := 
    if (frame_size f <=? maxFrameSize) && (length (params f) <=? maxFrameSize)
    then
      let m1 := add_regs new_stkmap (locals_ofs f) (locals f) in 
      OK (add_regs m1 (params_ofs f) (params f))
    else
      e_msg " uses too many pseudo-registers.\n" .  

  Lemma map_in : forall f r m,
      make_map f = OK m ->
      In r (locals f) \/ In r (params f) -> 
      r in_map m.
  Proof.
    intros.
    unfold make_map in H. monadInv H. 
    destruct H0. 
    - rewrite add_regs_not_in. eapply add_regs_in. auto. 
      intro. eapply locals_params_disjoint; eauto.  
    - eapply add_regs_in. auto.
  Qed.

  Lemma code_in : forall f r m,
      make_map f = OK m ->
      In r (regs_c f.(RTL.body)) ->
      r in_map m. 
  Proof.  
    intros.
    eapply map_in; eauto.
    eapply local_or_param; eauto.
  Qed.


  (* Alternative presentation that is more explicit about locations. *)
  Fixpoint locate (x:reg) (xs: list reg) : option nat :=
    match xs with
    | [] => None
    | y::ys => if Pos.eqb x y then Some O else
                 match locate x ys with
                 | None => None
                 | Some n => Some (S n)
                 end
    end.


  Lemma locate_nth_error: forall xs x n,
      locate x xs = Some n ->
      List.nth_error xs n = Some x. 
  Proof.
    induction xs; intros.
    - inv H. 
    - unfold locate in H. destruct (Pos.eqb_spec x a). 
      + inv H.  auto.
      + maybeMonadInv H. simpl. eauto.
  Qed.

  Lemma locate_bound : forall n (r:reg) rs,
      locate r rs = Some n ->
      (n < length rs)%nat. 
  Proof.
    intros. 
    apply locate_nth_error in H. 
    eapply nth_error_Some. intro X. rewrite H in X. discriminate X. 
  Qed.


  Lemma locate_add_regs: forall regs map0 base r,
      getofs (add_regs map0 base regs) r =
        match locate r regs with
          Some n => base + n
        | None => getofs map0 r
        end.
  Proof.
    induction regs; intros.
    - auto.
    - simpl. 
      unfold getofs in *. 
      destruct (Pos.eqb_spec a r). 
      + subst. rewrite Regset.gss. 
        unfold locate. 
        rewrite Pos.eqb_refl. lia'.
      + rewrite Regset.gso; try lia. 
        rewrite Pos.eqb_sym.
        apply Pos.eqb_neq in n. rewrite n. 
        rewrite IHregs.
        destruct (locate r regs) eqn:?.
        * lia'.
        * auto.
  Qed.

  Definition reg_slot (f: RTL.function) (r:reg) : Z :=
    match locate r (params f) with
    | Some n => params_ofs f + n 
    | None =>
        match locate r (locals f) with
        | Some n => locals_ofs f + n
        | None => -1
        end
    end.

  Lemma reg_slot_map: forall f map,
      make_map f = OK map -> 
      forall r, 
      getofs map r = reg_slot f r.
  Proof.
    intros. 
    unfold make_map in H. 
    monadInv H. 
    rewrite locate_add_regs. 
    rewrite locate_add_regs.
    unfold reg_slot. 
    unfold new_stkmap. unfold getofs. rewrite Regset.gempty.
    auto.
  Qed.

  (**)

  (*************************************************)
  (*                                               *)
  (*     Instruction translation & Auxillaries     *)
  (*                                               *)
  (*************************************************) 
  Section InstrTranslation.
    (* Instruction translation has to be parameterized by (a single) stkmap,
     hence this variable. *)
    Variable map: stkmap. 

    (* deposit & withdraw are just a privileged load & store, but whose source & dest locations
       are (calculated from) a RTL reg's offset. *)
    (* "deposit" because loads put something into the (register) "bank", "withdraw" similarly *)
    (* withdraw also protects the destination *)
    
    Definition Mstore_hp := Mstore hi t_pro.

    Definition deposit  (s: reg) (d: mreg) : instr := Mload hi  (SP, val_of_Z (map@s)) d.
    Definition withdraw (s: mreg) (d: reg) : instr := Mstore_hp s (SP, val_of_Z(map@d)).


    Fixpoint pp_rec (ofs:nat) params : code :=
      match params with [] => [] | h :: t =>
                                     pp_rec (1 + ofs) t      ++
                                       [deposit h GP1;
                                        Mstore_hp GP1 (SP+ ofs)]
      end.
    (* Pushes callee's parameters onto the stack just before a call *)
    Definition push_params (params: list reg) : code := pp_rec O params.

    Definition transl_instr arr_ofs i : code :=
      match i with

      | Imov s d =>
          deposit  s GP1 ::    (* load from where s is in the frame, into GP1 *)
          withdraw GP1 d ::    (* store from GP1 to where d is in the frame   *)
          []
          
      | Imovi v d =>
          Mmovi v GP1    ::    (* movi a val into GP1 *)
          withdraw GP1 d ::    (* store from GP1, to where d is in the frame *)
          []
          
      | Iop op s1 s2 d =>
          deposit s1 GP1     ::
          deposit s2 GP2     ::
          Mop op GP1 GP2 GP3 ::
          withdraw GP3 d     ::
          []
          
      | Iamper rd =>
          (* Iamper returns the _addr_ of the base of an RTL's local array. *)
          Mmovi arr_ofs GP1 ::   (* GP1 := arr_ofs *)
          Madd GP1 SP GP1    ::   (* GP1 := arr_ofs + SP *)
          withdraw GP1 rd    ::
          []

      | Iload s d =>
          (* RTL reg s contains a raw address, e.g. computed from some arr base *)
          deposit s GP1           ::      (* raw address, [addr] (pointing into array) *)
          Mload lo (GP1,NULL) GP1 ::      (* [*addr] into [GP1] *)
          withdraw GP1 d          ::      (* [*addr] into where [d] is mapped on the stack *)
          []

      | Istore s d =>
          (* d contains a raw address, s contains a payload to be written to mem *)
          deposit s GP1                    ::    (* put payload into GP1 *)
          deposit d GP2                    ::    (* put tgt addr into GP2 *)
          Mstore lo t_unp GP1 (GP2,NULL)   ::    (* store *)
          []

      | Icall cee_id args d =>
          push_params args  ++     (* push callee params *)
          Mjal cee_id       ::     (* make the call *)
          withdraw RV d     ::     (* save the RV *)
          []

      (* There is no explicit Ireturn instruction; instead, Return happens by
         falling off the end of the code sequence, and is handled in the [exit] code sequence. *)
      end.
    
    Definition transl_instrs arr_ofs := flat_map (transl_instr arr_ofs). 

  End     InstrTranslation.
  
  (********************************)
  (*                              *)
  (*     Function translation     *)
  (*                              *)
  (********************************)

  (* tagging for stk -alloc and -free *)
  Fixpoint stk_tag tag (ofs: nat) slots : code :=
    let rec := stk_tag tag in
    match slots with
    | S n => Mstore hi tag GP1 (SP+ofs) :: rec (S(ofs)) n
    | O   => []
    end.
  Definition   protect := stk_tag t_pro.
  Definition unprotect := stk_tag t_unp.
  (**)
  (**)

  (* fn pre- & post- ludes *)
  Definition entry f := 
    Mmovi (val_of_Z (frame_size f))  GP1         ::    (* move the SP *)
      Msub SP GP1 SP         ::    (* move the SP *)
      Mmovi NULL GP1         ::    (* zero/protect locals and CPR *)
      protect 0 (max_callee_params f) ++  
      protect (locals_ofs f) (length (locals f)) ++ 
      Mstore_hp RA (SP+ (ra_ofs f)) ::  (* save & protect ra *)
      [].

  Definition exit map f := 
    deposit map f.(rreg) RV       ::     (* save rv into RV *)
    [ Mload hi (SP+ (ra_ofs f)) RA    (* restore ra *)
    ; Mmovi NULL GP1                     (* & zero/unprotect it *)
    ; Mstore hi t_unp GP1 (SP+ (ra_ofs f))] ++   
    unprotect 0 (max_callee_params f) ++  (* zero/unprotect callee parameter region *)
    unprotect (locals_ofs f) (length (locals f)) ++ (* zero/unprotect locals *)
    Mmovi (val_of_Z (frame_size f)) GP1 :: (* amount to adjust the SP *)
    Madd SP GP1 SP                         :: (* adjust the SP *)
    [].

  Definition transl_function (f: RTL.function) : res function := 
    do map <- make_map f; 
    OK (mkfunction (RTL.f_id f)
                   (entry f ++ 
                    transl_instrs map (val_of_Z (arr_ofs f)) f.(RTL.body) ++
                    exit map f)).

  Lemma transl_function_id : forall f tf,
      transl_function f = OK tf ->
      RTL.f_id f = f_id tf. 
  Proof.
    intros. unfold transl_function in H.  monadInv H.  simpl. auto.
  Qed.


  (*******************************)
  (*                             *)
  (*     Program translation     *)
  (*                             *)
  (*******************************)

  Definition builtins :=
    [mkfunction RTL.Bmalloc_id [Mbuiltin Bmalloc];
     mkfunction RTL.Bfree_id  [Mbuiltin Bfree]].

  Fixpoint transl_prog (p: RTL.program) : res program  :=
    match p with
      [] => OK builtins
    | f :: t =>
        do f' <- transl_function f;
        do p' <- transl_prog t;
        OK (f'::p') 
    end. 

  Local Close Scope compiler_scope.

End    Functor. 

