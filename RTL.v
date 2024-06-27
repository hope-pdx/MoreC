(* Concrete C *)

(* Source language definition and semantics. *)

Require Import Integers.
Require Import Defns Mem Smallstep Behaviors.
Import ListNotations.
Require Import ListSet.
Import Int64.

Section Language.
  Inductive instr : Type :=
    | Imov : reg -> reg -> instr  
    | Imovi: val -> reg -> instr
    | Iop  : operation -> reg -> reg -> reg -> instr
    | Iamper : reg -> instr
    | Iload : reg -> reg -> instr
    | Istore : reg -> reg -> instr
    | Icall: ident -> list reg -> reg -> instr
    .

  Definition code : Type := list instr.

  Record function : Type := mkfunction
    { f_id : ident
    ; params: list reg
    ; params_NoDup: NoDup params
    ; sz_a  : nat
    ; body  : code
    ; rreg  : reg }.

  Definition program := list function.

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

  Lemma lookup_function_spec2: forall i p f,
      lookup_function i p = Some f -> In f p. 
  Proof.
    induction p; intros.
    - inv H. 
    - inv H. destruct (Pos.eqb_spec i (f_id a)). 
      + subst. inv H1. left; auto.
      + right. eapply IHp; auto.
  Qed.

  (* We pre-allocate certain identifiers as built-in functions.
     (If these identifiers are re-used as function identifiers,
     the builtins will be hidden, which is fine.) *)
  Inductive builtin : Type :=
    Bmalloc 
  | Bfree
  .

  Definition Bmalloc_id := 1%positive.
  Definition Bfree_id := 2%positive.

  Definition builtin_id (b: builtin) : ident := 
    match b with
    | Bmalloc => Bmalloc_id
    | Bfree => Bfree_id
    end.

  Definition lookup_builtin (i:ident) : option builtin :=
    if Pos.eqb i Bmalloc_id then
      Some Bmalloc
    else if Pos.eqb i Bfree_id then
      Some Bfree
    else
      None.      

  Lemma lookup_builtin_spec: forall i b,
    lookup_builtin i = Some b -> 
    builtin_id b = i.           
  Proof.
    intros.
    unfold lookup_builtin in H. 
    destruct (Pos.eqb_spec i Bmalloc_id); inversion H; auto.
    destruct (Pos.eqb_spec i Bfree_id); inversion H; auto. 
  Qed.
  
  Definition builtin_arity (b:builtin) : nat :=
      match b with
      | Bmalloc => 1
      | Bfree => 1
      end.

   Inductive callable :=
   | Func : function -> callable
   | Builtin : builtin -> callable.


   Definition callable_id (c:callable) : ident :=
     match c with
     | Func f => f.(f_id)
     | Builtin b => builtin_id b
     end.

  Definition lookup_callable (i: ident) (fs: program) : option (callable * nat) := 
    (* let defined functions hide builtins *)
    match lookup_function i fs with
    | Some f => Some(Func f, length (f.(params)))
    | None => match lookup_builtin i with
              | Some b => Some(Builtin b, builtin_arity b)
              | None => None
              end
    end.

  Definition callable_arity (c: callable) :=
    match c with
    | Func f => length (f.(params))
    | Builtin b => builtin_arity b
    end.            


  Lemma lookup_callable_arity_spec : forall i fs c a,
      lookup_callable i fs = Some(c,a) ->
          callable_arity c = a. 
  Proof.
    intros.
    unfold lookup_callable in H. 
    maybeMonadInv H; simpl; auto. 
  Qed.

  Lemma lookup_callable_id_spec: forall i fs c a,
      lookup_callable i fs = Some(c,a) ->
      callable_id c = i.
  Proof.
    intros.
    unfold lookup_callable in H. 
    maybeMonadInv H; simpl.
    - eapply lookup_function_spec; eauto.  
    - eapply lookup_builtin_spec; eauto.
  Qed.       

End     Language.

Section WellTyped.

  (* This typing is used to establish that the semantics never gets stuck.
     It just needs to check that function calls are valid and have the right arity. *)
 
  Variable p: program.

  Definition wt_inst (i:instr) : Prop :=
    match i with
      Icall callee args dst =>
        match lookup_callable callee p with
        | Some (c,arity) => length args = arity
        | None => False
        end
    | _ => True
    end.             

  Definition wt_function (f:function) : Prop :=
    Forall wt_inst f.(body).

  Definition wt_callable (c:callable) : Prop :=
    match c with
    | Func f => wt_function f 
    | Builtin b => True
    end.

  Definition wt_program : Prop :=
    Forall wt_function p /\
    exists main, hd_error p = Some main /\ params main = []. 

  Lemma wt_program_lookup_f: forall i f,
    wt_program ->
    lookup_function i p = Some f ->
    wt_function f. 
  Proof.
    intros.
    apply lookup_function_spec2 in H0. 
    unfold wt_program in H.  destruct H. 
    rewrite Forall_forall in H. 
    auto.
  Qed.

  Lemma wt_program_lookup : forall i c a,
    wt_program ->
    lookup_callable i p = Some (c,a) ->
    wt_callable c.
  Proof.
    intros.
    unfold lookup_callable in H0. 
    maybeMonadInv H0; simpl; auto. 
    eapply wt_program_lookup_f; eauto.
  Qed. 

End WellTyped.


Module Semantics. 

  Section Top.
  Declare Scope RTLSem_scope.
  Delimit Scope RTLSem_scope with RTLSem.
  Definition label : Type := ident * code. 
  Variable oracle : Oracle label.
  (* Some Notations *)
    Local Notation mem     := (oracle.(mem label)).
    Local Notation initial_mem := (oracle.(initial_mem label)).
    Local Notation stkAlloc   := (oracle.(stkAlloc label)).
    Local Notation hpAlloc   := (oracle.(hpAlloc label)).
    Local Notation stkFree    := (oracle.(stkFree label) ).
    Local Notation hpFree    := (oracle.(hpFree label) ).
    Local Notation load    := (oracle.(load label)    ).
    Local Notation store   := (oracle.(store label)   ).
    Local Notation perturb := (oracle.(perturb label) ).
    Local Notation AllocatedStk := (oracle.(AllocatedStk label)).
    Local Notation AllocatedHp := (oracle.(AllocatedHp label)).
  Local Open Scope RTLSem_scope.

  Definition regbank := Regmap.t val.

  Inductive stack : Type :=
    | StkNil : stack
    | StkFrame :
        forall (dest_in_caller    : reg     )
               (callers           : function)
               (return_site       : code    )
               (callers_arr_base  : Z       )
               (callers_rb        : regbank )
               (stk               : stack   ),
        stack
  .

  Fixpoint stackDepth (s:stack) : nat :=
    match s with
    | StkNil => O
    | StkFrame _ _ _ _ _ s => S(stackDepth s)
    end.


  (* Failstop codes *)
  Inductive failure := 
  | OOM : failure    (* out of memory *)
  | OOB : failure    (* out of bounds -- includes bad heap free arg *)
  .


  Inductive state : Type :=
    | State : forall
          (curr_fn : function)
          (pc      : code    )
          (arr_base: Z       )
          (B       : regbank )
          (M       : mem     )
          (cs      : stack   ),
        state
    | Callstate : forall
          (cee  : callable)
          (args : list val)
          (M    : mem     )
          (cs   : stack   ),
        state
    | Returnstate : forall
          (ret_val : val  )
          (M       : mem  )
          (cs      : stack),
        state
    | Failstop : failure -> state.


  Inductive initial_state (p : program) : state -> Prop :=
    | initial_state_intro : forall main,
        List.hd_error p = Some main ->
        main.(params) = [] -> 
        initial_state p (Callstate (Func main) nil initial_mem StkNil).

  Inductive final_state : state -> val -> Prop :=
    | final_state_intro : forall v xx,
        final_state (Returnstate v xx StkNil) v.

  Inductive failstop_state : state -> failure -> Prop :=
    | failstop_state_intro: forall failure,
       failstop_state (Failstop failure) failure.     
 
  (* This should probably complain if given the wrong number of vals, or at least if not enough.
     But evidently this is not needed for the compiler correctness proof. *)
  Fixpoint init_regs (rs: list reg) (vs: list val) {struct rs} : regbank :=
    match rs, vs with
    | r :: rs, v :: vs => Regmap.set r v (init_regs rs vs)
    | _      , _       => Regmap.init def_val
    end.

  (* Builtins *)

  Local Open Scope smem_scope.

  (* Can only fail if number of arguments is wrong. *)
  Definition perform_builtin (b:builtin) (args:list val) (M: mem) : option ((val * mem) + failure) := 
    match b with
    | Bmalloc =>
        match args with
        | [sz] =>  match hpAlloc M (Bmalloc_id,[])  (Z.to_nat (unsigned sz))  with
                   | Some (r,M') => Some(inl(val_of_Z (base r),M'))
                   | None => Some (inr OOM)
                   end
        | _ => None
        end
    | Bfree =>
        match args with
        | [a] => if Z.eq_dec (unsigned a) (unsigned NULL)  then
                   Some(inl(NULL,M))
                 else
                   match hpFree M (unsigned a) with
                   | Some M' => Some(inl(NULL,M'))
                   | None => Some (inr OOB)
                   end
        | _ => None
        end
    end.

  
  Section RELSEM.

    Variable p: program. 


    Inductive step : state -> state -> Prop :=

    | exec_Imov : forall f pc arb B M cs pc' rd vs rs, 
        pc = Imov rs rd :: pc' ->
        B#rs = vs ->
        step (State f pc  arb  B           M cs)
             (State f pc' arb (B#rd <- vs) M cs)

    | exec_Imovi : forall f pc arb B M cs pc' rd imm, 
        pc = Imovi imm rd :: pc' ->
        step (State f pc  arb  B            M cs)
             (State f pc' arb (B#rd <- imm) M cs)

    | exec_Iop : forall f pc arb B M cs pc' rd v op r1 r2 v1 v2, 
        pc = Iop op r1 r2 rd :: pc' ->
        B # r1 = v1 ->
        B # r2 = v2 ->
        v = eval_op op v1 v2 ->
        step (State f pc  arb  B          M cs)
             (State f pc' arb (B#rd <- v) M cs)

    | exec_Iamper : forall f pc arb B M cs pc' r, 
        pc = Iamper r :: pc' ->
        step (State f pc  arb  B           M cs)
             (State f pc' arb (B#r <- (val_of_Z arb)) M cs)

    | exec_Iload_M : forall f pc arb (B:regbank) M cs pc' rd rloc v, 
        pc = Iload rloc rd :: pc' ->
        load M (unsigned (B#rloc)) = Some v ->
        step (State f pc  arb  B          M cs)
             (State f pc' arb (B#rd <- v) M cs)

    | exec_Iload_M_OOB : forall f pc arb (B:regbank) M cs rloc pc' rd,
        pc = Iload rloc rd :: pc' ->
        load M (unsigned (B#rloc)) = None ->
        step (State f pc arb B M cs)
             (Failstop OOB)

    | exec_Istore_M : forall f pc arb (B:regbank) M cs pc' M' rs rloc, 
        pc = Istore rs rloc :: pc' ->
        store M (unsigned (B#rloc)) (B#rs) = Some M' ->
        step (State f pc  arb B M  cs)
             (State f pc' arb B M' cs)

    | exec_Istore_M_OOB : forall f pc arb (B:regbank)  M cs rs rloc pc',
        pc = Istore rs rloc :: pc' ->
        store M (unsigned (B#rloc)) (B#rs) = None ->
        step (State f pc  arb B M  cs)
             (Failstop OOB)

    | exec_Icall_M : forall f pc arb B M cs pc' cee args M' rx cee_id arity, 
        pc = Icall cee_id args rx :: pc' ->
        lookup_callable cee_id p = Some (cee,arity) ->
        arity = length args ->
        perturb M (f.(f_id),pc) = Some M' ->  
        step (State f pc arb B M cs)
             (Callstate cee (B##args) M' (StkFrame rx f pc' arb B cs))

    | exec_Icall_M_OOM : forall f pc arb B M cs pc' cee_id args rx,
        pc = Icall cee_id args rx :: pc' ->
        perturb M (f.(f_id),pc)  = None -> 
        step (State f pc arb B M cs)
             (Failstop OOM)

    | exec_pass_control_M : forall (f:function) args cs M M' r, 
        stkAlloc M (f.(f_id),f.(body)) f.(sz_a) = Some (r, M') ->
        step (Callstate (Func f) args M cs)
             (State f f.(body) (fst r) (init_regs f.(params) args) M' cs)

    | exec_pass_control_M_OOM : forall f args M cs,
        stkAlloc M (f.(f_id),f.(body)) f.(sz_a) = None ->
        step (Callstate (Func f) args M cs)
             (Failstop OOM)

    | exec_Ireturn_M: forall f pc arb B M cs M',
        pc = [] ->
        stkFree M = Some M' ->
        step (State f pc arb B M cs)
             (Returnstate B#(f.(rreg)) M' cs)

(* We do not need this rule, since its assumptions can never hold 
    | exec_Ireturn_M_underflow: forall f arb B M cs,
        (* pc = Ireturn r :: xx -> *)
        stkFree M = None ->
        step (State f [] arb B M cs)
             (Failstop StkUnderflow)
*)

    | exec_return_control_M : forall v rx f pc arb B cs M M', 
        perturb M (f.(f_id),pc) = Some M' ->     
        step (Returnstate v M (StkFrame rx f pc arb B cs))
             (State f pc arb (B#rx <- v) M' cs)

    | exec_return_control_OOM : forall v rx f pc arb B cs M,
        perturb M (f.(f_id),pc) = None -> 
        step (Returnstate v M (StkFrame rx f pc arb B cs))
             (Failstop OOM)
             
    | exec_builtin_M : forall b args cs M M' v,
        perform_builtin b args M = Some(inl(v,M')) -> 
        step (Callstate (Builtin b) args M cs)
             (Returnstate v M' cs) 

    | exec_builtin_M_Fail : forall b args cs M c, 
        perform_builtin b args M = Some(inr c) -> 
        step (Callstate (Builtin b) args M cs)
             (Failstop c)
  . 
  
  End     RELSEM.

  Definition RTL_semantics (p:program) : semantics.
  Proof.
    refine (@Semantics_gen 
            state
            program
            val
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
      determinate (RTL_semantics p).
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
        | _ => idtac
        end)).
    - intros. inv H.  inv H0. rewrite H1 in H. inv H. auto.
    - intros. intro. intro. inv H. inv H0. 
    - intros.  inv H.  inv H0.  auto.
    - intros. intro. intro. inv H.  inv H0. 
    - intros. inv H.  inv H0.  auto.
  Qed.

  End Top.


End    Semantics.


Module Progress.

  (* Under suitable well-formedness conditions on calls, the step function never gets stuck. *)

  Import Semantics.
  Section Top.
  Variable oracle : Oracle label. 



  (* Some Notations *)
  Local Notation mem     := (oracle.(mem label)). 
  Local Notation initial_mem := (oracle.(initial_mem label)).
  Local Notation stkAlloc   := (oracle.(stkAlloc label)).
  Local Notation hpAlloc   := (oracle.(hpAlloc label)).
  Local Notation stkFree    := (oracle.(stkFree label) ).
  Local Notation hpFree    := (oracle.(hpFree label) ).
  Local Notation load    := (oracle.(load label)    ).
  Local Notation store   := (oracle.(store label)   ).
  Local Notation perturb := (oracle.(perturb label) ).
  Local Notation AllocatedStk := (oracle.(AllocatedStk label)).

  Local Notation step := (step oracle). 

  Variable p: program.

  Inductive SM : state oracle -> Prop :=
  | SMState : forall cf pc ab B M cs,
      length (AllocatedStk M) >= S(stackDepth cs) -> 
      SM (State oracle cf pc ab B M cs)  
  | SMCallstate: forall cee args M cs,
      length (AllocatedStk M) >= stackDepth cs ->
      SM (Callstate oracle cee args M cs)
  | SMReturnstate : forall rv M cs,
      length (AllocatedStk M) >= stackDepth cs -> 
      SM (Returnstate oracle rv M cs)
  | SMFailstop : forall failure,
      SM (Failstop oracle failure) (* ???? *)
  .


  Lemma SM_initial_state: forall s,
      initial_state oracle p s -> SM s. 
  Proof.
    intros.
    inv H. 
    econstructor. 
    simpl. lia'. 
  Qed.

  Lemma SM_preserved: forall s,
      SM s -> forall s',
        step p s s' ->
        SM s'. 
  Proof.
    intros.
    inv H0; try (inv H; constructor; auto). 
    - eapply store_stable_status in H2. 
      inv H2. inv H. 
      auto. 
    - eapply perturb_stable_status in H4. 
      inv H4. inv H. 
      auto.
    - apply stkAlloc_charact in H1. destruct H1. rewrite H. simpl. lia'.
    - destruct (stkFree_charact _ _ _ _ H2) as [r [P _]]. 
      rewrite  P in H1. simpl in H1.  lia'. 
    - eapply perturb_stable_status in H1. 
      inv H1. inv H.
      auto.
    - unfold perform_builtin in H1.
      destruct b. 
      + maybeMonadInv H1; auto.
        destruct (hpAlloc_charact _ _ _ _ _ _ _ Heqo) as [P1 P2].
        rewrite P2.  auto.
      + maybeMonadInv H1; auto.  
        destruct (hpFree_charact _ _ _ _ _  Heqo) as [r [P1 [P2 P3]]]. 
        rewrite P3.  auto.
  Qed.

  Lemma SM_preserved_star: forall s s',
        star step p s s' ->
        SM s -> SM s'.
  Proof.
    induction 1; intros. 
    - auto. 
    - apply IHstar.
      eapply SM_preserved; eauto.
  Qed.

  Variable wtp: wt_program p.

  Fixpoint wt_stack (cs:stack) : Prop :=
    match cs with
    | StkNil => True
    | StkFrame _ _ code _ _ cs => Forall (wt_inst p) code /\ wt_stack cs
    end.


  Definition wt_state (s:state oracle) : Prop :=
    match s with
    | State _ code _ _ _ cs =>
        Forall (wt_inst p) code /\ wt_stack cs
    | Callstate c args _ cs =>
        wt_callable p c /\ 
          callable_arity c = length args /\
          wt_stack cs
    | Returnstate _ _ cs => wt_stack cs
    | Failstop _  => True
    end.


  Lemma wt_initial_state: forall s,
      initial_state oracle p s ->
      wt_state s. 
  Proof.
    intros.
    inv H. 
    assert (hd_error p = Some main /\ tl p = tl p) by (split; auto).
    rewrite hd_error_tl_repr in H.  (* ugh! *)
    simpl. intuition.
    rewrite H in *. 
    inv wtp. inv H2. 
    auto.
    rewrite H1. auto.
  Qed.

  Lemma wt_preserved: forall s,
      wt_state s ->
      forall s', 
        step p s s' ->
        wt_state s'. 
  Proof.
    intros.
    inv H0; try (inv H; inv H0; simpl; intuition). 
    eapply wt_program_lookup; eauto. 
    apply lookup_callable_arity_spec in H2. 
    rewrite map_length. auto.
  Qed.    

  Lemma wt_preserved_star : forall s s',
      star step p s s' ->
      wt_state s ->
      wt_state s'. 
  Proof.
    induction 1; intros.
    - auto.
    - apply IHstar.
      eapply wt_preserved; eauto.
  Qed.

  Lemma step_progress: forall s,
      (forall v, ~final_state oracle s v) ->
      (forall f, ~failstop_state oracle s f) ->
      SM s ->
      wt_state s -> 
      exists s', step p s s'. 
  Proof.
    intros.
    destruct s. 
    - destruct  pc; intros. 
      + destruct (stkFree M) as [M'|] eqn:?.
        * eexists. eapply exec_Ireturn_M; eauto. 
        * apply stkFree_charact_failure in Heqo. 
          inv H1.  rewrite Heqo in H4. inv H4. 
      + destruct i.
        * eexists; eapply exec_Imov; eauto.
        * eexists; eapply exec_Imovi; eauto.
        * eexists; eapply exec_Iop; eauto.
        * eexists; eapply exec_Iamper; eauto.
        * destruct (load M (unsigned (B#r))) as [v'|] eqn:?.
          -- eexists; eapply exec_Iload_M; eauto.
          -- eexists; eapply exec_Iload_M_OOB; eauto.
        * destruct (store M (unsigned (B#r0)) (B#r)) as [M'|] eqn:?.
          -- eexists; eapply exec_Istore_M; eauto.
          -- eexists; eapply exec_Istore_M_OOB; eauto.
        * destruct (perturb M (curr_fn.(f_id),(Icall i l r :: pc))) as [M'|] eqn:?. 
          -- inv H1. inv H2. inv H1. simpl in H6.
             destruct (lookup_callable i p) as [[cee arity]|] eqn:P1; try intuition. 
             eexists; eapply exec_Icall_M; eauto.
          -- eexists; eapply exec_Icall_M_OOM; eauto.
    - destruct cee.
      + destruct (stkAlloc M (f.(f_id),f.(body)) (f.(sz_a))) as [rM'|] eqn:?.
        * destruct rM' as [r M'].
          eexists; eapply exec_pass_control_M; eauto.
        * eexists; eapply exec_pass_control_M_OOM; eauto.
      + inv H2. inv H4. inv H3. 
        destruct b; simpl in H2. 
        * destruct args eqn:?; try inv H2. 
          destruct l; try inv H4. 
          assert (exists r, perform_builtin oracle Bmalloc [v] M = Some r). 
          {  unfold perform_builtin.
             destruct (hpAlloc M (Bmalloc_id,[]) (Z.to_nat (unsigned v))). 
             + destruct p0.  eexists;eauto. 
             + eexists; eauto.
          }
          destruct H2 as [r P]. 
          destruct r. 
          -- destruct p0. eexists; eapply exec_builtin_M; eauto.
          -- eexists; eapply exec_builtin_M_Fail; eauto.
        * destruct args eqn:?; try inv H2. 
          destruct l; try inv H4. 
          assert (exists r, perform_builtin oracle Bfree [v] M = Some r).
          { unfold perform_builtin.
            unfold eq. 
            destruct (Z.eq_dec (unsigned v) (unsigned NULL)). 
            - eexists; eauto.
            - destruct (hpFree M (unsigned v)). 
              + eexists; eauto.
              + eexists; eauto.
          }
          destruct H2 as [r P]. 
          destruct r. 
          -- destruct p0. eexists; eapply exec_builtin_M; eauto.
          -- eexists; eapply exec_builtin_M_Fail; eauto.
    - destruct cs. 
      + exfalso. apply (H ret_val).  econstructor.
      + destruct (perturb M (callers.(f_id), return_site)) eqn:?.
        * eexists; eapply exec_return_control_M; eauto.
        * eexists; eapply exec_return_control_OOM; eauto.
    - exfalso. eapply H0.  econstructor.
  Qed.  

  Lemma program_progress:  forall s0,
      initial_state oracle p s0 ->
      forall s,
        star step p s0 s -> 
        (forall v, ~final_state oracle s v) ->
        (forall f, ~failstop_state oracle s f) ->
        exists s', step p s s'. 
  Proof.
    intros.
    eapply step_progress; auto.
    - eapply SM_preserved_star; eauto.
      eapply SM_initial_state; eauto.
    - eapply wt_preserved_star; eauto.
      eapply wt_initial_state; eauto.
  Qed.


  Lemma well_typed_not_wrong: 
    forall behS,
      program_behaves (RTL_semantics oracle p) behS ->
      not_wrong behS. 
  Proof.
    intros.
    inv H. 
    - inv H1; try constructor. 
      exfalso.
      unfold nostep in H2.
      destruct (program_progress _ H0 _ H H3 H4) as [s'' P]. 
      eapply H2; eauto.
    - inv wtp. destruct H1 as [main [P1 P2]].
      eapply H0. 
      econstructor; eauto.
  Qed.


  End Top.

End Progress.

(** Utility functions on RTL. *)

Fixpoint cmp_rec (c: code) : nat :=
  match c with
  | Icall _ args _ :: c' => max (length args) (cmp_rec c')
  | _ :: c'              => cmp_rec c' 
  | []                  => O
  end.

Lemma cmp_code : forall (c:code) args f rx,
    In (Icall f args rx) c ->
    length args <= cmp_rec c.
Proof.
  induction c; intros. 
  - inv H. 
  - inv H. 
    + simpl. lia. 
    + pose proof (IHc _ _ _ H0). 
      simpl. destruct a; lia. 
Qed.

Definition max_callee_params f :=
  cmp_rec f.(body). 

Definition regs (i: instr) : list reg :=
  match i with
  | Iamper r
  | Imovi _ r => [r]
  (* | Ireturn r *)
  | Icall _ args r => r :: args
  | Imov   s d
  | Iload  s d
  | Istore s d => [s; d]
  | Iop _ s1 s2 d => [s1; s2; d]
  end.

Definition uniquify xs :=
  fold_right (set_add Pos.eq_dec) nil xs.                  

Lemma In_uniquify : forall xs x,
    In x xs <-> In x (uniquify xs). 
Proof.
  split.
  - induction xs; intros. 
    + inv H. 
    + inv H; simpl. 
      * apply set_add_intro2; auto. 
      * apply set_add_intro1; unfold set_In; eauto. 
  - induction xs; intros. 
    + inv H.
    + simpl in H. apply set_add_elim in H; unfold set_In in H. 
      destruct H.
      * subst; left; auto.
      * right; auto. 
Qed.

Lemma uniquify_nodup: forall xs,
    NoDup(uniquify xs). 
Proof.
  induction xs. 
  - simpl. constructor.
  - simpl. 
    apply set_add_nodup; auto.
Qed.

Definition regs_c (c: code) : list reg :=
  uniquify (List.flat_map regs c).


Definition locals f : list reg :=
  set_diff Pos.eq_dec (set_add Pos.eq_dec f.(rreg) (regs_c f.(body))) f.(params). 

Lemma locals_NoDup : forall f,
    NoDup (locals f). 
Proof.
  unfold locals. intros.
  apply set_diff_nodup. 
  eapply set_add_nodup.
  unfold regs_c.
  apply uniquify_nodup.
Qed.

Lemma locals_params_disjoint: forall f,
    list_disjoint (locals f) (params f). 
Proof.
  unfold locals. unfold list_disjoint. intros.
  apply set_diff_iff in H. 
  intro. subst. intuition.
Qed.


Lemma local_or_param : forall r f,
    In r (regs_c f.(body)) ->
    In r (locals f) \/ In r f.(params).
Proof with auto.
  unfold locals. intros.
  rewrite set_diff_iff. 
  destruct (In_dec Pos.eq_dec r (params f)). 
  - right; auto.
  - left. split; auto. eapply set_add_intro1. auto. 
Qed.

Lemma rreg_local_or_param : forall f,
    In f.(rreg) (locals f) \/ In f.(rreg) (params f). 
Proof.
  intros. 
  destruct (In_dec Pos.eq_dec f.(rreg) (params f)). 
  - right; auto.
  - left. unfold locals. 
    apply set_diff_iff.
    split; auto.
    apply set_add_intro2. auto.
Qed.



            
