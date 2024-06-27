(* Concrete C *)

(* Matching relations for semantics preservation proof. *)

Require Import Defns Mem.
Require Import RTL Mach.
Require Import Compiler SourceMem.
Require Integers. Import Integers.Int64.
Require Import Errors.
Require Import Separation.
Import ListNotations.

Module Relations (Import mparams : MachParameters)
                 (Import cparams : CompilerParameters).

  Module Import SourceMem := SourceMem.Functor cparams mparams .
  Export Compiler. (* this comes from Source Mem, which seems hacky. *)
  (* Don't do the following, because it gives us two copies of the Compiler structure that cause confusion later.
     Module Import Compiler := Compiler.Functor(cparams).  *)

  Module Import RTLS := RTL.Semantics.
  Module Import MacS := Mach.Semantics mparams.
  Module Export Separation := Separation mparams MacS.
  Open Scope compiler_scope.
  Open Scope sep_scope.

  Set Printing Coercions.

  Open Scope mach_scope.
  Open Scope Z_scope.
  Section WithSmem.


  Local Notation smem := SourceMem.mem'.

  Definition match_locals_sep f sB sp :=
    hasvalues (sp + locals_ofs f) 
        (List.map (fun r => Vint (sB # r)) (locals f)) t_pro. 

  Definition match_params_sep f (sB:regbank) sp :=
    hasvalues (sp + (params_ofs f)) (List.map (fun r => Vint (sB # r)) (params f)) t_pro. 

  Definition match_env_sep f (sB:regbank) sp : massert :=
    (match_params_sep f sB sp) ** (match_locals_sep f sB sp).

  Program Definition match_pub_sep (vm: SourceMem.valmem) (lo hi: Z) : massert :=
    {| m_pred := fun m => forall a, lo <= a < hi -> in_bounds a /\ m a = (Vint (vm a),t_unp)
    ; m_footprint := fun a => lo <= a < hi 
    |}.
  Next Obligation.
    unfold unchanged_on in H0. 
    rewrite <- H0.
    auto.
    split; auto; lia'. 
  Qed.
  Next Obligation.
    edestruct (H a).
    lia'.
    auto.
  Qed.

  Section WithSepConj.

    Local Transparent sepconj.  

    Lemma match_pub_sep_split_eqv : forall vm (lo mid hi: Z),
        lo <= mid <= hi -> 
        massert_eqv (match_pub_sep vm lo mid ** match_pub_sep vm mid hi) 
          (match_pub_sep vm lo hi). 
    Proof.
      intros.
      unfold match_pub_sep.
      unfold massert_eqv; split; split; intros; unfold massert_imp in *; simpl in *;
        unfold disjoint_footprint in *; simpl in *; unfold in_bounds in *; intros.
      - destruct H0 as [P1 [P2 P3]]. destruct (Z_lt_dec a mid).
        + apply P1; lia'.
        + apply P2; lia'.
      - destruct (Z_lt_dec a mid); intuition lia'. 
      - split;[|split]; intros. 
        + eapply H0; lia'. 
        + eapply H0; lia'. 
        + lia'.
      - intuition lia'.
    Qed.

  End WithSepConj.


  Lemma frame_separated_eqv: forall vm f sp,
      massert_eqv 
        (match_pub_sep vm sp (sp + (frame_size f))) 
        (match_pub_sep vm sp (sp + (max_callee_params f)) **
           match_pub_sep vm (sp + (locals_ofs f)) (sp + (locals_ofs f) + (length(locals f))) **
           match_pub_sep vm (sp + (ra_ofs f)) (sp + (ra_ofs f) + 1) **
           match_pub_sep vm (sp + (arr_ofs f)) (sp + (arr_ofs f) + f.(sz_a))).
  Proof.           
    intros. unfold_layout.
    repeat rewrite Nat2Z.inj_add. simpl. 
    repeat rewrite Z.add_assoc.
    set (a1 := (sp + max_callee_params f)).
    set (a2 := a1 + length (locals f)).
    set (a3 := a2 + 1). 
    rewrite <- match_pub_sep_split_eqv with (mid := a1); try (unfold_layout; lia'). 
    rewrite <- match_pub_sep_split_eqv with (lo := a1) (mid := a2);  try (unfold_layout; lia'). 
    rewrite <- match_pub_sep_split_eqv with (lo := a2) (mid := a3); try (unfold_layout; lia'). 
    eapply massert_eqv_refl.
  Qed.

  Lemma match_pub_sep_trange_imp: forall vm lo hi,
      massert_imp (match_pub_sep vm lo hi)
        (trange lo hi (fun t => t = t_unp)).
  Proof.
    unfold match_pub_sep.
    unfold massert_imp.
    intros.
    split; intros.
    - simpl in H. simpl.  intros.
      epose proof (H a H0). intuition. rewrite H4; auto.
    - simpl in *. auto.
  Qed.


  (* Separation description of single stack frame, including used parameters from caller.
   (In context, must adjoin unused part of callee params.) *)
  Definition frame_contents f sp retaddr sB vm : massert :=
    match_env_sep f sB sp 
      ** hasvalue (sp + ra_ofs f) retaddr t_pro 
      ** match_pub_sep vm  (sp + arr_ofs f) (sp + arr_ofs f + sz_a f) 
  . 

  Fixpoint stack_contents (cs:RTLS.stack) (retaddrs:list mval) (sp:Z) (callee_param_cnt:nat) vm : massert :=
    match cs, retaddrs with
    | StkNil, _ => pure True  
    | StkFrame rd f ret_site arb sB cs', retaddr::retaddrs' => 
        frame_contents f sp retaddr sB vm
          ** trange (sp + callee_param_cnt) (sp + (max_callee_params f)) (fun t => t = t_pro)
          ** stack_contents cs' retaddrs' (sp + (frame_size f)) (length (params f)) vm
    | _,_ => pure False
    end.   

  Fixpoint heap_contents (h:SourceMem.heap) (b:Z) vm : massert :=
    match h with
    | [] => pure True
    | (sz,af)::rest =>
        hasvalue b (val_of_Z (if af then sz + 1 else -(sz+1))) t_pro ** match_pub_sep vm (b+1) (b+1+sz)
          ** heap_contents rest (b+1+sz) vm
    end.


  Definition state_contents f sp retaddr retaddrs sB hp vm cs :=
    frame_contents f sp retaddr sB vm
      ** stack_contents cs retaddrs ((frame_size f) + sp) (length (params f)) vm
      ** trange sp (sp + (max_callee_params f)) (fun t => t = t_pro)
      ** match_pub_sep vm StkLimit sp
      ** heap_contents hp HpBase vm.

  Definition compile_from_retaddr callerf rd ret_site map :=
    let trs := transl_instrs map (val_of_Z (arr_ofs callerf)) ret_site in
    VCP (withdraw map RV rd :: trs ++ exit map callerf).

  Definition sp_good f sp : Prop :=
    StkLimit <= sp /\  sp + (frame_size f) + length(params f) <= StkBase.

  Inductive match_stacks p : RTLS.stack -> list mval -> Z -> nat -> Prop :=
  | match_stacks_nil:
    match_stacks p StkNil (* [VCP []] *) [Vint zero] StkBase O 
  | match_stacks_frame: forall rd f ret_site arb sB cs' sp retaddr retaddrs (callee_param_cnt:nat) map,
    forall
      (FF: RTL.lookup_function (RTL.f_id f) p = Some f)
      (SPG: sp_good f sp)
      (MAP: make_map f = OK map)
      (RAG: retaddr = compile_from_retaddr f rd ret_site map) 
      (MBase: arb = sp + (arr_ofs f))
      (Mrd: rd in_map map)
      (Mele: forall r, In r (regs_c ret_site) -> r in_map map)  (* maybe can be done differently *)
      (CMP: forall args f' rx', In (Icall f' args rx') ret_site -> length args <= (max_callee_params f)) (* ditto *)
      (PCNT: callee_param_cnt <= max_callee_params f)
      (MSTK: match_stacks p cs' retaddrs (sp + (frame_size f)) (length (params f))),
      match_stacks p (StkFrame rd f ret_site arb sB cs') (retaddr::retaddrs) sp callee_param_cnt.

  
  Definition match_sp s (sp:Z) := sp_of_stack s = sp. 

  Inductive match_stk_smem : RTLS.stack -> option RTL.function -> SourceMem.stack -> Prop :=
  | stk_smem_nil:  match_stk_smem StkNil None []
  | stk_smem_frame_none: forall cs' f rd ra arb sB s s',
      match_stk_smem cs' None s' ->
      s = (f,f.(sz_a))::s' -> 
      match_stk_smem (StkFrame rd f ra arb sB cs') None s
  | stk_smem_frame_some: forall cs s' s f, 
      match_stk_smem cs None s' ->
      s = (f,f.(sz_a))::s' -> 
      match_stk_smem cs (Some f) s.

  Inductive  match_builtin : RTL.builtin -> Mach.builtin -> Prop :=
  | mb_malloc : match_builtin RTL.Bmalloc Mach.Bmalloc
  | mb_free : match_builtin RTL.Bfree Mach.Bfree.

  Inductive match_vals: val -> mval -> Prop := 
  | match_vals_intro: forall v, match_vals v (Vint v).
  
  (* possibly this can/should be more refined *)
  Inductive match_failures: RTLS.failure -> MacS.failure -> Prop :=
  | match_failures_intro: forall rtlf macf, match_failures rtlf macf. (* for now *)
  

  Inductive match_states' p mv mf : RTLS.state (oracle p) -> MacS.state -> Prop :=
  | match_State : forall f pc arb sB sM cs tpc B M
                         map sp retaddr retaddrs, 
    forall
      (FF: RTL.lookup_function (RTL.f_id f) p = Some f)
      (MAP: make_map f = OK map)
      (SPG: sp_good f sp)
      (SPv: B#SP = Vint (val_of_Z sp))
      (MBase: arb = sp + (arr_ofs f)) 
      (Mpcs: tpc = transl_instrs map (val_of_Z (arr_ofs f)) pc ++ exit map f) 
      (MSP: match_sp (stk (proj1_sig sM)) sp)
      (MSM: match_stk_smem cs (Some f) (stk (proj1_sig sM)))
      (Mele: forall r, In r (regs_c pc) -> r in_map map)  (* maybe can be done differently *)
      (CMP: forall args f' rx', In (Icall f' args rx') pc -> length args <= (max_callee_params f)) (* ditto *)
      (STACK: match_stacks p cs (retaddr::retaddrs) ((frame_size f) + sp) (length (params f)))
      (HSP: heap_sizes_partition (hp (proj1_sig sM)))
      (SEP: M |= state_contents f sp retaddr retaddrs sB (hp (proj1_sig sM)) (vmem (proj1_sig sM)) cs),
      match_states' p mv mf (RTLS.State (oracle p) f pc arb sB sM cs)
        (MacS.State tpc B M)

  (* immediately after the jal, i.e. sp not changed and RA not saved.  *)
  | match_Callstate_f : forall f args sM cs tf B M sp retaddr retaddrs,
    forall
      (FF: RTL.lookup_function (RTL.f_id f)  p = Some f)
      (MFun: transl_function f = OK tf)
      (SPv: B # SP = Vint(val_of_Z sp))
      (SPG1: StkLimit <= sp)
      (SPG2 : sp + length (params f) <= StkBase)
      (RAv: B # RA = retaddr)
      (MSP: match_sp (stk (proj1_sig sM)) sp)
      (MSM: match_stk_smem cs None (stk (proj1_sig sM)))
      (STACK: match_stacks p cs (retaddr::retaddrs) sp (length (params f)))
      (ArgsL: length args = length (params f))
      (HSP: heap_sizes_partition (hp (proj1_sig sM)))
      (SEP:                              
        M |= stack_contents cs retaddrs sp (length (params f)) (vmem (proj1_sig sM))
          ** hasvalues sp (List.map (fun a => Vint a) args) t_pro  
          ** match_pub_sep (vmem (proj1_sig sM)) StkLimit sp
          ** heap_contents (hp (proj1_sig sM)) HpBase (vmem (proj1_sig sM))),
      match_states' p mv mf (Callstate (oracle p) (Func f) args sM cs)
        (State tf.(Mach.body) B M)

  (* calling built-in *)
  | match_Callstate_b : forall b mb args sM cs  B M sp retaddr retaddrs,
    forall
      (Mbuilt: match_builtin b mb)
      (SPv: B # SP = Vint(val_of_Z sp))
      (SPG1: StkLimit <= sp)
      (SPG2 : sp + (builtin_arity b)  <= StkBase)
      (RAv: B # RA = retaddr)
      (MSP: match_sp (stk (proj1_sig sM)) sp)
      (MSM: match_stk_smem cs None (stk (proj1_sig sM)))
      (STACK: match_stacks p cs (retaddr::retaddrs) sp (builtin_arity b))
      (ArgsL: length args = builtin_arity b)
      (HSP: heap_sizes_partition (hp (proj1_sig sM)))
      (SEP:                              
        M |= stack_contents cs retaddrs sp (builtin_arity b) (vmem (proj1_sig sM))
          ** hasvalues sp (List.map (fun a => Vint a) args) t_pro  
          ** match_pub_sep (vmem (proj1_sig sM)) StkLimit sp
          ** heap_contents (hp (proj1_sig sM)) HpBase (vmem (proj1_sig sM))),
      match_states' p mv mf (Callstate (oracle p) (Builtin b) args sM cs)
        (State [Mach.Mbuiltin mb] B M)
        
  (* after the sp and RA have been restored. *)
  | match_Returnstate : forall rv sM cs B M sp retaddr retaddrs,
    forall
      (SPv: B#SP = Vint (val_of_Z sp))
      (SPG1: StkLimit <= sp)
      (SPG2: sp <= StkBase)
      (RAv: B # RA = retaddr)
      (RVv: mv rv (B # RV))
      (MSP: match_sp (stk (proj1_sig sM)) sp)
      (MSM: match_stk_smem cs None (stk (proj1_sig sM)))
      (STACK: match_stacks p cs (retaddr::retaddrs) sp 0)
      (HSP: heap_sizes_partition (hp (proj1_sig sM)))
      (SEP: 
        M |= stack_contents cs retaddrs sp 0 (vmem (proj1_sig sM)) (* none valid now *) 
          ** match_pub_sep (vmem (proj1_sig sM)) StkLimit sp
          ** heap_contents (hp (proj1_sig sM)) HpBase (vmem (proj1_sig sM))),
      match_states' p mv mf (Returnstate (oracle p) rv sM cs)
        (State [] B M)

  | match_Failstop : forall err err',   
      mf err err' -> 
      match_states' p mv mf (RTLS.Failstop (oracle p) err)
        (MacS.Failstop err')

  . 


  Definition match_args_sep (sB:regbank) sp args :=
    hasvalues sp (List.map (fun r => Vint (sB # r)) args) t_pro. 

  End WithSmem.

  Inductive match_prog : RTL.program -> Mach.program -> Prop :=
  | mprog_nil : match_prog [] builtins
  | mprog_cons: forall f tf p tp 
                       (TF: transl_function f = OK tf)
                       (MP: match_prog p tp),
      match_prog (f :: p) (tf :: tp).


  Lemma match_lookup_function: forall prog tprog,
      match_prog prog tprog ->
      forall id f, RTL.lookup_function id prog = Some f ->
                   exists f', Mach.lookup_function id tprog = Some f' /\
                                transl_function f = OK f'. 
  Proof.
    induction prog; intros.
    - inv H. inv H0.
    - inv H. inv H0. 
      pose proof (transl_function_id _ _ TF). rewrite H in *.
      simpl. 
      destruct (Pos.eqb_spec id (f_id tf)). 
      + subst. inv H1.
        exists tf. intuition. 
      + eapply IHprog; eauto.
  Qed.  

  Lemma match_lookup_builtin: forall prog tprog,
      match_prog prog tprog ->
      forall id b, RTL.lookup_function id prog = None -> 
                   RTL.lookup_builtin id = Some b -> 
                   exists f' mb, lookup_function id tprog = Some f' /\
                                   f'.(body) = [Mbuiltin mb] /\
                                   match_builtin b mb.
  Proof.
    induction prog; intros.
    - inv H. 
      unfold lookup_builtin in H1. 
      unfold RTL.Bmalloc_id, RTL.Bfree_id in *. 
      destruct (Pos.eqb_spec id 1); subst. 
      * inv H1.  eexists; eexists; split; [|split]; simpl; eauto; try constructor. 
      * destruct (Pos.eqb_spec id 2); subst. 
        -- inv H1. eexists; eexists; split; [|split]; simpl; eauto; try constructor. 
        -- inv H1. 
    - assert (RTL.lookup_function id prog = None).
      { simpl in H0.  destruct (Pos.eqb_spec id (RTL.f_id a)); subst; try discriminate. auto. }
      assert (a.(RTL.f_id) <> id). 
      { simpl in H0.  destruct (Pos.eqb_spec id (RTL.f_id a)); subst; try discriminate. auto. }
      inv H. 
      destruct (IHprog _ MP _ _ H2 H1) as [f' [mb [P1 [P2 P3]]]]. 
      eexists; eexists; split; [|split]; eauto. 
      simpl. 
      destruct (Pos.eqb_spec id (f_id tf)); subst; eauto.
      exfalso. clear -TF H3.
      apply H3. 
      unfold transl_function in TF. monadInv TF. simpl.  auto.
  Qed.

End    Relations.

