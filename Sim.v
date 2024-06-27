(* Concrete C. *)

(* The refinement proofs, using step-by-step simulation. *)

Require Import Arith.
Require Import Lia.
Require Import Program.
Require Import Coq.Program.Program.
From Equations Require Import Equations.
Require Import NsatzTactic.
Require ssreflect.
Require Import Defns Mem Smallstep Behaviors.
Require Import RTL Mach.
Require Import Compiler. 
Require Import Matching.
Require Integers.
Require Import Errors.
Import Integers.Int64 ListNotations.
Require Import ListSet.
Import ssreflect. (* Using explicit direction arrows lets us recover ordinary rewrite. *)

(* Arthur's trick: https://stackoverflow.com/questions/63027162/abstraction-typing-error-resulting-from-case-eq-and-rewriting-in-coq  *)
Ltac monadInvDep H :=
  match type of H  with
  | (((match ?E as _ return _ with _ => _ end) _ = _)) => 
      revert H; 
      generalize (eq_refl E) ;
      case: {2 3} E ;
      intros;
      try discriminate
  end.

Module Proofs (Import mparams : MachParameters) (Import cparams: CompilerParameters).
  Module Import Invariants := Relations(mparams)(cparams).
  Import RTLS MacS Compiler.
  Import Separation.
  Import SourceMem.

  Section WithAssumptions.

    Variable maxFrameSizeBounded2:  maxFrameSize <= StkLimit - HpLimit.
    (* see comment at top of Compiler. *)
    Set Printing Coercions.

    Create HintDb DB.
    Hint Resolve writedown_hi_OK : DB.
    
    Remark SPv_unchanged : forall (B:mregbank) sp r v,
        r <> SP ->
        B # SP = sp ->
        (B # r <- v) # SP = sp.
    Proof ltac:(
                  intros; rewrite Regmap.gso; auto).
    Hint Resolve SPv_unchanged : DB.

    Remark distinct_sp1: SP <> GP1. Proof ltac:(inversion 1).
    Remark distinct_sp2: SP <> GP2. Proof ltac:(inversion 1).
    Remark distinct_sp3: SP <> GP3. Proof ltac:(inversion 1).
    Remark distinct_sp4: SP <> RA.  Proof ltac:(inversion 1). 
    Remark distinct_sp5: SP <> RV.  Proof ltac:(inversion 1). 
    Remark distinct_ra1: RA <> GP1. Proof ltac:(inversion 1).
    Remark distinct_ra2: RA <> GP2. Proof ltac:(inversion 1).
    Remark distinct_ra3: RA <> GP3. Proof ltac:(inversion 1).
    Remark distinct_rv1: RV <> GP1. Proof ltac:(inversion 1).
    Remark distinct_rv2: RV <> RA.  Proof ltac:(inversion 1).
    Remark distinct_12 : GP1<> GP2. Proof ltac:(inversion 1).
    Hint Resolve distinct_sp1 distinct_sp2 distinct_sp3 distinct_sp4 distinct_sp5
      distinct_ra1 distinct_ra2 distinct_ra3
      distinct_rv1 distinct_rv2 distinct_12: DB.

    
    Lemma accessible_in_bounds : forall sM a f sp 
                                        (SPG: sp_good f sp)
                                        (MSP: match_sp (stk (proj1_sig sM)) sp)
                                        (HSP: heap_sizes_partition (hp (proj1_sig sM))),
        accessible' sM a ->
        in_bounds a. 
    Proof with (eauto with DB; try (unfold_layout; lia')). 
      intros.
      unfold in_bounds. 
      unfold accessible', accessible in H.
      destruct H as [H|[H|H]].
      - unfold allocated in H. 
        destruct H as [[bs sz] [P1 P2]]. 
        inv MSP.
        inv SPG...
        rewrite in_app in P1.  destruct P1 as [P1|P1].
        +  assert (sp_bounded_below (stk (proj1_sig sM))).  { unfold sp_bounded_below; lia'. }
           pose proof (amap_of_stack_bounded_below _ H1 _ P1). simpl in H2. 
           pose proof (amap_of_stack_bounded_above _ _ P1). simpl in H3.
           unfold within in P2. simpl in P2... 
        + apply amap_of_heap'_bounds in P1. simpl in P1. unfold heap_sizes_partition in HSP.  unfold within in P2; simpl in P2...
      - unfold beyond_sp in H. 
        pose proof (sp_bounded_above (stk (proj1_sig sM)))...
      - destruct H as [r [P1 P2]].
        apply amap_of_heap'_bounds in P1. unfold heap_sizes_partition in HSP.  unfold within in P2; simpl in P2...
    Qed.


    (** Relating the separation matching predicates to SourceMem accessibility. *)

    Section OPAQUE_SEPCONJ.
      Local Opaque sepconj.
      
      Lemma frame_contents_pub:  forall p f sp retaddr sB M s vm P cs retaddrs h,
          forall
            (HSP: heap_sizes_partition h)
            (MSP: match_sp s sp)
            (MSM: match_stk_smem cs (Some f) s)
            (SPG: sp_good f sp)
            (MST: match_stacks p cs (retaddr::retaddrs) (sp + frame_size f) (length (params f))),
            M |= frame_contents f sp retaddr sB vm  ** P ->
            forall a, sp + max_callee_params f <= a < sp + frame_size f + length (params f) ->
                      if accessible_dec s h a then
                        M a = (Vint (vm a),t_unp)
                      else
                        snd (M a) = t_pro.
      Proof with (eauto; try (unfold_layout;lia')).   
        intros.
        unfold frame_contents, match_env_sep, match_locals_sep, match_params_sep in H.
        sepa_in H. 
        inv MSM. 
        inv MSP.
        inv SPG. 
        simpl in *. 
        set (s := (f,sz_a f)::s'). 
        destruct (accessible_dec s h a); simpl.
        - unfold accessible in a0.  destruct a0 as [H4|[H4|H4]].
          + unfold allocated in H4.
            destruct H4 as [[bs sz] [P1 P2]].
            apply in_app in P1.  
            unfold within in P2.  unfold s in P1. simpl in *. 
            destruct P1 as [P1|P1]. 
            * destruct P1. 
              -- inv H4. 
                 apply sep_swap4 in H.  apply sep_proj1 in H.  unfold match_pub_sep in H; simpl in H.  destruct (H a)...
              -- exfalso.
                 inv MST.
                 ++ inv H2. inv H4. 
                 ++ inv H2. assert (bs >= sp_of_stack ((f0,sz_a f0):: s'0) + max_callee_params f0). 
                    { simpl in H4. destruct H4. inv H2.
                      - simpl... 
                      - apply amap_of_stack_bounded_below in H2.
                        + simpl in H2. simpl...
                        + unfold sp_good in SPG. simpl in SPG. unfold sp_bounded_below... }
                    idtac...
            * exfalso.
              pose proof (amap_of_heap_bounded_above _ _ HSP P1). simpl in H4. 
              pose proof StkHp_disjoint...
          + exfalso. unfold beyond_sp in H4; unfold s in H4; simpl in H4... 
          + exfalso. unfold in_unallocated_hp in H4. destruct H4 as [[bs sz] [P1 P2]].
            unfold within in P2. pose proof (umap_of_heap_bounded_above _ _ HSP P1). simpl in *.
            pose proof StkHp_disjoint...
        - unfold accessible in n. destruct (Decidable.not_or _ _ n). clear n H5.
          unfold allocated, AllocatedStk in H4. 
          set (sp := sp_of_stack s).  unfold s in *; simpl in *. 
          destruct (Z_lt_dec a (sp + locals_ofs f + length (locals f))).
          + (* in locals *)
            apply sep_swap in H. apply sep_proj1 in H.
            eapply hasvalues_tag with (n := Z.to_nat(a - (sp + locals_ofs f)))  in H.
            rewrite <- H. f_equal. f_equal...  
            rewrite map_length... 
          + destruct (Z.eq_dec a (sp + ra_ofs f))...
            ++ (* is RA *)
              apply sep_swap3 in H. apply sep_proj1 in H. destruct H as [P1 [P2 P3]]. 
              subst. auto.
            ++ destruct (Z_lt_dec a (sp + params_ofs f))...
               +++ (* accessible *)
                 exfalso.
                 apply sep_swap4 in H.  apply sep_proj1 in H.  simpl in H. 
                 exploit (H a)...
                 unfold in_bounds...
                 intro.
                 apply H4. 
                 exists (sp + arr_ofs f, sz_a f). split...
                 unfold within; simpl...
               +++ (* in params *)
                 apply sep_proj1 in H. 
                 eapply hasvalues_tag with (n := Z.to_nat (a - (sp + params_ofs f))) in H. 
                 rewrite <- H. f_equal.  f_equal... 
                 rewrite map_length...
      Qed. 


      Lemma accessible_push:
        forall s h a f sp
               (MSP: match_sp ((f,sz_a f)::s) sp)
               (SPG1: StkLimit <= sp)
               (ABOVE: a >= sp_of_stack s), 
          accessible s h a <-> accessible ((f,sz_a f)::s) h a.
      Proof.
        intros.
        inv MSP. 
        simpl in SPG1. 
        unfold accessible; split; intros.
        - destruct H as [H|[H|H]].
          + left. unfold allocated in *.  destruct H as [r [P1 P2]].
            exists r. split; auto.
            rewrite in_app in P1; destruct P1.
            * rewrite in_app. left. simpl. right; auto.
            * rewrite in_app. right. auto.
          + unfold beyond_sp in H. unfold_layout; lia'. 
          + right; right; auto.
        - destruct H as [H|[H|H]].
          + destruct H as [r [P1 P2]].
            * rewrite in_app in P1. destruct P1. 
              -- simpl in H. destruct H. 
                 ++ destruct r as [bs sz]. inv H. unfold within in P2. simpl in P2. 
                    right; left. unfold beyond_sp.  unfold_layout; lia'. 
                 ++ left. unfold allocated. exists r.  split; auto. rewrite in_app. left.  auto.
              -- left.  unfold allocated.  exists r. split; auto.  rewrite in_app.  right; auto.
          + right; left. unfold beyond_sp in *.  simpl in H.  lia'. 
          + right; right; auto.
      Qed.

      Lemma stack_contents_pub:
        forall p cs sp retaddr retaddrs param_count M vm s P h
               (HSP: heap_sizes_partition h)
               (MSP: match_sp s sp)
               (MSM: match_stk_smem cs None s)
               (SPG1: StkLimit <= sp)
               (MST: match_stacks p cs (retaddr::retaddrs) sp param_count),
          M |= stack_contents cs retaddrs sp param_count vm  ** P -> 
          forall a, sp + param_count <= a < StkBase ->  
                    if accessible_dec s h a then
                      M a = (Vint (vm a),t_unp)
                    else
                      snd (M a) = t_pro.
      Proof with (eauto; try (unfold_layout;lia')).   
        induction cs; intros.
        - simpl in H. 
          inv MSM. 
          inv MSP.
          simpl in *. lia'. 
        - rename callers into f. simpl in H. 
          destruct retaddrs as [|retaddr' retaddrs']; [ rewrite sep_pure in H; intuition|].
          inv MSM. 
          inv MSP.  simpl in H0.
          set (sp' := sp_of_stack s'). 
          set (sp := sp' - frame_size f). 
          set (s := (f,sz_a f)::s'). 
          destruct (Z_lt_dec a (sp + max_callee_params f)).
          + (* in top frame unused callee-params *)
            destruct (accessible_dec s h a). 
            -- exfalso.
               unfold accessible in a0. destruct a0 as [H1|[H1|H1]].
               ++  unfold allocated in H1. 
                   destruct H1 as [[bs sz] [P1 P2]].
                   rewrite in_app in P1.
                   unfold within in P2; simpl in *.  
                   destruct P1 as [P1|P1].
                   ** assert (bs >= sp + max_callee_params f). 
                      { inv MST. subst s. (* inv P2. *)
                        destruct P1. 
                        - inv H1... 
                        - apply amap_of_stack_bounded_below in H1.
                          + simpl in H1...
                          + unfold sp_bounded_below... }
                      idtac...
                   ** pose proof (amap_of_heap_bounded_above _ _ HSP P1). simpl in H1. 
                      pose proof StkHp_disjoint...
               ++ unfold beyond_sp in H1. subst s. simpl in H1... 
               ++ unfold in_unallocated_hp in H1. destruct H1 as [[bs sz] [P1 P2]].
                  unfold within in P2. pose proof (umap_of_heap_bounded_above _ _ HSP P1). simpl in *.
                  pose proof StkHp_disjoint...
            -- sepa_in H. apply sep_swap in H. apply sep_proj1 in H. 
               eapply trange_tag in H... simpl... simpl...
          + destruct (Z_lt_dec a (sp' + length (params f))).
            * (* in top frame proper *)
              eapply frame_contents_pub.
              -- eauto.
              -- unfold match_sp. instantiate (1:= sp)...
              -- subst s. econstructor...
              -- unfold sp_good; split...
                 inv MST. inv MSTK; subst sp... unfold sp_good in SPG0. simpl in SPG0... 
              -- inv MST... 
              -- rewrite sep_assoc in H. eauto.
              -- simpl... 
            *  (* in some lower frame *)
              exploit (IHcs sp' retaddr' retaddrs' (length (params f))  M vm s' P). 
              -- eauto.
              -- unfold match_sp...
              -- auto.
              -- simpl in SPG1...
              -- inv MST... simpl in MSTK. 
                 replace (sp_of_stack s' - Z_of_nat (max_callee_params f + Datatypes.length (locals f) + 1 + sz_a f) +
                            Z_of_nat (frame_size f)) with (sp_of_stack s') in MSTK...  
              -- sepa_in H; do 2 apply sep_drop in H. simpl in H. subst sp'. 
                 replace (sp_of_stack s' - Z_of_nat (max_callee_params f + Datatypes.length (locals f) + 1 + sz_a f) +
                            Z_of_nat (frame_size f)) with (sp_of_stack s') in H...  
              -- instantiate (1:= a)... 
              -- intros.
                 exploit (accessible_push s' h a).  constructor.  eapply SPG1.  unfold_layout; lia'.  intro Q. 
                 destruct (accessible_dec s' h a); destruct (accessible_dec s h a); eauto. 
                 ++ exfalso. apply n1. subst s. rewrite <- Q. auto. 
                 ++ exfalso. apply n1. subst s. rewrite -> Q. auto.
      Qed.               

      Lemma heap_contents_pub0: forall h a b r afp vm P M
          (HSP : Z.of_nat (heap_size h) = HpLimit - b)
          (SEP : M |= heap_contents h b vm ** P),
          In r (amap_of_heap' afp b h) ->
          within r a -> 
          M a = (Vint (vm a), t_unp).
      Proof with  (eauto; try (unfold_layout;lia')).           
        induction h; intros.
        - inv H. 
        - rewrite amap_of_heap'_cons in H. 
          destruct r as [bs sz].
          destruct a as [sz0 b0]. simpl in H, H0. destruct H. 
          + destruct H. inv H.  simpl in SEP. 
            sepa_in SEP. apply sep_proj2 in SEP.  apply sep_proj1 in SEP. 
            unfold match_pub_sep in SEP; simpl in SEP. 
            unfold within in H0. 
            edestruct (SEP a0) as [_ Q]...  
          + simpl in SEP. rewrite heap_size_cons in HSP. simpl in HSP.
            sepa_in SEP.  apply sep_swap3 in SEP. eapply IHh... 
            replace (b + Z.pos (Pos.of_succ_nat sz0)) with (b + 1 + Z_of_nat sz0) in H by lia'... 
      Qed.


      Lemma heap_contents_pub1:forall h a b vm P M
          (HSP : Z.of_nat (heap_size h) = HpLimit - b)
          (SEP : M |= heap_contents h b vm ** P),
          b <= a < HpLimit ->                                      
          (forall r, In r (amap_of_heap' (fun _ => true) b h) -> ~ within r a) -> 
          snd (M a) = t_pro.
      Proof with (eauto; try (unfold_layout; lia')).
        induction h as [|o h]; intros.
        - simpl in HSP...
        - destruct o as [sz af].  
          destruct (Z.eq_dec a b). 
          + subst. simpl in SEP. sepa_in SEP. apply sep_proj1 in SEP. 
            unfold hasvalue in SEP. simpl in SEP. intuition. 
          + destruct (Z_lt_dec a (b + 1 + Z_of_nat sz)). 
            * exfalso. simpl in H0. pose proof (H0 (b+1,sz)). eapply H1.  left; auto. unfold within; simpl...
            * simpl in SEP. sepa_in SEP.  rewrite sep_swap3 in SEP.
              rewrite heap_size_cons in HSP. simpl in HSP. 
              eapply IHh... 
              intros. eapply H0. rewrite amap_of_heap'_cons. right. simpl. 
              replace (b + Z.pos (Pos.of_succ_nat sz)) with (b + 1 + Z_of_nat sz) by lia'... 
      Qed.

      Lemma heap_contents_pub: forall vm s sp M h P,
        forall
          (HSP: heap_sizes_partition h)
          (SEP: M |= heap_contents h HpBase vm ** P)
          (MSP: match_sp s sp)
          (SPG1: sp_bounded_below s),
        forall a, HpBase <= a < HpLimit -> 
                  if accessible_dec s h a then
                    M a = (Vint (vm a),t_unp)
                  else
                    snd (M a) = t_pro.
      Proof with  (eauto; try (unfold_layout;lia')).           
        intros.
        pose proof StkHp_disjoint as SHD.
        inv MSP.
        destruct (accessible_dec s h a); simpl. 
        - unfold accessible in a0.  destruct a0 as [H4|[H4|H4]].
          + unfold allocated in H4.
            destruct H4 as [[bs sz] [P1 P2]].
            apply in_app in P1.  
            destruct P1 as [P1|P1]. 
            * exfalso. unfold within in P2.  simpl in *. 
              apply amap_of_stack_bounded_below in P1...  simpl in P1. unfold sp_bounded_below in SPG1...
            * clear H. unfold amap_of_heap in P1.
              eapply heap_contents_pub0... 
          + unfold beyond_sp in H4...
          + unfold in_unallocated_hp in H4.
            destruct H4 as [[bs sz] [P1 P2]]. 
            eapply heap_contents_pub0...
        - eapply heap_contents_pub1... 
          intros. intro. apply n. 
          unfold accessible.
          apply amap_of_heap'_all in H0.  destruct H0. 
          + left. unfold allocated. exists r. intuition.
          + right; right. unfold in_unallocated_hp.  exists r.  intuition.
      Qed.

      Lemma state_contents_pub: forall p f sB s vm cs M h sp retaddr retaddrs, 
        forall
          (HSP: heap_sizes_partition h)
          (SPG: sp_good f sp)
          (MSP: match_sp s sp)
          (MSM: match_stk_smem cs (Some f) s)
          (STACK: match_stacks p cs (retaddr::retaddrs) ((frame_size f) + sp) (length (params f)))
          (SEP: M |= state_contents f sp retaddr retaddrs sB h vm cs),
        forall a, in_bounds a ->
                  if accessible_dec s h a then
                    M a = (Vint (vm a),t_unp)
                  else
                    snd (M a) = t_pro.
      Proof with  (eauto; try (unfold_layout;lia')).           
        intros.
        unfold in_bounds in H.  
        destruct H. 
        2: {
          eapply heap_contents_pub... 
          unfold state_contents in SEP. sep_swap_end_in SEP.  eauto.
          unfold sp_good in SPG. unfold sp_bounded_below. inv MSP...
        }
        destruct( Z_lt_dec a sp);
          [|destruct (Z_lt_dec a (sp + max_callee_params f));[|destruct (Z_lt_dec a (sp + frame_size f + length (params f)))]].
        - (* StkLimit <= a < sp *)
          do 3 apply sep_drop in SEP.  apply sep_proj1 in SEP. simpl in SEP.
          exploit (SEP a)...
          intros [P1 P2]. 
          destruct (accessible_dec s h a)...
          unfold accessible in n. 
          exfalso. apply n. right. inv SPG. inv MSP. unfold beyond_sp...
        - (* sp <= a < sp + max_callee_params f *)
          apply sep_swap3 in SEP. apply sep_proj1 in SEP. simpl in SEP.
          destruct (SEP a) as [P1 P2]...
          destruct (accessible_dec s h a)...
          exfalso.
          unfold accessible in a0. destruct a0 as [H0| [H0|H0]].
          + unfold allocated in H0. destruct H0 as [[bs sz] [Q1 Q2]].
            apply in_app in Q1. destruct Q1 as [Q1|Q1]. 
            * assert (bs >= sp + max_callee_params f). 
              { inv MSM. inv MSP. simpl in Q1.  destruct Q1. 
                - inv H0. simpl... 
                - apply amap_of_stack_bounded_below in H0.
                  + simpl in *...
                  + inv SPG. simpl in H2. unfold sp_bounded_below... }
              unfold within in Q2; simpl in Q2...
            * apply amap_of_heap_bounded_above in Q1... unfold within in Q2; simpl in *; pose proof StkHp_disjoint...
          + unfold beyond_sp in H0. inv MSM. inv MSP... 
          + destruct H0 as [[bs sz] [Q1 Q2]]... apply umap_of_heap_bounded_above in Q1... unfold within in Q2; simpl in *;
              pose proof StkHp_disjoint... 
        - (* sp + max_callee_params f <= a < sp + frame_size f + length (params f) *)
          eapply frame_contents_pub...
          rewrite Z.add_comm...
        - (* sp + frame_size f + length (params f) <= a < StkBase *)
          apply sep_swap in SEP. 
          inv SPG. inv MSP. inv MSM. 
          replace (frame_size f + sp_of_stack ((f,sz_a f) :: s')) with (sp_of_stack s') in *.
          simpl in n, n0, n1. 
          2: simpl...
          exploit (stack_contents_pub p cs (sp_of_stack s')  retaddr retaddrs (length (params f)) M vm s')...
          + unfold match_sp...
          + simpl in H0...
          + instantiate (1:= a)...
          + intro. 
            destruct (accessible_dec s' h a); destruct (accessible_dec ((f,sz_a f)::s') h a); auto... 
            * exfalso; apply n2. erewrite <- accessible_push; unfold match_sp; auto... 
            * exfalso; apply n2. erewrite -> accessible_push; unfold match_sp; auto... 
      Qed.

    End OPAQUE_SEPCONJ.

    
    (**  Characterizing hi privilege updates and loads. *)

    Lemma replace_one: forall rs n r v sB, 
        locate r rs = Some n ->
        NoDup rs -> 
        replace (map (fun r0 => Vint (sB # r0)) rs) n (Vint v) = map (fun r0 => Vint(sB # r <- v) # r0) rs.
    Proof.
      induction rs; intros. 
      - inv H. 
      - apply NoDup_cons_iff in H0.
        simpl in *. destruct (Pos.eqb_spec r a). 
        + subst. inv H. 
          unfold replace. simpl.
          rewrite Regmap.gss. 
          f_equal. 
          apply list_map_exten. 
          intros. 
          rewrite -> Regmap.gso. auto. intro.  subst. intuition. 
        + destruct (locate r rs) eqn:?; inv H. 
          unfold replace. simpl. 
          rewrite Regmap.gso; try lia'. 
          f_equal. 
          erewrite <- IHrs; eauto; try intuition.    
    Qed. 

    Lemma match_env_sep_hi_update : forall f sB sp P m v M r,
        M |= match_env_sep f sB sp ** P ->
        make_map f = OK m -> 
        r in_map m -> 
        let M' := updm t_pro M (sp+m@r) (Vint v) in
        writedown hi t_pro M (sp + m @ r) (Vint v) = Normal M'  /\
          M' |= match_env_sep f (sB # r <- v) sp ** P.
    Proof.
      intros. 
      subst M'. 
      edestruct in_map_exists as [ofs E]; eauto. 
      assert (F: m @ r = ofs) by (unfold getofs; rewrite ->  E; auto).  
      rewrite ->  F. 
      erewrite ->  reg_slot_map in F; eauto. 
      unfold reg_slot in F. 
      unfold match_env_sep in H|-*. 
      destruct (locate r (params f)) eqn:?.
      - rewrite ->  sep_assoc in H. 
        unfold match_params_sep in H. 
        eapply writedown_rule_vs with (priv := hi) (n := n) (mv := Vint v) in H. 
        2: constructor.
        2: {  eapply nth_error_Some. intro. 
              apply locate_nth_error in Heqo.  eapply map_nth_error in Heqo. 
              rewrite ->  Heqo in H2.  inv H2.  }
        destruct H as [P1 P2].
        rewrite <- F. 
        rewrite ->  Z.add_assoc.  
        split; auto. 
        rewrite ->  sep_assoc. 
        eapply sep_imp; eauto. 
        + erewrite ->  replace_one; eauto. 
          apply massert_imp_refl. 
          apply (params_NoDup f). 
        +  unfold match_locals_sep.
           assert (map (fun r0 => Vint ((sB # r <- v) #r0)) (locals f) =
                     map (fun r0 => Vint (sB #r0)) (locals f)). 
           { apply list_map_exten. intros.
             rewrite ->  Regmap.gso; auto. intro. subst. apply locate_nth_error in Heqo. apply nth_error_In in Heqo.
             eapply locals_params_disjoint; eauto. }
           rewrite ->  H. apply massert_imp_refl.
      - destruct (locate r (locals f)) eqn:?; [| lia'] . 
        rewrite ->  sep_assoc in H. 
        rewrite ->  sep_swap in H. 
        unfold match_locals_sep in H. 
        eapply writedown_rule_vs with (priv := hi) (n:= n) (mv := Vint v) in H. 
        2: constructor.
        2: {  eapply nth_error_Some. intro. 
              apply locate_nth_error in Heqo0.  eapply map_nth_error in Heqo0. 
              rewrite ->  Heqo0 in H2.  inv H2.  }
        destruct H as [P1 P2].
        rewrite <- F. 
        rewrite ->  Z.add_assoc. 
        split; auto. 
        rewrite ->  sep_assoc. 
        rewrite ->  sep_swap.
        eapply sep_imp; eauto. 
        + unfold match_locals_sep.
          erewrite ->  replace_one; eauto. 
          apply massert_imp_refl. 
          apply locals_NoDup.
        + unfold match_params_sep.
          assert (map (fun r0 => Vint ((sB # r <- v) #r0)) (params f) = 
                    map (fun r0 => Vint (sB #r0)) (params f)). 
          { apply list_map_exten. intros.
            rewrite ->  Regmap.gso; auto. intro. subst. apply locate_nth_error in Heqo0.
            apply nth_error_In in Heqo0. eapply locals_params_disjoint; eauto. } 
          rewrite ->  H. apply massert_imp_refl.
    Qed.


    Lemma frame_contents_hi_update : forall f sB sp retaddr P m v M r vm,
        M |= frame_contents f sp retaddr sB vm ** P -> 
        make_map f = OK m -> 
        r in_map m -> 
        let M' := updm t_pro M (sp+m@r) (Vint v) in
        writedown hi t_pro M (sp + m@r) (Vint v) = Normal M' /\
          M' |= frame_contents f sp retaddr (sB # r <- v) vm ** P.
    Proof.
      intros.
      unfold frame_contents in *.  
      rewrite sep_assoc in H. 
      eapply match_env_sep_hi_update in H; eauto. 
      destruct H as [Q R].
      split; eauto.
      rewrite sep_assoc.  eauto.
    Qed.

    
    Lemma match_env_sep_load: forall f sp sB r m M, 
        M |= match_env_sep f sB sp -> 
        make_map f = OK m -> 
        r in_map m -> 
        lookup hi M (sp+m@r) = Normal (Vint(sB # r)).
    Proof.
      intros.
      edestruct in_map_exists as [ofs E]; eauto. 
      assert (F: m @ r = ofs) by (unfold getofs; rewrite E; auto).  
      rewrite F. 
      erewrite reg_slot_map in F; eauto. 
      unfold reg_slot in F. 
      unfold match_env_sep in H.
      destruct (locate r (params f)) eqn:?.
      - apply sep_proj1 in H.
        unfold match_params_sep in H.
        simpl in H. 
        rewrite <- F. rewrite Z.add_assoc. 
        apply locate_nth_error in Heqo. 
        eapply lookup_rule_vs; eauto. 
        + constructor. 
        + erewrite map_nth_error; eauto.
      - destruct (locate r (locals f)) eqn:?; [|lia']. 
        apply sep_proj2 in H.
        unfold match_locals_sep in H. 
        simpl in H. 
        rewrite <- F.  rewrite Z.add_assoc.
        apply locate_nth_error in Heqo0. 
        eapply lookup_rule_vs; eauto. 
        + constructor. 
        + erewrite map_nth_error; eauto.
    Qed.

    Lemma frame_contents_sep_load: forall f sp retaddr sB M m r vm P,
        M |= frame_contents f sp retaddr sB vm ** P -> 
        make_map f = OK m -> 
        r in_map m -> 
        lookup hi M (sp+m@r) = Normal (Vint(sB # r)).
    Proof.
      intros.
      unfold frame_contents in H.  
      apply sep_proj1 in H.  apply sep_proj1 in H. 
      eapply match_env_sep_load; eauto.
    Qed.


    (** Characterizing lo privilege updates and loads. *)

    Lemma match_pub_sep_footprints: forall vm l h vm',
        incl_footprint
          (match_pub_sep vm l h) 
          (match_pub_sep vm' l h). 
    Proof.
      intros.
      unfold incl_footprint; simpl; auto.
    Qed.


    Lemma frame_contents_footprints: forall f sp retaddr sB vm vm',
        incl_footprint
          (frame_contents f sp retaddr sB vm)
          (frame_contents f sp retaddr sB vm').
    Proof.
      intros.
      unfold incl_footprint; simpl; auto.
    Qed.


    Lemma stack_contents_footprints : forall cs retaddrs sp args_size vm vm',
        incl_footprint 
          (stack_contents cs retaddrs sp args_size vm)
          (stack_contents cs retaddrs sp args_size vm').
    Proof.
      unfold incl_footprint.
      induction cs; intros.
      - simpl in *. auto.
      - simpl in *. 
        destruct retaddrs.
        + auto.
        + unfold m_footprint. simpl in *. 
          destruct H; [left; auto| right].
          destruct H; [left; auto| right].
          eauto.
    Qed.


    Lemma heap_contents_footprints : forall h b vm vm', 
        incl_footprint 
          (heap_contents h b vm) 
          (heap_contents h b vm').
    Proof.
      unfold incl_footprint.
      induction h; intros.
      - simpl in *. auto.
      - simpl in *. 
        destruct a as [sz af]. 
        unfold m_footprint in H|-*; simpl in H|-*. 
        destruct H; [left; auto|right]. 
        destruct H; [left; auto|right]. 
        eauto.
    Qed.        

    Hint Resolve match_pub_sep_footprints
      frame_contents_footprints
      stack_contents_footprints
      heap_contents_footprints
      incl_footprint_refl 
      sep_incl_footprint : DB. 

    Lemma frame_contents_lo_update:
      forall M f sp retaddr sB a v M' vm
             (MFrm: M |= frame_contents f sp retaddr sB vm)
             (WLo: writedown lo t_unp M a (Vint v) = Normal M'),
        M' |= frame_contents f sp retaddr sB (updvm vm a v). 
    Proof with (auto with DB).
      intros. 
      unfold frame_contents in *. 
      unfold match_env_sep in *. eapply sep_assoc. rewrite sep_assoc in MFrm. 
      sep_swap_end.
      sep_swap_end_in MFrm.
      eapply sep_preserved_footprint; eauto; intros; clear MFrm... 
      - simpl in *. intros.
        unfold writedown in WLo.
        destruct (M a) as (v0,sec). machMonadInv WLo. 
        unfold updm, updvm. 
        destruct (H a0 H0). split; auto. 
        destruct (Z.eq_dec a a0).
        + subst. rewrite Z.eqb_refl; auto.
        + rewrite <- Z.eqb_neq in n. rewrite n. auto. 
      - eapply sep_preserved; eauto; intros.
        + unfold match_params_sep in *. 
          eapply writedown_unchanged_vs; eauto. intro. inv H1. 
        + eapply sep_preserved; eauto; intros.
          * unfold match_locals_sep in *. 
            eapply writedown_unchanged_vs; eauto. intro. inv H2. 
          * eapply writedown_unchanged_v; eauto. intros. subst.  intro.  inv H2. 
    Qed.


    Lemma stack_contents_lo_update:
      forall p cs sp M args_size retaddr retaddrs param_cnt (a:Z) v M' vm
             (STACK: match_stacks p cs (retaddr::retaddrs) sp param_cnt)
             (SEP: M |= stack_contents cs retaddrs sp args_size vm)
             (WLo: writedown lo t_unp M a (Vint v) = Normal M'),
        M' |= stack_contents cs retaddrs sp args_size (updvm vm a v). 
    Proof with (eauto with DB). 
      induction cs; intros. 
      - auto.
      - simpl in SEP|-*. 
        destruct retaddrs; [inv SEP|]. 
        inv STACK.
        eapply sep_preserved_footprint; eauto; intros; clear SEP... 
        + eapply frame_contents_lo_update... 
        + eapply sep_preserved_footprint; eauto; intros; clear H... 
          eapply writedown_unchanged_trange; eauto.
          left. intros. subst. intro X; inv X.  
    Qed.          

    Lemma pub_sep_lo_update: forall M vm l h a v M'
                                    (WLo : writedown lo t_unp M a (Vint v) = Normal M'),
        M |= match_pub_sep vm l h ->
        M' |= match_pub_sep (updvm vm a v) l h.
    Proof.
      intros.
      unfold match_pub_sep in H|-*; simpl in H|-*; intros. 
      unfold writedown in WLo. destruct (M a).
      machMonadInv WLo. destruct (H a0); auto.
      split; auto. 
      destruct (Z.eq_dec a a0).
      ** subst. rewrite mupdate_gss. rewrite updvm_same; auto.
      ** rewrite mupdate_gso; auto. rewrite updvm_other; auto.
    Qed.

    Lemma heap_contents_lo_update:
      forall h b vm M (a:Z) v M'
             (HSP: Z.of_nat (heap_size h) = HpLimit - b)
             (SEP: M |= heap_contents h b vm)
             (WLo: writedown lo t_unp M a (Vint v) = Normal M'),
        M' |= heap_contents h b (updvm vm a v).
    Proof with (eauto with DB; try (unfold_layout; lia')). 
      induction h; intros.
      - auto.
      - simpl in SEP|-*. 
        destruct a as [sf af]. 
        rewrite heap_size_cons in HSP; simpl in HSP.
        eapply sep_preserved_footprint; eauto; intros; clear SEP... 
        + eapply writedown_unchanged; eauto. intros. subst t'. intro. inv H0.
        + eapply sep_preserved_footprint; eauto; intros; clear H... 
          * eapply pub_sep_lo_update...
          * eapply IHh...
    Qed.


    Lemma state_contents_lo_update:
      forall p f sB sM cs M a sM' v sp retaddr retaddrs 
             (HSP: heap_sizes_partition (hp (proj1_sig sM)))
             (SM: store' sM a v = Some sM')
             (SEP : M |= state_contents f sp retaddr retaddrs sB (hp (proj1_sig sM)) (vmem (proj1_sig sM)) cs)
             (SPG: sp_good f sp)
             (MSP: match_sp (stk (proj1_sig sM)) sp)
             (MSM: match_stk_smem cs (Some f) (stk (proj1_sig sM)))
             (STACK: match_stacks p cs (retaddr::retaddrs) ((frame_size f) + sp) (length (params f))),
        let M' := updm t_unp M a (Vint v) in 
        writedown lo t_unp M a (Vint v) = Normal M' /\
          M' |= state_contents f sp retaddr retaddrs sB (hp (proj1_sig sM')) (vmem (proj1_sig sM')) cs.
    Proof with (eauto with DB). 
      intros. unfold state_contents in SEP|-*.
      pose proof StkHp_disjoint as SHD.
      unfold store' in SM. 
      maybeMonadInv SM. 
      assert (INB: in_bounds a) by (eapply accessible_in_bounds; eauto).
      assert (WLo: writedown lo t_unp M a (Vint v) = Normal M').
      { unfold writedown. destruct (M a) as [v0 sec0] eqn:?. 
        pose proof (state_contents_pub _ _ _ _ _ _ _ _ _ _ _ HSP SPG MSP MSM STACK SEP a INB).
        unfold accessible_dec' in Heqs. rewrite Heqs in H.  simpl in H. rewrite Heqp0 in H. inv H. 
        rewrite in_bounds_access in INB. rewrite INB; simpl; auto. }
      split...
      simpl proj1_sig. simpl vmem. simpl hp. 
      eapply sep_preserved_footprint; eauto; intros; clear SEP... 
      + eapply frame_contents_lo_update... 
      + eapply sep_preserved_footprint; eauto; intros; clear H...
        * eapply stack_contents_lo_update...
        * eapply sep_preserved_footprint; eauto; intros; clear H0... 
          -- eapply writedown_unchanged_trange... 
             left; intros. subst t'. intro X; inv X. 
          -- eapply sep_preserved_footprint; eauto; intros; clear H... 
             ++ eapply pub_sep_lo_update... 
             ++ eapply heap_contents_lo_update...
    Qed.


    Lemma state_contents_lo_update_fail:
      forall p f sB sM cs M a  v sp retaddr retaddrs 
             (SEP : M |= state_contents f sp retaddr retaddrs sB (hp (proj1_sig sM)) (vmem (proj1_sig sM)) cs)
             (HSP: heap_sizes_partition (hp (proj1_sig sM)))
             (SPG: sp_good f sp)
             (MSP: match_sp (stk (proj1_sig sM)) sp)
             (MSM: match_stk_smem cs (Some f) (stk (proj1_sig sM)))
             (STACK: match_stacks p cs (retaddr::retaddrs) ((frame_size f) + sp) (length (params f)))
             (SM: store' sM a v = None),
      exists c, writedown lo t_unp M a (Vint v) = Failure c. 
    Proof with (eauto with DB; try (unfold_layout; lia')). 
      intros.
      unfold store' in SM. unfold accessible_dec' in SM. 
      unfold writedown. 
      assert (INB: in_bounds a \/ ~ in_bounds a). 
      { unfold in_bounds... } 
      destruct INB as [INB|INB]. 
      - pose proof (state_contents_pub _ _ _ _ _ _ _ _ _ _ _ HSP SPG MSP MSM STACK SEP a INB).
        destruct (M a) as [v0 t0].
        destruct (accessible_dec (stk (proj1_sig sM)) (hp (proj1_sig sM)) a); try inv SM.  
        simpl in H. subst t0. rewrite in_bounds_access in INB. rewrite INB. simpl. 
        eexists. unfold e_msg...
      - rewrite in_bounds_access in INB.  destruct (access_in_bounds a) eqn:?; try (exfalso; apply INB; auto; fail). 
        destruct (M a) as [v0 t0]. simpl.
        eexists. unfold e_msg...
    Qed.        


    Lemma state_contents_lo_lookup:
      forall p f sB sM cs M a  sp retaddr retaddrs 
             (SEP : M |= state_contents f sp retaddr retaddrs sB (hp (proj1_sig sM)) (vmem (proj1_sig sM)) cs)
             (HSP: heap_sizes_partition (hp (proj1_sig sM)))
             (SPG: sp_good f sp)
             (MSP: match_sp (stk (proj1_sig sM)) sp)
             (MSM: match_stk_smem cs (Some f) (stk (proj1_sig sM)))
             (STACK: match_stacks p cs (retaddr::retaddrs) ((frame_size f) + sp) (length (params f)))
             (ACC: accessible' sM a), 
        lookup lo M a = Normal (Vint ((proj1_sig sM).(vmem) a)). 
    Proof with (eauto with DB; try (unfold_layout; lia')). 
      intros.
      exploit accessible_in_bounds; eauto. intro INB. 
      pose proof (state_contents_pub _ _ _ _ _ _ _ _ _ _ _ HSP SPG MSP MSM STACK SEP a INB).
      unfold lookup.
      destruct (M a) as [v0 t0].
      unfold accessible' in ACC. 
      destruct (accessible_dec (stk (proj1_sig sM)) (hp (proj1_sig sM)) a); try contradiction. 
      inv H.
      rewrite in_bounds_access in INB. rewrite INB. simpl...
    Qed.

    Lemma state_contents_lo_lookup_fail:
      forall p f sB sM cs M a  sp retaddr retaddrs 
             (SEP : M |= state_contents f sp retaddr retaddrs sB (hp (proj1_sig sM)) (vmem (proj1_sig sM)) cs)
             (HSP: heap_sizes_partition (hp (proj1_sig sM)))
             (SPG: sp_good f sp)
             (MSP: match_sp (stk (proj1_sig sM)) sp)
             (MSM: match_stk_smem cs (Some f) (stk (proj1_sig sM)))
             (STACK: match_stacks p cs (retaddr::retaddrs) ((frame_size f) + sp) (length (params f)))
             (ACC: ~ accessible' sM a), 
      exists c, lookup lo M a = Failure c.
    Proof with (eauto with DB; try (unfold_layout; lia')). 
      intros.
      unfold lookup. 
      unfold accessible' in ACC.
      assert (INB: in_bounds a \/ ~ in_bounds a). 
      { unfold in_bounds... } 
      destruct INB as [INB|INB]. 
      - pose proof (state_contents_pub _ _ _ _ _ _ _ _ _ _ _ HSP SPG MSP MSM STACK SEP a INB).
        destruct (M a) as [v0 t0].
        destruct (accessible_dec (stk (proj1_sig sM)) (hp (proj1_sig sM)) a); try contradiction. 
        simpl in H. subst t0. rewrite in_bounds_access in INB. rewrite INB. simpl. 
        eexists. unfold e_msg...
      - rewrite in_bounds_access in INB.  destruct (access_in_bounds a) eqn:?; try (exfalso; apply INB; auto; fail). 
        destruct (M a) as [v0 t0]. simpl.
        eexists. unfold e_msg...
    Qed.        


    (** Justifying arithmetic *)

    Lemma offset_arith_ok': forall f ofs sp
        (SPG: sp_good f sp),
        0 <= ofs <= frame_size f + length (params f) -> 
        unsigned (add (val_of_Z ofs) (val_of_Z sp)) = sp + ofs. 
    Proof.
      intros.
      destruct SPG as [P1 P2].  
      pose proof StkBase_WF. 
      pose proof StkLimit_WF.
      rewrite <- repr_distr_add.
      rewrite -> unsigned_repr; try lia'. 
    Qed.

    Lemma offset_arith_ok: forall r f map sp
          (RIN: r in_map map)
          (MAP: make_map f = OK map)
          (SPG: sp_good f sp),
        unsigned (add (val_of_Z map @ r) (val_of_Z sp)) = sp + map @ r.
    Proof.
      intros.
      eapply offset_arith_ok'; eauto. 
      pose proof (reg_slot_map _ _ MAP r). 
      edestruct in_map_exists as [n Q]; eauto.
      unfold reg_slot in H.
      destruct (locate r (params f)) eqn:?. 
      - apply locate_bound in Heqo. 
        unfold_layout; lia'. 
      - destruct (locate r (locals f)) eqn:?; try lia'. 
        apply locate_bound in Heqo0. 
        unfold_layout; lia'. 
    Qed.


    Lemma init_regs_local : forall (f:RTL.function) args r,
        In r (RTL.locals f) -> 
        (init_regs (params f) args) # r = NULL. 
    Proof.
      intros.
      remember (params f) as xs. 
      assert (forall x, In x xs -> In x (params f)).
      { intro; subst; auto. }
      clear Heqxs.
      revert args. 
      generalize dependent xs. 
      induction xs; intros.
      - simpl; apply Regmap.gi.  
      - destruct args eqn:?. 
        + simpl; apply Regmap.gi.
        + simpl. 
          rewrite ->  Regmap.gso.
          eapply IHxs. 
          intros. eapply H0. right; auto.
          intro.
          subst r. 
          eapply locals_params_disjoint; eauto.
          eapply H0.  left; auto.
    Qed.
    
    Lemma init_regs_locals : forall f args,
        map (fun r0 : positive => Vint (init_regs (params f) args) # r0) (locals f) = repeat (Vint NULL) (length (locals f)). 
    Proof.
      intros.
      remember (locals f) as xs.
      assert (forall x, In x xs -> In x (locals f)). 
      {  intro; subst; auto.  }
      clear Heqxs. 
      revert args.
      generalize dependent xs. 
      induction xs; intros; simpl.
      - auto.
      - simpl. f_equal.
        f_equal.
        * eapply init_regs_local; eauto.
          eapply H; left; auto.
        * eapply IHxs.
          intros. eapply H; right; auto.
    Qed.
    
    Lemma init_regs_params: forall f args,
        length args = length (params f) ->
        map (fun r0 : positive => Vint (init_regs (params f) args) # r0) (params f) = map (fun a : val => Vint a) args. 
    Proof.
      intros.
      remember (params f) as xs.
      assert (forall x, In x xs -> In x (params f)).
      { intro; subst; auto. }
      assert (NoDup xs).
      { subst; apply f.(params_NoDup); auto.  }
      clear Heqxs.
      generalize dependent args.
      generalize dependent xs. 
      induction xs; intros; simpl. 
      - destruct args; auto. inv H. 
      - destruct args; simpl. inv H. 
        inv H. 
        rewrite Regmap.gss.
        f_equal.
        rewrite <- IHxs; eauto. 
        2 : intros; eapply H0; right; auto. 
        2 :  inv H1; auto. 
        eapply list_map_exten.
        intros. 
        f_equal.
        erewrite Regmap.gso; auto.
        intro.
        inv H1. contradiction.
    Qed.


    (** Correctness of parameter pushing code. *)

    Lemma pp_rec_correct: forall args (ofs:nat) sp B M sB f m instrs tge P
                                 (SPG: sp_good f sp)
                                 (MAP: make_map f = OK m)
                                 (ARGS_IN: forall r, In r args -> r in_map m)
                                 (SPv: B#SP = Vint (val_of_Z sp))
                                 (OFSG: ofs + length args <= max_callee_params f),
        M |= trange (sp + ofs) (sp + max_callee_params f) (fun t : Tag => t = t_pro) **
          match_env_sep f sB sp ** P -> 
        exists B' M',
          Smallstep.star step tge (State (pp_rec m ofs args ++ instrs) B M) 
            (State instrs B' M') /\ 
            B#SP = B'#SP /\
            M' |= match_args_sep sB (sp + ofs) args **
              trange (sp + ofs + length args) (sp + max_callee_params f) (fun t : Tag => t = t_pro) **
              match_env_sep f sB sp ** P. 
    Proof with (eauto with DB; try lia').
      Opaque sepconj.
      unfold match_args_sep. 
      induction args as [|a args' IHargs]; intros.
      - simpl.
        exists B, M; split; [|split]; auto.
        + simpl; constructor. 
        + rewrite sep_pure. rewrite Z.add_0_r. intuition. 
      - simpl.
        assert (a in_map m). { intros. eapply ARGS_IN. left; auto. }
        simpl in OFSG. 
        erewrite <- trange_eqv with (mid := (sp + S ofs)) in H... sepa_in H. 
        apply sep_comm in H. rewrite sep_assoc in H.  rewrite sep_assoc in H.  
        edestruct IHargs with (sp := sp) (ofs := S ofs) as [B' [M' [P1 [P2 P3]]]]... 
        { intros. eapply ARGS_IN. right; auto. }
        edestruct writedown_rule_v with (m := M') (a:= sp + ofs) as [R1 R2].
        { replace (sp + (1 + ofs)) with (sp + ofs + 1) in P3 by lia'.
          replace (sp + (S ofs)) with (sp + ofs + 1) in P3 by lia'. 
          rewrite trange_contains_imp in P3.
          sep_swap_end_in P3.  eapply P3.  }
        { intros. simpl in H1.  subst. constructor. }
        rewrite P2 in SPv. 
        eexists. eexists. split; [|split]. 
        + eapply star_trans.
          rewrite <- app_assoc. eapply P1. 
          eapply star_two.
          * (* 1st step - deposit *)
            eapply step_Mload...
            -- unfold lea. simpl.  rewrite SPv... 
            -- erewrite offset_arith_ok... 
               apply sep_pick3 in P3. eapply match_env_sep_load... 
          * (* 2nd step - Store *)
            eapply step_Mstore...
            -- unfold lea... simpl. rewrite Regmap.gso... rewrite SPv... 
            -- rewrite Regmap.gss...
               erewrite offset_arith_ok'...
               simpl in OFSG; unfold_layout; lia'.  
        + rewrite Regmap.gso...
        + replace (sp + ofs + Z.pos (Pos.of_succ_nat (length args'))) with (sp + ofs + 1 + length args') by lia'...
          sepa...
    Transparent sepconj.             
    Qed.

    Lemma push_params_correct: forall args sp B M sB f m instrs tge P
                                      (SPG: sp_good f sp)
                                      (MAP: make_map f = OK m)
                                      (ARGS_IN: forall r, In r args -> r in_map m)
                                      (SPv: B#SP = Vint (val_of_Z sp))
                                      (OFSG: length args <= max_callee_params f),
        M |= trange sp (sp + max_callee_params f) (fun t : Tag => t = t_pro)
          ** match_env_sep f sB sp ** P ->
        exists B' M',
          Smallstep.star step tge (State (push_params m args ++ instrs) B M) 
            (State instrs B' M') /\ 
            B#SP = B'#SP /\
            M' |= match_args_sep sB sp args **
              trange (sp + length args) (sp + max_callee_params f) (fun t : Tag => t = t_pro)
              ** match_env_sep f sB sp ** P.
    Proof with (eauto with DB).
      intros.
      unfold push_params. 
      setoid_replace sp with (sp + O) at 1 2 by (rewrite Z.add_0_r; reflexivity).
      eapply pp_rec_correct...  
      rewrite Z.add_0_r.
      auto.
    Qed.
    
    (** Correctness of stack tagging code. *)

    Lemma stk_tag_correct: forall (cnt ofs:nat) sp B M f instrs tag tge P gp1v tspec 
                                  (SPG: sp_good f sp)
                                  (SPv: B#SP = Vint (val_of_Z sp))
                                  (OFSG: ofs + cnt <= frame_size f)
                                  (GP1VAL: B#GP1 = gp1v),
        M |= trange (sp + ofs) (sp + ofs + cnt) tspec ** P ->
        exists M',
          Smallstep.star step tge (State (stk_tag tag ofs cnt ++ instrs) B M) 
            (State instrs B M') /\ 
            M' |= hasvalues (sp + ofs) (repeat gp1v cnt) tag ** P .
    Proof with (eauto with DB; try lia').
      Opaque sepconj.
      induction cnt; intros. 
      - simpl. exists M.  split...
        + constructor.
        + rewrite sep_pure. apply sep_drop in H. intuition. 
      - simpl.
        erewrite <- trange_eqv with (mid := sp + ofs + 1) in H...
        sepa_in H. 
        edestruct writedown_rule_v with (m := M) (dst_t := tag) (a:= sp + ofs) (priv:=hi) (mv := gp1v) as [R1 R2]...
        { erewrite trange_contains_imp in H. 
          erewrite contains_imp in H.
          eapply H. 
          - instantiate (1:= fun _ => True). auto.
          - intros. subst. constructor. }
        edestruct IHcnt with (ofs := S ofs) (M := updm tag M (sp + ofs) gp1v) as [M'' [P1 P2]]...  
        { eapply sep_swap in R2. replace (sp + S ofs) with (sp + ofs + 1) by lia'.
          replace (sp + ofs + 1 + cnt) with (sp + ofs + S cnt) by lia'.
          eapply R2. } 
        eexists. split.  
        + eapply star_trans.
          * eapply star_one.  
            eapply step_Mstore.
            -- unfold lea; simpl.  now rewrite SPv. 
            -- erewrite offset_arith_ok'...  
               rewrite GP1VAL...
          * eapply P1. 
        + eapply sep_swap in P2. 
          replace (sp + ofs + 1) with (sp + (S ofs)) by lia'.
          rewrite sep_assoc...  
    Transparent sepconj.
    Qed.


    Lemma store_below_limit_fails: forall priv tag val instrs B M sp (ofs:nat) f m tge
                                          (MAP: make_map f = OK m)                            
                                          (SPv: B#SP = Vint (val_of_Z sp))
                                          (SPGU: sp + (frame_size f) + length(params f) <= StkBase)
                                          (SPGL: sp >= StkLimit - (frame_size f))
                                          (OFSG: ofs <= frame_size f),
        sp + ofs < StkLimit -> 
        star step tge (State (Mstore priv tag val (SP+ ofs)::instrs) B M)
          (Failstop BadMemAccess). 
    Proof with (eauto with DB; try lia').
      intros.
      eapply star_one.
      eapply step_Mstore_FS.
      unfold lea. simpl. rewrite SPv... 
      rewrite <- repr_distr_add. 
      unfold make_map in MAP. 
      destruct (Z.leb_spec (Z_of_nat (frame_size f)) maxFrameSize); try (inv MAP; fail).
      pose proof StkBase_WF. 
      pose proof HpBase_WF. 
      pose proof HpBaseLimit_WF.
      rewrite -> unsigned_repr...
      unfold writedown.
      destruct (M (Z_of_nat ofs + sp)). 
      unfold access_in_bounds.
      destruct (Z.leb_spec StkLimit (Z_of_nat ofs + sp))...  simpl. 
      destruct (Z.leb_spec HpBase (Z_of_nat ofs + sp))... simpl. 
      destruct (Z.ltb_spec (Z_of_nat ofs + sp) HpLimit)...
    Qed.

    Lemma match_pub_sep_unchanged_imp: forall vm lo hi vm',
        (forall a , lo <= a < hi -> vm a = vm' a) ->
        massert_imp (match_pub_sep vm lo hi) (match_pub_sep vm' lo hi).
    Proof.
      intros.
      unfold massert_imp; split; intros.
      - simpl in H0 |-*. 
        intros.
        destruct (H0 a H1). 
        pose proof (H a H1). 
        rewrite H4 in H3. 
        intuition.
      - simpl in H0 |-*; auto.
    Qed.

    Lemma match_pub_sep_unchanged_eqv: forall vm lo hi vm',
        (forall a , lo <= a < hi -> vm a = vm' a) ->
        massert_eqv (match_pub_sep vm lo hi) (match_pub_sep vm' lo hi).
    Proof.
      intros.
      split; eapply match_pub_sep_unchanged_imp; eauto.
      intros. symmetry; auto.
    Qed.


    Lemma frame_contents_unchanged_imp: forall f sp m rb vm vm'  
                                               (SPG: sp_good f sp),                                           
        (forall a:Z, sp <= a < StkBase -> vm a = vm' a) -> 
        massert_imp (frame_contents f sp m rb vm)
          (frame_contents f sp m rb vm').
    Proof.
      split; intros.
      - unfold frame_contents in *.
        rewrite <- match_pub_sep_unchanged_imp; eauto. 
        intros.
        inv SPG. 
        apply H.  
        unfold_layout; lia'. 
      - unfold frame_contents in *. 
        rewrite <- match_pub_sep_unchanged_eqv.
        eauto.
        intros. 
        inv SPG.
        symmetry.
        apply H. 
        unfold_layout; lia'. 
    Qed.

    Lemma frame_contents_unchanged_eqv: forall f sp m rb vm vm'  
        (SPG: sp_good f sp),                                           
        (forall a:Z, sp <= a < StkBase -> vm a = vm' a) -> 
        massert_eqv (frame_contents f sp m rb vm)
          (frame_contents f sp m rb vm').
    Proof.
      intros. split; eapply frame_contents_unchanged_imp; eauto.
      intros. symmetry; auto.
    Qed.

    Lemma heap_contents_footprint : forall h b vm a,
        b <= a < b + heap_size h <->         
          m_footprint (heap_contents h b vm) a. 
    Proof.
      induction h; intros. 
      - simpl. lia.
      - simpl. destruct a as [sz af]. rewrite heap_size_cons.  unfold obj_size.
        simpl. 
        pose proof (IHh (b + 1 + sz) vm a0). 
        split.
        * intros. 
          destruct (Z.eq_dec b a0); try lia'. 
          right.
          destruct (Z_lt_ge_dec a0 (b + 1 + Z.of_nat sz)); try lia'.
          right.
          apply H.  lia'. 
        * intros.
          destruct H0; try lia'. 
          destruct H0; try lia'. 
          apply H in H0.  lia'. 
    Qed.

    Lemma heap_contents_split_eqv: forall h1 h2 b vm,
        massert_eqv (heap_contents (h1++h2) b vm)
                    (heap_contents h1 b vm ** heap_contents h2 (b + heap_size h1) vm).
    Proof.
      induction h1; intros. 
      - simpl.  rewrite Z.add_0_r.
        split.
        + unfold massert_imp; split.
          * intros. rewrite sep_pure. split; auto. 
          * simpl. intros. destruct H; intuition.
        + unfold massert_imp; split.
          * intros. rewrite sep_pure in H. destruct H; auto.
          * simpl. intros. right; auto.
      - simpl. destruct a as [sz af].  rewrite heap_size_cons. unfold obj_size.
        split.
        + unfold massert_imp; split.
          * intros.
            rewrite IHh1 in H. 
            replace (b + Z.of_nat (S sz + heap_size h1))
              with (b + 1 + sz + heap_size h1) by lia.
            repeat rewrite sep_assoc. 
            auto.
          * intro. simpl.  repeat rewrite <- heap_contents_footprint. 
            rewrite heap_size_app.
            lia'. 
        + unfold massert_imp; split.
          * intros.
            replace (b + Z.of_nat (S sz + heap_size h1))
                      with ((b + 1 + Z.of_nat sz) + Z.of_nat (heap_size h1)) in H by lia. 
            repeat rewrite sep_assoc in H.  rewrite <- IHh1 in H.  auto.
          * intro. simpl. repeat rewrite <- heap_contents_footprint.
            rewrite heap_size_app. lia'. 
    Qed.             
            
    Lemma heap_contents_unchanged_imp: forall h b vm vm',
        (forall a:Z, b <= a < b + heap_size h -> vm a = vm' a) -> 
        massert_imp (heap_contents h b vm)
          (heap_contents h b vm').
    Proof.
      induction h; intros. 
      - simpl. eapply massert_imp_refl.
      - simpl. destruct a as [sz af].
        rewrite heap_size_cons in H; simpl in H. 
        erewrite IHh with (vm' := vm'); try lia'.
        2: {  intros; eapply H; lia'.  }
        erewrite match_pub_sep_unchanged_imp with (vm':=vm'). 
        2 : { intros; eapply H ; lia'. }
        eapply massert_imp_refl.
    Qed.

    Lemma heap_contents_unchanged_eqv: forall h b vm vm',
        (forall a:Z, b <= a < b + heap_size h -> vm a = vm' a) -> 
        massert_eqv (heap_contents h b vm)
          (heap_contents h b vm').
    Proof.
      intros. split; eapply heap_contents_unchanged_imp; eauto.
      intros. symmetry; auto. 
    Qed.

    Lemma stack_contents_unchanged_imp : forall p cs vm vm' retaddr retaddrs callee_params sp 
                                                (STACK: match_stacks p cs (retaddr::retaddrs) sp callee_params),
        (forall a : Z, sp <= a < StkBase -> vm a = vm' a) ->
        massert_eqv (stack_contents cs retaddrs sp callee_params vm)
          (stack_contents cs retaddrs sp callee_params vm').
    Proof.
      induction cs; intros.
      - split; intros.
        + split; intros.
          * constructor.
          * simpl in H0. intuition.
        + split; intros.
          * constructor.
          * simpl in H0. intuition.
      - split; intros.
        + split; intros.
          *  unfold stack_contents in H0|-*. fold stack_contents in H0|-*.
             destruct retaddrs; auto. 
             inv STACK.
             erewrite <- frame_contents_unchanged_eqv with (vm := vm); eauto.
             erewrite <- IHcs; eauto.
             intros.
             eapply H; lia'. 
          *  unfold stack_contents in H0|-*.  fold stack_contents in H0|-*.
             destruct retaddrs; auto. 
             inv STACK.
             erewrite <- frame_contents_unchanged_eqv with (vm := vm'); eauto.
             2: {  intros. symmetry; eapply  H; lia'.  }
             erewrite <- IHcs; eauto. 
             intros. symmetry; eapply H; lia'. 
        + split; intros.
          *  unfold stack_contents in H0|-*. fold stack_contents in H0|-*.
             destruct retaddrs; auto. 
             inv STACK.
             erewrite <- frame_contents_unchanged_eqv with (vm := vm'); eauto.
             2: { intros. symmetry; eapply H; lia'.  }
             erewrite <- IHcs; eauto.
             intros.
             symmetry; eapply H; lia'. 
          *  unfold stack_contents in H0|-*.  fold stack_contents in H0|-*.
             destruct retaddrs; auto. 
             inv STACK.
             erewrite <- frame_contents_unchanged_eqv with (vm := vm); eauto.
             erewrite <- IHcs; eauto. 
             intros. eapply H; lia'. 
    Qed.


    Lemma hasvalue_match_pub_sep: forall lo vm, 
        vm lo = NULL -> 
        massert_imp (hasvalue lo (Vint NULL) t_unp)
          (match_pub_sep vm lo (lo + 1)).
    Proof.
      intros. unfold massert_imp; split; intros.
      - simpl in H0. destruct H0 as [H1 [H2 H3]]. destruct (m lo) eqn:?; simpl in *; subst.
        intros. assert (a = lo) by lia'. subst. 
        split; auto. rewrite H. auto. 
      - simpl in H0.  simpl. lia'.
    Qed.

    Lemma hasvalues_match_pub_sep : forall (count:nat) lo vm, 
        (forall a, lo <= a < lo + count -> vm a = NULL)  -> 
        massert_imp (hasvalues lo (repeat (Vint NULL) count) t_unp)
          (match_pub_sep vm lo (lo + count)).
    Proof.
      induction count; intros.
      - unfold massert_imp; split; intros. 
        + simpl. lia'.  
        + simpl in H0. lia'.
      - unfold massert_imp; split; intros.
        + simpl in H0. erewrite <- match_pub_sep_split_eqv with (mid := lo + 1); try lia'.
          replace (lo + (S count))  with (lo + 1 + count) by lia'. 
          erewrite <- IHcount.
          2: { intros. eapply H; try lia'.  }
          erewrite <- hasvalue_match_pub_sep; eauto.
          rewrite H; auto; try lia'. 
        + simpl in H0. apply hasvalues_footprint.  rewrite repeat_length. lia'. 
    Qed.

    (** Correctness of builtins *)

    Lemma split_heap_impl_match: forall h b n h2 o h1 h0 M vm P
                                        (BBB: b >= HpBase)                                        
                                        (HSP: Z.of_nat (heap_size h) = HpLimit - b),
        split_heap h n = Some(h2, o, h1, h0) -> 
        M |= heap_contents h b vm ** P -> 
        exists rv M',
          hpAlloc_loop M n b = Normal(rv, M') /\
            (rv = val_of_Z (b + heap_size h2 + 1)) /\
            M' |= heap_contents (h2 ++ o:: h1 ++ h0) b vm ** P.                                            
    Proof.
      Opaque sepconj.
      induction h; intros.
      - inv H. 
      - inv H. 
        pose proof HpLimit_WF. pose proof HpBase_WF. pose proof HpBaseLimit_WF. pose proof min_signed_neg.
        assert (MMM: min_signed = -max_signed - 1) by (unfold min_signed, max_signed; lia'). 
        destruct a as [s af]. 
        maybeMonadInv H2. 
        + (* already allocated or too small; recurse *)
          rewrite heap_size_cons in HSP. simpl in HSP. 
          edestruct (IHh (b + 1 + s)) as [rv [M' [P1 [P2 P3]]]]; eauto. clear IHh.
          * lia'. 
          * lia'. 
          * simpl in H0. sepa_in H0. rewrite sep_swap3 in H0. eauto.
          * exists rv, M'. split;[|split].
            -- funelim (hpAlloc_loop M n b). rewrite <- Heqcall. clear Heqcall H H0. 
               destruct (Z_lt_ge_dec p HpLimit); try lia'. 
               simpl in H1. 
               erewrite lookup_rule_v.
               2: { sepa_in H1. apply sep_proj1 in H1. eauto. }
               2: { constructor. }
               simpl. 
               destruct af. 
               ++ unfold val_of_Z; rewrite signed_repr; try lia'. 
                  destruct (Z.eq_dec (Z_of_nat s + 1) 0); try lia'.
                  destruct (Z_lt_ge_dec (Z_of_nat s + 1) 0); try lia'. 
                  replace (p + (Z_of_nat s + 1)) with (p + 1 + Z_of_nat s) by lia'. eauto. 
               ++ rewrite Nat.ltb_lt in Heqb0.
                  unfold val_of_Z; rewrite signed_repr; try lia'.
                  destruct (Z.eq_dec (- (Z_of_nat s + 1)) 0); try lia'.
                  destruct (Z_lt_ge_dec (- (Z_of_nat s + 1)) 0); try lia'. 
                  destruct (Z.geb_spec (- - (Z_of_nat s + 1)) (Z_of_nat sz + 1)); try lia'.  
                  replace (p + -- (Z_of_nat s + 1)) with (p + 1 + Z_of_nat s) by lia'. eauto.  
            -- rewrite heap_size_cons. simpl. rewrite P2. f_equal. lia'. 
            -- simpl. sepa. rewrite sep_swap3. eauto.
        + (* matches exactly *)
          rewrite orb_false_iff in Heqb0. destruct Heqb0. subst af. 
          apply Nat.eqb_eq in Heqb1. subst n.  clear H5.
          rewrite heap_size_cons in HSP. 
          simpl in HSP,H0|-*.
          set (M' := updm t_pro M b (Vint (val_of_Z (Z_of_nat s + 1)))).
          unfold hasvalue in H0.  sepa_in H0. 
          epose proof (updm_rule_v _ _ (Vint (val_of_Z (Z_of_nat s + 1))) t_pro _ _ _ H0).
          fold M' in H2. 
          exists (val_of_Z(b+1)), M'. split;[|split]. 
          * funelim (hpAlloc_loop M s b).  rewrite <- Heqcall. clear Heqcall H H0. 
            destruct (Z_lt_ge_dec p HpLimit); try lia'. 
            erewrite lookup_rule_v.
            2: { sepa_in H1. apply sep_proj1 in H1. eauto. }
            2: { constructor. }
            simpl. 
            unfold val_of_Z; rewrite signed_repr; try lia'. 
            destruct (Z.eq_dec (- (Z_of_nat sz + 1)) 0); try lia'.
            destruct (Z_lt_ge_dec (- (Z_of_nat sz + 1)) 0); try lia'. 
            destruct (Z.geb_spec (-- (Z_of_nat sz + 1)) (Z_of_nat sz + 1)); try lia'. 
            edestruct (writedown_rule_v _ _ _ _ hi t_pro (Vint (repr (Z_of_nat sz + 1))) _ H1). 
            intros. subst t'. constructor.
            rewrite H0. simpl. 
            destruct (Z.gtb_spec (-- (Z_of_nat sz + 1)) (Z_of_nat sz + 1)); try lia'. 
            simpl.  auto.
          * f_equal; lia'. 
          * sepa. auto.
        + (* matches with slop *)
          rewrite orb_false_iff in Heqb0. destruct Heqb0. subst af. 
          apply Nat.eqb_neq in Heqb1.
          apply Nat.ltb_ge in H5. 
          rewrite heap_size_cons in HSP.
          simpl in HSP,H0|-*.
          set (M' := updm t_pro M b (Vint (val_of_Z (Z_of_nat n + 1)))).
          unfold hasvalue in H0.  sepa_in H0. 
          epose proof (updm_rule_v _ _ (Vint (val_of_Z (Z_of_nat n + 1))) t_pro _ _ _ H0).
          fold M' in H2. 
          erewrite <- match_pub_sep_split_eqv with (mid := b + 1 + Z_of_nat n) in H2; try lia'.
          erewrite <- match_pub_sep_split_eqv with (lo := b + 1 + Z_of_nat n) (mid := b + 1 + Z_of_nat n + 1) in H2; try lia'. 
          sepa_in H2. 
          rewrite sep_swap3 in H2. 
          rewrite -> match_pub_sep_trange_imp in H2.
          rewrite trange_contains_imp in H2. 
          set (M'' := updm t_pro M' (b + 1 + Z_of_nat n) (Vint (val_of_Z (- (Z_of_nat (s -n - 1) + 1))))).
          epose proof (updm_rule_v _ _ (Vint (val_of_Z (- (Z_of_nat (s -n - 1) + 1)))) t_pro _ _ _ H2).
          fold M'' in H6.
          rewrite sep_swap3 in H6. 
          exists (val_of_Z(b+1)), M''. split;[|split]. 
          * funelim (hpAlloc_loop M n b).  rewrite <- Heqcall. clear Heqcall H H0. 
            destruct (Z_lt_ge_dec p HpLimit); try lia'. 
            erewrite lookup_rule_v.
            2: {  apply sep_proj1 in H1. eauto. }
            2: { constructor. }
            simpl. 
            unfold val_of_Z; rewrite signed_repr; try lia'. 
            destruct (Z.eq_dec (- (Z_of_nat s + 1)) 0); try lia'.
            destruct (Z_lt_ge_dec (- (Z_of_nat s + 1)) 0); try lia'. 
            destruct (Z.geb_spec (-- (Z_of_nat s + 1)) (Z_of_nat sz + 1)); try lia'. 
            edestruct (writedown_rule_v _ _ _ _ hi t_pro (Vint (repr (Z_of_nat sz + 1))) _ H1). 
            intros. subst t'. constructor.
            rewrite H0. simpl. 
            destruct (Z.gtb_spec (-- (Z_of_nat s + 1)) (Z_of_nat sz + 1)); try lia'. 
            edestruct (writedown_rule_v _ _ _ _ hi t_pro (Vint (repr (Z_of_nat sz + 1 - - - (Z_of_nat s + 1)))) _ H7).  
            intros. subst t'. constructor. 
            replace (p + Z_of_nat sz + 1) with (p + 1 + Z_of_nat sz) by lia'.
            rewrite H11. 
            simpl. 
            unfold M''. unfold val_of_Z. do 6 f_equal. lia'. 
          * f_equal; lia'. 
          * sepa. 
            replace (b+1 + Z_of_nat n + 1 + Z_of_nat (s - n - 1)) with (b + 1 + Z_of_nat s) by lia'. 
            auto.
    Transparent sepconj.
    Qed.          
    
    Lemma hpAlloc_impl_match : forall m lbl n r m' M P
                                      (HSP: heap_sizes_partition m.(hp)),
        hpAlloc m lbl n = Some (r, m') ->
        M |= heap_contents m.(hp) HpBase m.(vmem) ** P -> 
        exists rv M', hpAlloc_impl M n = Normal(rv, M') /\ (rv = val_of_Z (base r))%smem /\
                        M' |= heap_contents m'.(hp) HpBase m'.(vmem) ** P.                                            
    Proof.
      intros.
      unfold hpAlloc in H. 
      maybeMonadInv H. simpl. 
      unfold insert_in_heap in Heqo. maybeMonadInv Heqo. simpl in *. 
      unfold hpAlloc_impl. 
      eapply split_heap_impl_match; eauto.
      lia'.
    Qed.

    Lemma split_heap_fail_match: forall h b n M vm P
                                        (BBB: b >= HpBase)                                        
                                        (HSP: Z.of_nat (heap_size h) = HpLimit - b),
        split_heap h n = None ->
        M |= heap_contents h b vm ** P ->
        exists c, hpAlloc_loop M n b = Failure c. 
    Proof.
      Opaque sepconj.
      pose proof HpLimit_WF. pose proof HpBase_WF. pose proof HpBaseLimit_WF. pose proof min_signed_neg. 
      assert (MMM: min_signed = -max_signed - 1) by (unfold min_signed, max_signed; lia'). 
      induction h; intros.
      - simpl in HSP.  
        funelim (hpAlloc_loop M n b).  rewrite <- Heqcall. clear Heqcall H H0. 
        destruct (Z_lt_ge_dec p HpLimit); try lia'. 
        eexists; auto.
      - simpl in H3. 
        destruct a as [s af]. 
        destruct (af || (s <? n)%nat) eqn:?.
        2: { destruct ((n=?s)%nat); discriminate. }
        destruct (split_heap h n) eqn:?; try discriminate.
        + destruct p. destruct p.  destruct p. discriminate.
        + (* recursion led to failure *)
          rewrite heap_size_cons in HSP. simpl in HSP. 
          assert (exists c, hpAlloc_loop M n (b + 1 + Z_of_nat s) = Failure c).
          { eapply IHh; auto; try lia'. 
            simpl in H4. sepa_in H4. rewrite sep_swap3 in H4. eapply H4.  }
          funelim (hpAlloc_loop M n b).  rewrite <- Heqcall. clear Heqcall H H0. 
          destruct (Z_lt_ge_dec p HpLimit); try lia'; auto. 
          erewrite lookup_rule_v.
          2: {  simpl in H5. apply sep_proj1 in H5. apply sep_proj1 in H5. eauto. }
          2: { constructor. }
          simpl. 
          destruct af. 
          ++ unfold val_of_Z; rewrite signed_repr; try lia'. 
             destruct (Z.eq_dec (Z_of_nat s + 1) 0); try lia'.
             destruct (Z_lt_ge_dec (Z_of_nat s + 1) 0); try lia'. 
             replace (p + (Z_of_nat s + 1)) with (p + 1 + Z_of_nat s) by lia'. eauto. 
          ++ rewrite Nat.ltb_lt in Heqb0.
             unfold val_of_Z; rewrite signed_repr; try lia'.
             destruct (Z.eq_dec (- (Z_of_nat s + 1)) 0); try lia'.
             destruct (Z_lt_ge_dec (- (Z_of_nat s + 1)) 0); try lia'. 
             destruct (Z.geb_spec (- - (Z_of_nat s + 1)) (Z_of_nat sz + 1)); try lia'.  
             replace (p + -- (Z_of_nat s + 1)) with (p + 1 + Z_of_nat s) by lia'. eauto.  
    Transparent sepconj.
    Qed.

    Lemma hpAlloc_fail_match : forall m lbl n M P
                                      (HSP: heap_sizes_partition m.(hp)),
        hpAlloc m lbl n = None -> 
        M |= heap_contents m.(hp) HpBase m.(vmem) ** P -> 
        exists c, hpAlloc_impl M n  = Failure c. 
    Proof.
      intros.
      unfold hpAlloc in H. 
      destruct (insert_in_heap (hp m) n) eqn:?. 
      - destruct p; inv H. 
      - unfold insert_in_heap in Heqo.
        destruct (split_heap (hp m) n) eqn:?.
        + destruct p. destruct p. destruct p.  inv Heqo.
        + eapply split_heap_fail_match; eauto; try lia'. 
    Qed.


    (* for some mysterious reason, version exported from SourceMem doesn't
       rewrite heap_size_nil properly. *)
   Ltac hsize :=
      repeat (try rewrite heap_size_app;
              try rewrite heap_size_cons;
              try rewrite heap_size_nil;
              try rewrite <- rev_heap_size;
              try unfold obj_size).

    Ltac hsize_in H := 
      repeat (try rewrite heap_size_app in H;
              try rewrite heap_size_cons in H;
              try rewrite heap_size_nil in H;
              try rewrite <- rev_heap_size in H;
              try unfold obj_size in H).


    Definition prev_loc (prev:heap) : Z :=
      match prev with
      | [] => HpBase - 1
      | (_::t) => HpBase + heap_size t
      end.

    Lemma locate_in_heap_impl_match: forall h prev a before s after M vm P,
      locate_in_heap prev h a = Some(before,s,after) ->
      forall (HSP: heap_size h + heap_size prev = HpLimit - HpBase),
      M |= heap_contents h (HpBase + heap_size prev) vm ** P ->
      hpFree_loop M a (HpBase + heap_size prev) (prev_loc prev) = Normal (prev_loc before,Z.of_nat s + 1,HpLimit - heap_size after).
    Proof.
      Opaque sepconj.
      induction h; intros. 
      - inv H.
      - simpl in H. 
        destruct a as [s' af'].
        maybeMonadInv H.  
        + simpl in H0. 
          eapply Z.eqb_eq in Heqb. subst a0.
          funelim (hpFree_loop M (HpBase + Z.of_nat (heap_size before) + 1) (HpBase + Z.of_nat (heap_size before)) (prev_loc before)).  rewrite <- Heqcall. clear Heqcall H0 H.
          hsize_in HSP. 
          assert (B: min_signed <= Z.of_nat s + 1 <= max_signed).
          { pose proof HpBaseLimit_WF.  pose proof min_signed_neg. lia'. }
          destruct (Z_lt_ge_dec (HpBase + Z.of_nat (heap_size before)) HpLimit); try lia. 
          erewrite lookup_rule_v; [| repeat rewrite sep_assoc in H1; eapply sep_proj1 in H1; eauto | constructor]. 
          simpl. 
          destruct (Z.eq_dec (HpBase + Z.of_nat (heap_size before) + 1) (HpBase + Z.of_nat (heap_size before) + 1)); try lia'.  
          destruct (Z_gt_le_dec (signed (val_of_Z (Z.of_nat s + 1))) 0); [| (rewrite signed_repr in l0 ; lia)]. 
          f_equal; f_equal; [f_equal|].
          * rewrite signed_repr; lia. 
          * rewrite signed_repr; lia. 
        + eapply Z.eqb_neq in Heqb. 
          exploit (IHh ((s',af')::prev) a0 
                     before s after M vm P).
          * auto.
          * rewrite <- HSP.
            repeat rewrite heap_size_cons. lia'.
          * simpl in H0. 
            hsize.
            repeat rewrite sep_assoc in H0. do 2 apply sep_drop in H0. 
            replace (HpBase + Z.of_nat (S s' + heap_size prev)) with
              (HpBase + Z.of_nat (heap_size prev) + 1 + Z.of_nat s') by lia.
            auto.
          * intro. 
            hsize_in H1. hsize_in HSP. 
            assert (B: min_signed <= Z.of_nat s' + 1 <= max_signed).
            { pose proof HpBaseLimit_WF.  pose proof min_signed_neg. lia'. }
            assert (B1: min_signed <= - (Z.of_nat s' + 1) <= max_signed).
            { pose proof HpBaseLimit_WF.  unfold min_signed, max_signed in *.  lia'. }
            funelim (hpFree_loop M a0 (HpBase + Z.of_nat (heap_size prev)) (prev_loc prev)).
            rewrite <- Heqcall. clear Heqcall H0 H.
            destruct (Z_lt_ge_dec (HpBase + Z.of_nat (heap_size prev)) HpLimit); try lia'.
            erewrite lookup_rule_v; [| repeat rewrite sep_assoc in H2; eapply sep_proj1 in H2; eauto | constructor]. 
            simpl.
            destruct (Z.eq_dec a (HpBase + Z.of_nat (heap_size prev) + 1)); try lia'. 
            destruct (Z.eq_dec (signed (val_of_Z (if af' then Z.of_nat s' + 1 else - (Z.of_nat s' + 1)))) 0).
            -- destruct af'; rewrite signed_repr in e; lia. 
            -- destruct (Z_gt_le_dec (signed (val_of_Z (if af' then Z.of_nat s' + 1 else - (Z.of_nat s' + 1)))) 0).
               ++ destruct af'.
                  ** rewrite signed_repr; try lia. 
                     rewrite <- H3. f_equal. lia'. 
                  ** rewrite signed_repr in g; lia. 
               ++ destruct af'.
                  ** rewrite signed_repr in l0; lia. 
                  ** rewrite signed_repr; try lia. 
                     rewrite <- H3. f_equal. lia.
    Transparent sepconj.
    Qed.

    Lemma locate_in_heap_fail_match: forall h prev a vm M P,
      locate_in_heap prev h a = None -> 
      forall (HSP: heap_size h + heap_size prev = HpLimit - HpBase),
      M |= heap_contents h (HpBase + heap_size prev) vm ** P ->
      exists c, hpFree_loop M a (HpBase + heap_size prev) (prev_loc prev) = Failure c. 
    Proof.
      Opaque sepconj.
      induction h; intros. 
      - simpl in HSP.  rewrite HSP. 
        eexists. 
        funelim (hpFree_loop M a (HpBase + (HpLimit - HpBase)) (prev_loc prev)). 
        rewrite <- Heqcall. clear Heqcall H0 H. 
        destruct (Z_lt_ge_dec (HpBase + (HpLimit - HpBase)) HpLimit); try lia'.
        eauto.
      - simpl in H. 
        destruct a as [s af].
        hsize_in HSP.
        assert (B: min_signed <= Z.of_nat s + 1 <= max_signed).
        { pose proof HpBaseLimit_WF.  pose proof min_signed_neg. lia'. }
        assert (B1: min_signed <= - (Z.of_nat s + 1) <= max_signed).
        { pose proof HpBaseLimit_WF.  unfold min_signed, max_signed in *.  lia'. }
        destruct (Z.eqb_spec a0 (HpBase + Z.of_nat (heap_size prev) + 1)). 
        + destruct af; try inv H.  
          funelim (hpFree_loop M (HpBase + Z.of_nat (heap_size prev) + 1) (HpBase + Z.of_nat (heap_size prev)) (prev_loc prev)).
          rewrite <- Heqcall. clear Heqcall H0 H.
          destruct (Z_lt_ge_dec (HpBase + Z.of_nat (heap_size prev)) HpLimit); try lia'. 
          simpl in H1. 
          repeat rewrite sep_assoc in H1. 
          erewrite lookup_rule_v; [| eapply sep_proj1 in H1; eauto| constructor]. 
          simpl. 
          destruct (Z.eq_dec (HpBase + Z.of_nat (heap_size prev) + 1) (HpBase + Z.of_nat (heap_size prev) + 1)); try lia'. 
          rewrite signed_repr; try lia'. 
          destruct (Z_gt_le_dec (- (Z.of_nat s + 1)) 0); try lia'.
          eexists; eauto.
        + exploit IHh. 
            apply H. 
            hsize. lia'.
            hsize. simpl in H0.
              repeat rewrite sep_assoc in H0. rewrite sep_swap3 in H0.
              replace (HpBase + Z.of_nat (S s + heap_size prev)) with
                (HpBase + Z.of_nat (heap_size prev) + 1 + Z.of_nat s) by lia'. 
              eapply H0. 
         intro Q. 
         hsize_in Q. unfold prev_loc in Q.
         funelim (hpFree_loop M a0 (HpBase + Z.of_nat (heap_size prev)) (prev_loc prev)).
         rewrite <- Heqcall.  clear Heqcall H0 H.
         destruct (Z_lt_ge_dec (HpBase + Z.of_nat (heap_size prev)) HpLimit); try lia'. 
         simpl in H2. 
         repeat rewrite sep_assoc in H2. 
         erewrite lookup_rule_v; [| eapply sep_proj1 in H2; eauto| constructor]. 
         simpl. 
         destruct (Z.eq_dec a (HpBase + Z.of_nat (heap_size prev) + 1)); try lia'. 
         destruct (Z.eq_dec (signed (val_of_Z (if af then Z.of_nat s + 1 else - (Z.of_nat s + 1)))) 0); eauto. 
         destruct af.
          * rewrite signed_repr in n1 |- *; try lia'. 
            destruct (Z_gt_le_dec (Z.of_nat s + 1) 0); try lia'. 
            replace (HpBase + Z.of_nat (heap_size prev) + (Z.of_nat s + 1))
              with (HpBase + Z.of_nat (S s + heap_size prev)) by lia'. 
            eapply Q. 
          * rewrite signed_repr in n1 |- *; try lia'. 
            destruct (Z_gt_le_dec (- (Z.of_nat s + 1)) 0); try lia'. 
            replace (HpBase + Z.of_nat (heap_size prev)  - - (Z.of_nat s + 1))
              with (HpBase + Z.of_nat (S s + heap_size prev)) by lia'. 
            eapply Q. 
    Qed.



    Lemma clear_word_eqv : forall a a0 b vm, 
        a = a0 -> 
        b = a + 1 -> 
        massert_eqv (match_pub_sep (clear_word a0 vm) a b)
          (hasvalue a (Vint zero) t_unp). 
    Proof.
      intros. subst b a0.  split;  unfold massert_imp.
      - split.
        + intros. unfold clear_word in H. simpl in H. destruct (H a). lia'. 
          unfold hasvalue.  unfold contains. simpl.  split; auto.
          rewrite Z.eqb_refl in H1. rewrite H1.  auto.
        + simpl.  intros. lia'. 
      - split. 
        + intros. unfold clear_word. simpl. unfold hasvalue, contains in H.  simpl in H. destruct H. destruct H0. 
          intros. 
          assert (a0 = a) by lia'. 
          subst a0. 
          split; auto.
          rewrite Z.eqb_refl.   destruct (m a).  simpl in *. subst; auto.
        + simpl. intros. lia'. 
    Qed.

    
    (* Utility tactics for the next proof. More aggressive automation would be desirable! *)

    Ltac cw := (hsize; intros a ?; unfold clear_word;
                repeat
                match goal with |- context [(match Z.eqb ?A ?B with | true => _ | false => _ end)] =>
                                  destruct (Z.eqb_spec A B); try lia'; auto end). 

    Ltac zd :=
      match goal with |- exists _, (((match ?ZC with | left _ => _ | right _ => _ end) = _) /\ _) => 
                        destruct ZC; try lia'
      end.

    Ltac lk := 
      match goal with
        H : lookup _ ?M ?A = _ |- exists _, (do _ <- lookup _ ?M ?A0; _) = _ /\ _ => 
          replace A0 with A by lia' ; rewrite H; simpl
      end.

    Ltac wd :=
          match goal with
            H: writedown _ _ _ ?A _ = _ |- context C [writedown _ _ _ ?A0 _]  => 
             replace A0 with A by lia'; erewrite H 
          end.

    Ltac hv :=         
        match goal with H: _ |= hasvalue ?A ?V _ ** _ |- _ |= hasvalue ?A0 ?V0 _ ** _ => 
           (replace A0 with A at 1 by lia'; replace V0 with V at 1 by (f_equal; f_equal; lia'))
        end.

    Ltac mps := 
        match goal with H: _ |= match_pub_sep ?M ?L ?R ** _ |- _ |= match_pub_sep ?M ?L0 ?R0 ** _ => 
                          (replace L0 with L at 1 by lia'; replace R0 with R at 1 by lia')
        end.

    Ltac hc := 
        match goal with H: _ |= heap_contents ?H ?A ?M ** _ |- _ |= heap_contents ?H ?A0 ?M ** _ => 
                          (replace A0 with A at 1 by lia')
        end.

    Lemma hpFree_impl_match : forall m a m' M P
        (HSP: heap_sizes_partition m.(hp)),
        hpFree m a = Some m' ->
        M |= heap_contents m.(hp) HpBase m.(vmem) ** P -> 
        exists M', hpFree_impl M a = Normal M' /\ 
                     M' |= heap_contents m'.(hp) HpBase m'.(vmem) ** P.
    Proof.
      Opaque sepconj.
      Opaque heap_size.
      intros.
      unfold hpFree in H. 
      unfold hpFree_impl; 
      maybeMonadInv H;
        try(
        pose proof (locate_in_heap_spec1 _ _ _ _ _ _ Heqo) as Q1; simpl in Q1; ring_simplify in Q1; 
        pose proof (locate_in_heap_spec _ _ _ _ _ _ Heqo) as Q2; simpl in Q2;
        subst a;
        exploit locate_in_heap_impl_match;
        [eapply Heqo | rewrite <- HSP; hsize; lia'| hsize; simpl; rewrite Z.add_0_r; eauto|..];
        rewrite Q2 in H0; 
        intro H; hsize_in H; simpl in H;  hsize;
          rewrite Z.add_0_r in H |- *;  rewrite H;  simpl).
      - (* no L no R : no merge *)
        zd. zd.
        (* justify the write *)
        unfold heap_contents in H0. 
        rewrite sep_assoc in H0. 
        setoid_rewrite sep_assoc. 
        exploit writedown_rule_v; [eauto | intros t' T; simpl in T; subst t'; econstructor|].
        intros [R1 R2].
        wd.
        eexists; split; eauto.
      - (* no L alloc R : no merge *) 
        zd. zd.
        (* justify the read *)
        unfold heap_contents in H0; fold heap_contents in H0. 
        rewrite Q2 in HSP.  unfold heap_sizes_partition in HSP.  
        hsize_in HSP. 
        repeat rewrite sep_assoc in H0. 
        exploit lookup_rule_v;[|constructor|].
        {  rewrite sep_swap3 in H0. apply sep_proj1 in H0. 
           eapply H0.  }
        intro L. 
        lk.
        assert (B: min_signed <= Z.of_nat n0 + 1 <= max_signed).
        { pose proof HpBaseLimit_WF.  pose proof min_signed_neg. lia'. }
        rewrite signed_repr; try lia'. 
        zd. 
        repeat setoid_rewrite sep_assoc. 
        exploit writedown_rule_v; [eauto| intros t' T; simpl in T; subst t'; econstructor|].
        intros [R1 R2].
        wd.
        eexists; split; eauto. 
      - (* no L free R : merge right *)
        zd. zd.
        unfold heap_contents in H0; fold heap_contents in H0. 
        rewrite Q2 in HSP.  unfold heap_sizes_partition in HSP.  
        hsize_in HSP. 
        repeat rewrite sep_assoc in H0. 
        exploit lookup_rule_v;[|constructor|].
        { rewrite sep_swap3 in H0. apply sep_proj1 in H0. eapply H0. }
        intro L. 
        lk.
        assert (B: min_signed <= - (Z.of_nat n0 + 1) <= max_signed).
        { pose proof HpBaseLimit_WF.  unfold min_signed, max_signed in *.  lia'. }
        rewrite signed_repr; try lia'.
        zd.
        (* justify writes *)
        exploit writedown_rule_v; [eauto| intros t' T; simpl in T; subst t'; econstructor|].
        intros [R1 R2].
        wd; simpl. 
        rewrite sep_swap3 in R2. 
        exploit writedown_rule_v; [eauto| intros t' T; simpl in T; subst t'; econstructor|].
        intros [S1 S2].
        wd. 
        eexists; split; eauto. 
        (* matching *)
        (* general approach:
             - split regions as needed
             - get rid of any clear_word operations
             - get things in the right order
             - semi-automatically do the lia-based rewrites *)
        rewrite sep_swap3 in S2. 
        set (p := HpBase + n + 1).
        erewrite heap_contents_unchanged_eqv with (vm' := (vmem m)); try cw.
        rewrite <- match_pub_sep_split_eqv with (mid := p); try lia'.
        setoid_rewrite <- match_pub_sep_split_eqv with (mid := p + 1) at 2; try lia'.
        setoid_rewrite <- match_pub_sep_unchanged_eqv with (vm := (vmem m)) at 1 3; try cw.
        repeat rewrite sep_assoc. 
        erewrite clear_word_eqv; try lia'. 
        hv.
        rewrite -> sep_swap2 in S2 |-*; mps.
        rewrite -> sep_swap3 in S2 |-*; hv.
        rewrite -> sep_swap4 in S2 |-*; mps.
        rewrite -> sep_swap5 in S2 |-*; hc.
        eapply S2. 
      - (* alloc L no R : no merge *)
        zd.
        rewrite Q2 in HSP.  unfold heap_sizes_partition in HSP.  
        hsize_in HSP. 
        repeat rewrite <- app_assoc in H0. 
        rewrite heap_contents_split_eqv in H0. 
        rewrite sep_assoc in H0. 
        hsize_in H0.
        (* justify the read *)
        exploit lookup_rule_v;[|constructor|].
        { apply sep_drop in H0. 
          simpl in H0.  repeat rewrite sep_assoc in H0. apply sep_proj1 in H0. 
          eapply H0. }
        intro L; lk. 
        assert (B: min_signed <= Z.of_nat n0 + 1 <= max_signed).
        { pose proof HpBaseLimit_WF.  pose proof min_signed_neg. lia'. }
        rewrite signed_repr; try lia'. 
        zd. 
        zd.
        (* justify the write *)
        apply sep_swap in H0. 
        rewrite heap_contents_split_eqv in H0. 
        rewrite sep_assoc in H0. rewrite sep_swap in H0.  
        unfold heap_contents at 1 in H0. 
        do 2 rewrite sep_assoc in H0. 
        hsize_in H0.
        exploit writedown_rule_v; [eapply H0 | intros t' T; simpl in T; subst t'; econstructor|].
        intros [R1 R2].
        wd. 
        eexists; split; eauto. 
        (* matching *)
        do 2 rewrite heap_contents_split_eqv.
        do 2 rewrite sep_assoc. 
        rewrite sep_swap3. 
        unfold heap_contents at 1. 
        rewrite heap_size_app.
        hsize.
        do 2 rewrite sep_assoc.
        hv.
        rewrite -> sep_swap2 in R2|-*. mps.
        eapply R2. 
      - (* alloc L alloc R : no merge *)
        zd. 
        (* justify the read *)
        rewrite <- app_assoc in Q2.  simpl in Q2. 
        rewrite Q2 in H0, HSP. 
        unfold heap_sizes_partition in HSP.  hsize_in HSP. 
        do 2 rewrite heap_contents_split_eqv in H0. 
        do 2 rewrite sep_assoc in H0. 
        hsize_in H0. 
        exploit lookup_rule_v;[|econstructor|].
          { apply sep_drop in H0; 
            simpl in H0; repeat rewrite sep_assoc in H0; apply sep_proj1 in H0; 
            eapply H0. }
        intro L1. lk. 
        assert (B: min_signed <= Z.of_nat n0 + 1 <= max_signed).
        { pose proof HpBaseLimit_WF.  pose proof min_signed_neg. lia'. }
        rewrite signed_repr; try lia'. 
        zd. zd.
        (* justify the read *)
        exploit lookup_rule_v;[|econstructor|]. 
        { change ((n,true) :: (n1,true):: h2) with
            (((n,true)::nil) ++ ((n1,true)::h2)) in H0.  
          rewrite heap_contents_split_eqv in H0. 
          rewrite sep_assoc in H0. rewrite sep_swap4 in H0.  
          unfold heap_contents at 1 in H0. fold heap_contents in H0. 
          do 2 rewrite sep_assoc in H0. 
          apply sep_proj1 in H0. 
          hsize_in H0. 
          eapply H0. }
        intro L2.
        lk.
        assert (B1: min_signed <= Z.of_nat n1 + 1 <= max_signed).
        { pose proof HpBaseLimit_WF.  pose proof min_signed_neg. lia'. }
        rewrite signed_repr; try lia'.
        zd.
        (* justify the write *)
        rewrite sep_swap3 in H0.
        change ((n, true) :: (n1, true) :: h2) with ([(n,true)] ++ (n1,true)::h2) in H0.
        rewrite heap_contents_split_eqv in H0. 
        rewrite sep_assoc in H0. 
        unfold heap_contents at 1 in H0. 
        rewrite sep_assoc in H0. 
        hsize_in H0. 
        exploit writedown_rule_v;[eapply H0 | intros t' T; simpl in T; subst t'; econstructor|]. 
        intros [R1 R2].
        wd.
        eexists; split; eauto. 
        (* matching *)
        rewrite sep_assoc in R2. 
        change ((n,false):: (n1,true):: h2) with ([(n,false)] ++ ((n1,true) :: h2)). 
        do 3 rewrite heap_contents_split_eqv.
        rewrite sep_swap2.
        do 3 rewrite sep_assoc.
        rewrite sep_swap23.  rewrite sep_swap34. rewrite sep_swap23.
        unfold heap_contents at 1. 
        hsize. 
        do 2 rewrite sep_assoc. 
        eapply R2. 
      - (* alloc L free R : merge right *)
        zd. 
        (* justify the read *)
        rewrite <- app_assoc in Q2.  simpl in Q2. 
        rewrite Q2 in H0, HSP. 
        unfold heap_sizes_partition in HSP.  hsize_in HSP. 
        repeat rewrite heap_contents_split_eqv in H0. 
        do 2 rewrite sep_assoc in H0. 
        hsize_in H0. 
        rewrite sep_swap in H0. 
        exploit lookup_rule_v; [|econstructor|]. 
        { apply sep_proj1 in H0. 
          eapply H0. }
        intro L1.  lk. 
        assert (B: min_signed <= Z.of_nat n0 + 1 <= max_signed).
        { pose proof HpBaseLimit_WF.  pose proof min_signed_neg. lia'. }
        rewrite signed_repr; try lia'. 
        zd. 
        zd.
        (* justify the read *)
        exploit lookup_rule_v; [|constructor|]. 
        { change ((n,true) :: (n1,false):: h2) with
             (((n,true)::nil) ++ ((n1,false)::h2)) in H0.  
          rewrite heap_contents_split_eqv in H0. 
          rewrite sep_assoc in H0. rewrite sep_swap4 in H0.  
          hsize_in H0.
          unfold heap_contents at 1 in H0. fold heap_contents in H0. 
          do 2 rewrite sep_assoc in H0. 
          apply sep_proj1 in H0. 
          eapply H0. }
        intro L2. lk.
        assert (B1: min_signed <= - (Z.of_nat n1 + 1) <= max_signed).
        { pose proof HpBaseLimit_WF.  unfold min_signed, max_signed in *.  lia'. }
        rewrite signed_repr; try lia'. 
        zd.
        (* justify the writes *)
        do 2 rewrite sep_assoc in H0. rewrite sep_swap5 in H0.
        unfold heap_contents at 1 in H0.   fold heap_contents in H0. 
        do 4 rewrite sep_assoc in H0. 
        exploit writedown_rule_v; [eapply H0 |intros t' T; simpl in T;subst t'; econstructor |]. 
        intros [R1 R2].
        wd; simpl. 
        rewrite sep_swap3 in R2. 
        exploit writedown_rule_v; [eapply R2 | intros t' T; simpl in T; subst t'; econstructor|]. 
        intros [S1 S2]. 
        wd; simpl.
        eexists; split; eauto. 
        (* matching *)
        change (((n+n1+1)%nat,false) :: h2) with ([((n+n1+1)%nat,false)] ++ h2). 
        do 3 rewrite heap_contents_split_eqv. 
        do 3 rewrite sep_assoc.
        rewrite sep_swap3. 
        unfold heap_contents at 1. 
        do 2 rewrite sep_assoc.
        rewrite sep_swap3. rewrite sep_pure. split; auto.
        hsize. 
        set (p := HpBase + heap_size h1 + n0 + 1 + n + 1). 
        rewrite <- match_pub_sep_split_eqv with (mid := p); try lia'. 
        setoid_rewrite <- match_pub_sep_split_eqv with (mid := p + 1) at 2; try lia'. 
        do 2 rewrite sep_assoc.
        rewrite sep_swap.
        setoid_rewrite <- match_pub_sep_unchanged_eqv with (vm := (vmem m)) at 2 3; try cw.
        erewrite (heap_contents_unchanged_eqv
                    (rev h1) _ _ (vmem m)); try cw. 
        erewrite (heap_contents_unchanged_eqv
                    [(n0,true)] _ _ (vmem m)); try cw.
        erewrite (heap_contents_unchanged_eqv h2 _ _ (vmem m)); try cw.
        erewrite clear_word_eqv; try lia'.
        unfold heap_contents at 1.
        do 2 rewrite sep_assoc. 
        rewrite sep_swap34.
        rewrite sep_swap89 sep_swap78 sep_swap67 sep_swap56.
        rewrite sep_swap67.
        rewrite sep_swap78.
        rewrite sep_swap89.
        hv.
        rewrite -> sep_swap2 in S2 |- *; mps.
        rewrite -> sep_swap3 in S2 |- *; hv.
        rewrite -> sep_swap4 in S2 |- *; mps.
        rewrite -> sep_swap5 in S2 |- *; hc.
        eapply S2. 
      - (* free L no R : merge left *)
        zd.
        rewrite Q2 in HSP. unfold heap_sizes_partition in HSP. hsize_in HSP.
        (* justify the read *)
        rewrite <- app_assoc in H0. simpl in H0.
        rewrite heap_contents_split_eqv in H0.  
        exploit lookup_rule_v; [|constructor|]. 
          { simpl in H0.
            hsize_in H0. 
            rewrite sep_swap in H0.  rewrite sep_assoc in H0. apply sep_proj1 in H0. 
            eapply H0. }
        intro L. lk.
        assert (B: min_signed <= - (Z.of_nat n0 + 1) <= max_signed). 
        { pose proof HpBaseLimit_WF.  unfold min_signed, max_signed in *.  lia'. }
        rewrite signed_repr; try lia'.  
        zd. zd.
        rewrite sep_assoc sep_swap in H0. hsize_in H0. 
        unfold heap_contents at 1 in H0. rewrite sep_assoc in H0. 
        exploit writedown_rule_v; [eapply H0 | intros t' T; simpl in T; subst t'; econstructor|]. 
        intros [R1 R2].
        wd; simpl.
        do 2 rewrite sep_assoc  in R2.  rewrite sep_swap3 in R2. 
        exploit writedown_rule_v; [eapply R2 | intros t' T; simpl in T; subst t'; econstructor|].
        intros [S1 S2].
        wd.
        eexists; split; auto. 
        (* matching *)
        rewrite heap_contents_split_eqv. 
        set (p := HpBase + heap_size h1 + n0 + 1). 
        hsize.
        erewrite (heap_contents_unchanged_eqv
                    (rev h1) _ _ (vmem m)); try cw.
        rewrite sep_assoc sep_swap.
        unfold heap_contents at 1. 
        repeat rewrite sep_assoc.
        rewrite sep_swap3 sep_pure; split; auto. 
        hsize.
        setoid_rewrite <- match_pub_sep_split_eqv with (mid := p); try lia'. 
        rewrite sep_assoc.
        setoid_rewrite <- match_pub_sep_split_eqv with (mid := p+1) at 2; try lia'. 
        rewrite sep_assoc.
        hsize.
        erewrite (match_pub_sep_unchanged_eqv
                    (clear_word p (vmem m)) (HpBase + Z.of_nat (heap_size h1) + 1) p);  try cw. 
        erewrite (match_pub_sep_unchanged_eqv
                    (clear_word p (vmem m)) (p+1)); try cw.
        erewrite clear_word_eqv; try lia'. 
        rewrite sep_swap34 sep_swap23 sep_swap34.
        rewrite sep_assoc in S2. 
        rewrite sep_swap5 sep_pure in S2.  destruct S2 as [_ S2]. 
        mps.
        rewrite -> sep_swap2 in S2 |- *; hv.
        rewrite -> sep_swap3 in S2 |- *; mps.
        rewrite -> sep_swap4 in S2 |- *; hv.
        eapply S2. 
      - (* free L alloc R : merge left *)
        zd.
        (* justify the reads *)
        rewrite Q2 in HSP. unfold heap_sizes_partition in HSP. hsize_in HSP.
        rewrite <- app_assoc in H0. simpl in H0.
        rewrite heap_contents_split_eqv in H0.  
        exploit lookup_rule_v; [|constructor|]. 
        { simpl in H0.
          hsize_in H0. 
          rewrite sep_swap in H0.  rewrite sep_assoc in H0. apply sep_proj1 in H0. 
          eapply H0. }
        intro L1. lk.
        assert (B: min_signed <= - (Z.of_nat n0 + 1) <= max_signed). 
        { pose proof HpBaseLimit_WF.  unfold min_signed, max_signed in *.  lia'. }
        rewrite signed_repr; try lia'.
        zd. 
        zd.
        exploit lookup_rule_v; [|constructor|]. 
        { change ((n0,false) :: (n,true):: (n1,true) :: h2) with
              ([(n0,false);(n,true)] ++ (n1,true)::h2) in H0.
          rewrite heap_contents_split_eqv in H0. 
          hsize_in H0. 
          rewrite sep_swap3 sep_assoc in H0.  
          unfold heap_contents in H0. 
          rewrite sep_assoc in H0. 
          apply sep_proj1 in H0. 
          eapply H0. }
        intro L2. lk.   
        assert (B1: min_signed <= Z.of_nat n1 + 1 <= max_signed).
        { pose proof HpBaseLimit_WF.  pose proof min_signed_neg. lia'. }
        rewrite signed_repr; try lia'.
        zd.
        (* justify the writes *)
        rewrite sep_assoc sep_swap in H0. hsize_in H0. 
        unfold heap_contents at 1 in H0. fold heap_contents in H0. rewrite sep_assoc in H0. 
        exploit writedown_rule_v; [eapply H0 | intros t' T; simpl in T; subst t'; econstructor|].
        intros [R1 R2].
        wd; simpl.
        do 2 rewrite sep_assoc  in R2.  rewrite sep_swap3 in R2. 
        exploit writedown_rule_v; [eapply R2 | intros t' T; simpl in T; subst t'; econstructor|].
        intros [S1 S2].
        wd. 
        eexists; split; auto.
        (* matching *)
        do 3 rewrite sep_assoc in S2. 
        rewrite heap_contents_split_eqv. 
        hsize.
        set (p := HpBase + (heap_size h1) + n0 + 1).
        erewrite (heap_contents_unchanged_eqv
                    (rev h1) _ _ (vmem m)); try cw.
        rewrite sep_assoc sep_swap.
        change (((n + n0 + 1)%nat, false) :: (n1, true) :: h2)
                 with ([((n+ n0 + 1)%nat, false)] ++ (n1,true)::h2).
        rewrite heap_contents_split_eqv.
        unfold heap_contents at 1.  
        do 3  rewrite sep_assoc.
        rewrite sep_swap3 sep_pure; split; auto.
        setoid_rewrite <- match_pub_sep_split_eqv with (mid := p); try lia'. 
        rewrite sep_assoc.
        setoid_rewrite <- match_pub_sep_split_eqv with (mid := p+1) at 2; try lia'. 
        rewrite sep_assoc.
        erewrite (match_pub_sep_unchanged_eqv
                    (clear_word p (vmem m)) (HpBase + Z.of_nat (heap_size h1) + 1) p);  try cw. 
        erewrite (match_pub_sep_unchanged_eqv
                    (clear_word p (vmem m)) (p+1)); try cw.
        erewrite clear_word_eqv with (vm := vmem m); try lia'.
        hsize.
        erewrite (heap_contents_unchanged_eqv ((n1,true)::h2) _ _ (vmem m)); try cw.
        rewrite sep_swap34 sep_swap23 sep_swap34.
        rewrite sep_swap4 sep_swap34 sep_swap23. 
        unfold heap_contents at 1.  fold heap_contents. do 2 rewrite sep_assoc.
        hv.
        rewrite -> sep_swap2 in S2 |- *; mps.
        rewrite -> sep_swap3 in S2 |- *; hv.
        rewrite -> sep_swap4 in S2 |- *; mps.
        rewrite -> sep_swap5 in S2 |- *; hv.
        rewrite -> sep_swap6 in S2 |- *; mps.
        rewrite -> sep_swap7 in S2 |- *; hc.
        eapply S2. 
      - (* free L free R : merge both *)
        zd.
        (* justify the reads *)
        rewrite <- app_assoc in H0. simpl in H0.
        rewrite heap_contents_split_eqv in H0.  
        exploit lookup_rule_v; [|constructor|]. 
        { simpl in H0.
          hsize_in H0. 
          rewrite sep_swap in H0.  rewrite sep_assoc in H0. apply sep_proj1 in H0. 
          eapply H0. }
        intro L1; lk.
        rewrite Q2 in HSP. unfold heap_sizes_partition in HSP. hsize_in HSP.
        assert (B: min_signed <= - (Z.of_nat n0 + 1) <= max_signed). 
        { pose proof HpBaseLimit_WF.  unfold min_signed, max_signed in *.  lia'. }
        rewrite signed_repr; try lia'. 
        zd. zd.
        exploit lookup_rule_v; [|constructor|]. 
        { change ((n0,false) :: (n,true):: (n1,false) :: h2) with
              ([(n0,false);(n,true)] ++ (n1,false)::h2) in H0.
          rewrite heap_contents_split_eqv in H0. 
          hsize_in H0. 
          rewrite sep_swap3 sep_assoc in H0.  
          unfold heap_contents in H0. 
          rewrite sep_assoc in H0. 
          apply sep_proj1 in H0. 
          eapply H0. }
        intro L2; lk.
        assert (B1: min_signed <= - (Z.of_nat n1 + 1) <= max_signed).
        { pose proof HpBaseLimit_WF.  unfold min_signed, max_signed in *.  lia'. }
        rewrite signed_repr; try lia'.
        zd. 
        (* justify the writes *)
        rewrite sep_assoc sep_swap in H0. hsize_in H0. 
        unfold heap_contents at 1 in H0. fold heap_contents in H0. rewrite sep_assoc in H0. 
        exploit writedown_rule_v; [eapply H0 | intros t' T; simpl in T; subst t'; econstructor|].
        intros [R1 R2].
        wd; simpl.
        do 2 rewrite sep_assoc  in R2.  rewrite sep_swap3 in R2. 
        exploit writedown_rule_v; [eapply R2 | intros t' T; simpl in T; subst t'; econstructor|].
        intros [S1 S2].
        wd; simpl. 
        do 2 rewrite sep_assoc in S2. rewrite sep_swap5 in S2. 
        exploit writedown_rule_v; [eapply S2 | intros t' T; simpl in T; subst t'; econstructor|].
        intros [T1 T2].
        wd; simpl. 
        eexists; split; eauto.
        (* matching *)
        rewrite heap_contents_split_eqv. 
        hsize.
        set (p1 := HpBase + heap_size h1 + n0 + 1).
        set (p2 := p1 + n + 1). 
        erewrite (heap_contents_unchanged_eqv
                    (rev h1) _ _ (vmem m)); try cw. 
        rewrite sep_assoc sep_swap.
        change (((n + n0 + 1 + n1 + 1)%nat, false) :: h2) with
               ([((n + n0 + 1 + n1 + 1)%nat, false)] ++ h2). 
        rewrite heap_contents_split_eqv.
        erewrite (heap_contents_unchanged_eqv
                    h2 _ _ (vmem m)); try cw. 
        rewrite sep_assoc.
        unfold heap_contents at 1. 
        do 2  rewrite sep_assoc.
        rewrite sep_swap3 sep_pure; split; auto.
        setoid_rewrite <- match_pub_sep_split_eqv with (mid := p1); try lia'. 
        rewrite sep_assoc.
        setoid_rewrite <- match_pub_sep_split_eqv with (mid := p1+1) at 2; try lia'. 
        rewrite sep_assoc.
        setoid_rewrite <- match_pub_sep_split_eqv with (mid := p2) at 3; try lia'. 
        rewrite sep_assoc.
        setoid_rewrite <- match_pub_sep_split_eqv with (mid := p2+1) at 4; try lia'. 
        rewrite sep_assoc.
        erewrite (match_pub_sep_unchanged_eqv
                    (clear_word p2 (clear_word p1 (vmem m))) (HpBase + Z.of_nat (heap_size h1) + 1) p1);
          try cw. 
        erewrite (match_pub_sep_unchanged_eqv
                    (clear_word p2 (clear_word p1 (vmem m))) (p1 + 1) p2);
          try cw. 
        erewrite (match_pub_sep_unchanged_eqv
                    (clear_word p2 (clear_word p1 (vmem m))) (p2 + 1) _);
          try cw. 
        erewrite (clear_word_eqv p2) with (vm := (clear_word p1 (vmem m))); try lia'.
        assert (PP: clear_word p2 (clear_word p1 (vmem m)) = clear_word p1 (clear_word p2 (vmem m))).
        {
          unfold clear_word. 
          apply functional_extensionality. intros.
          destruct (Z.eqb_spec x p2); destruct (Z.eqb_spec x p1); try lia'; auto.   }
        setoid_rewrite PP.  
        erewrite clear_word_eqv with (vm := (clear_word p2 (vmem m))); try lia'.
        hsize.
        rewrite sep_assoc in T2. 
        rewrite sep_swap4 sep_swap34 sep_swap23  sep_swap56 sep_swap45 sep_swap34 sep_swap45. 
        hv.
        rewrite -> sep_swap2 in T2 |- *; mps.
        rewrite -> sep_swap3 in T2 |- *; hv.
        rewrite -> sep_swap4 in T2 |- *; mps.
        rewrite -> sep_swap5 in T2 |- *; hv.
        rewrite -> sep_swap6 in T2 |- *; mps.
        rewrite -> sep_swap7 in T2 |- *; hc.
        eapply T2. 
    Qed.


    Lemma hpFree_fail_match: forall m a M P
                                    (HSP: heap_sizes_partition m.(hp)),
        hpFree m a = None ->
        M |= heap_contents m.(hp) HpBase m.(vmem) ** P -> 
        exists c, hpFree_impl M a = Failure c.
    Proof.
      intros.
      unfold hpFree in H. 
      destruct (locate_in_heap [] (hp m) a) eqn:?; try discriminate. 
      destruct p as [p1 est]. 
      destruct p1 as [init s]. 
      destruct init; try discriminate.
      - destruct est; try discriminate.
        destruct o as [sn b].  destruct b; try discriminate.
      - destruct o as [sp b].  destruct b; try discriminate.
        + destruct est; try discriminate.
          destruct o as [sn b0]. destruct b0; try discriminate.
        + destruct est; try discriminate.
          destruct o as [sn b0]. destruct b0; try discriminate.
      - exploit locate_in_heap_fail_match.
          eapply Heqo.
          hsize. rewrite HSP.  lia'. 
          hsize. rewrite Z.add_0_r. eauto.
        intro. hsize_in H1.  rewrite Z.add_0_r in H1. unfold prev_loc in H1. 
        destruct H1 as [c H1]. 
        unfold hpFree_impl. rewrite H1. simpl.
        eexists; eauto.
    Qed.
    

    Section CORRECTNESS.
      Opaque sepconj.


      Variable  prog: RTL.program.
      Variable tprog: Mach.program.
      Hypothesis TRANSL: match_prog prog tprog.


      Ltac autmc := auto with machdb.
      Ltac autmt := auto with matchdb.

      Ltac onestep := econstructor;[|left].
      Ltac twostep :=
        econstructor;[|eright;[|left]].
      Ltac threestep :=
        econstructor;[|eright;[|eright;[|left]]].
      Ltac fourstep :=
        econstructor;[|eright;[|eright;[|eright;[|left]]]].


      Ltac find_in_map :=
        match goal with H: (forall r:reg, In r _ -> r in_map _) |- _ => 
                          (eapply H; unfold regs_c, flat_map; simpl;
                           repeat (eapply set_add_intro; try (left; auto; fail); right);
                           eauto)
        end.


      (* Needs more consistent use of DB! *)
      Notation match_states := (match_states' prog match_vals match_failures). 

      Theorem transl_step_correct: forall S1 S2
         (Sstp: RTLS.step (oracle prog) prog S1 S2) (T1: MacS.state)
         (MST : match_states S1 T1),
        exists T2, plus MacS.step tprog T1 T2
                   /\ match_states S2 T2.
      Proof with (eauto with DB; try (unfold_layout; lia'); try find_in_map).   (* note: blanket simpl here causes problems *)
        destruct 1; intros T1 MST; inv MST;
          try (rename B into sB, B0 into B);
          try (rename M into sM, M0 into M).
        - (* exec_Imov *)
          edestruct frame_contents_hi_update with (r := rd) as [R1 R2]... 
          eexists; split...
          + (* execution *) {
              twostep.
              * (* 1st step - deposit *)
                eapply step_Mload...
              - unfold lea. simpl. now rewrite SPv.
              - erewrite offset_arith_ok... 
                eapply frame_contents_sep_load...
                * (* 2nd step - withdraw *)
                  eapply step_Mstore.
              - unfold lea...
                erewrite SPv_unchanged...
                simpl...
              - rewrite Regmap.gss...
                erewrite offset_arith_ok... } 
          + (* matching *)
            econstructor...
            * intros... 
            * intros; eapply CMP; right; eauto. 
        - (* exec_Imovi *)
          edestruct frame_contents_hi_update with (r := rd) as [R1 R2]...  
          eexists; split...
          + (* execution *) {
              twostep.
              * (* 1st step - movi *)
                eapply step_Mmovi...
              * (* 2nd step - store *)
                eapply step_Mstore.
              - unfold lea... 
                erewrite SPv_unchanged...
                simpl...
              - erewrite offset_arith_ok...
                rewrite Regmap.gss...
            }
          + (* matching *)
            econstructor...
            * intros... 
            * intros; eapply CMP; right; eauto. 
        - (* exec_Iop *)
          edestruct frame_contents_hi_update with (r := rd) as [R1 R2]... 
          eexists; split...
          + (* execution *) {
              fourstep.
              * (* 1st step - load *)
                eapply step_Mload...
                -- unfold lea; simpl; rewrite -> SPv...
                -- erewrite -> offset_arith_ok...
                   eapply frame_contents_sep_load... 
              * (* 2nd step - load *)
                eapply step_Mload...
                -- unfold lea; simpl; rewrite -> Regmap.gso, SPv...
                -- erewrite -> offset_arith_ok...        
                   eapply frame_contents_sep_load... 
              * (* 3rd step - op *)
                eapply step_Mop.
              - unfold eval_op'.
                rewrite -> Regmap.gso, Regmap.gss, Regmap.gss...
              - eauto. 
                * (* 4th step - store *)
                  eapply step_Mstore.
              - unfold lea... repeat rewrite -> Regmap.gso...
                simpl. now rewrite -> SPv.
              - rewrite -> Regmap.gss...
                erewrite -> offset_arith_ok... }
          + (* matching *)
            econstructor...
            * intros...
            * intros; eapply CMP; right; eauto. 
        - (* exec_Iamper *)
          edestruct frame_contents_hi_update with (r := r) as [R1 R2]...  
          eexists; split...
          + (* execution *) {
              threestep.
              * (* 1st step - movi *)
                eapply step_Mmovi... 
              * (* 2nd step - op *)
                eapply step_Mop.
              - unfold eval_op'.
                rewrite -> Regmap.gss, Regmap.gso, SPv...
              - rewrite -> Regmap.set2...
                * (* 3rd step - store *)
                  eapply step_Mstore.
              - unfold lea... simpl. rewrite -> Regmap.gso, SPv...
              - rewrite -> Regmap.gss.
                (* simplify result here *)
                unfold eval_op.
                setoid_rewrite <- repr_distr_add at 2. 
                erewrite -> offset_arith_ok...
            }
          + (* matching *)
            econstructor...
            * intros... 
            * intros; eapply CMP; right; eauto. 
            * setoid_rewrite Zplus_comm at 1... 
        - (* exec_Iload_M *)
          unfold Mem.load in H0. simpl in H0.  unfold load' in H0. 
          destruct (accessible_dec' sM (unsigned sB # rloc)); try inv H0. 
          edestruct frame_contents_hi_update with (r := rd) as [R1 R2]...
          eexists; split...
          + (* execution *) {
              threestep.
              * (* 1st step - load *)
                eapply step_Mload...
              - unfold lea... simpl. rewrite SPv...
              - erewrite offset_arith_ok... 
                eapply frame_contents_sep_load...
                * (* 2nd step - load *)
                  eapply step_Mload.
              - unfold lea...
                rewrite -> Regmap.gss, add_zero_l...
              - eapply state_contents_lo_lookup... 
              - rewrite -> Regmap.set2. eauto. 
                * (* 3rd step - store *)
                  eapply step_Mstore.
              - unfold lea... simpl. rewrite -> Regmap.gso, SPv...
              - rewrite -> Regmap.gss. erewrite -> offset_arith_ok... 
            }
          + (* matching *)
            econstructor...
            * intros... 
            * intros; eapply CMP; right; eauto. 
        - (* exec_Iload_M_OOB *) 
          unfold Mem.load in H0; simpl in H0. unfold load' in H0. 
          destruct (accessible_dec' sM (unsigned sB # rloc)); try inv H0. 
          eapply state_contents_lo_lookup_fail in n...
          destruct n as [msg P]. 
          eexists; split...
          + (* execution *) {
              twostep.
              * (* 1st step - load *)
                eapply step_Mload...
              - unfold lea... simpl. rewrite SPv...
              - erewrite offset_arith_ok... 
                eapply frame_contents_sep_load...
                * (* 2nd step - load *)
                  eapply step_Mload_FS_lkup...
                  unfold lea...
                  rewrite ->  Regmap.gss, add_zero_l... } 
          + (* matching *)
            constructor.  econstructor.
        - (* exec_Istore_M *)
          unfold Mem.store in H0; simpl in H0. 
          edestruct state_contents_lo_update as [P1 P2]...
          eexists; split...
          + (* execution *) {
              threestep.
              * (* 1st step - load *)
                eapply step_Mload...
              - unfold lea... simpl. now rewrite SPv.
              - erewrite offset_arith_ok... 
                eapply frame_contents_sep_load...
                * (* 2nd step - load *)
                  eapply step_Mload...
              - unfold lea... simpl. rewrite -> Regmap.gso, SPv...
              - erewrite offset_arith_ok... 
                eapply frame_contents_sep_load...
                * (* 3rd step - store *)
                  eapply step_Mstore.
              - unfold lea... rewrite -> Regmap.gss, add_zero_l...
              - rewrite -> Regmap.gso, Regmap.gss... }
          + (* matching *)
            econstructor...
            * unfold store' in H0. maybeMonadInv H0... 
            * unfold match_sp in *; erewrite <- stack_store'...
            (*             * inv MSM. econstructor; eauto. 
              erewrite stack_store' in H3; eauto.  *)
            * intros...
            * intros; eapply CMP; right; eauto. 
            * unfold heap_sizes_partition in *; erewrite <- heap_store'...
        - (* exec_Istore_M_OOB *) 
          unfold Mem.store in H0; simpl in H0. 
          edestruct state_contents_lo_update_fail as [msg P]...
          eexists; split...
          + (* execution *) {
              threestep.
              * (* 1st step - load *)
                eapply step_Mload...
              - unfold lea... simpl. rewrite SPv...
              - erewrite offset_arith_ok... 
                eapply frame_contents_sep_load...
                * (* 2nd step - load *)
                  eapply step_Mload...
              - unfold lea... simpl. rewrite -> Regmap.gso, SPv...
              - erewrite offset_arith_ok... 
                eapply frame_contents_sep_load...
                * (* 3rd step - store *)
                  eapply step_Mstore_FS... 
              - unfold lea...
                rewrite -> Regmap.gss, add_zero_l... 
              - rewrite -> Regmap.gso, Regmap.gss... }
          + (* matching *)
            constructor. constructor.
        - (* exec_Icall_M *)
          rename M' into sM'. 
          unfold transl_instrs, transl_instr. simpl flat_map.
          do 2 rewrite <- app_assoc. 
          edestruct push_params_correct with (args := args)
            as [B1 [M1 [P [SPv1 Q]]]]...
          { intros. try find_in_map. rewrite <- In_uniquify. apply in_or_app. intuition. } 
          { eapply CMP. left... } 
          { unfold state_contents in SEP.
            unfold frame_contents in SEP.
            eapply sep_swap3 in SEP. 
            eapply sep_swap23 in SEP. 
            sepa_in SEP.
            eapply SEP. }
          unfold lookup_callable in H0.
          {
            assert (sM = sM').  (* yuck *)
            { clear - H2. inv H2. destruct sM. simpl.  f_equal. }
            subst sM'. 
            maybeMonadInv H0. 
            - (* ordinary function *)
              edestruct match_lookup_function with (id:= cee_id) as [tf [T1 T2]]...
              eexists; split.
              + (* execution *) {
                  eapply star_plus_plus.
                  - eapply P. 
                  - onestep.
                    eapply step_Mjal...
                }
              + (* matching *) {
                  simpl.
                  eapply match_Callstate_f...
                  - apply lookup_function_spec in T1. 
                    apply transl_function_id in T2. rewrite T2 T1; auto. 
                  - rewrite -> Regmap.gso... rewrite <- SPv1... 
                  - destruct SPG as [SPG1 _]...
                  - destruct SPG as [SPG1 SPG2].  rewrite -> H3.
                    assert (length args <= max_callee_params f). 
                    { eapply CMP. left; auto. }
                    unfold_layout; lia'. 
                  - clear P. (* just for screen space *)
                    inv MSM. 
                    econstructor... 
                  - rewrite -> Regmap.gss...  
                    econstructor...
                    + intros. eapply Mele. unfold regs_c. rewrite <- In_uniquify. simpl.
                      unfold regs_c in H. rewrite <- In_uniquify in H.  right. apply in_app. right; auto.
                    + intros. eapply CMP... simpl.  right... 
                    + rewrite -> H3. eapply CMP. left. eauto.
                    + rewrite -> Z.add_comm. eauto.
                  - rewrite -> H3. eapply map_length... 
                  - simpl. unfold frame_contents. rewrite -> H3.
                    clear - Q. 
                    setoid_rewrite -> Z.add_comm at 7. 
                    unfold match_args_sep in Q. 
                    sepa_in Q.
                    rewrite -> map_map. 
                    sepa. 
                    (* oy veh *)
                    apply sep_swap56.
                    apply sep_swap34.
                    apply sep_swap45.
                    apply sep_swap23.
                    apply sep_swap34.
                    apply sep_swap3...
                }
            - (* builtin *)
              edestruct match_lookup_builtin as [tf [mb [HB1 [HB2 HB3]]]]...
              eexists; split.
              + (* execution *) {
                  eapply star_plus_plus.
                  - eapply P. 
                  - onestep.
                    eapply step_Mjal...
                } 
              + (* matching *) {
                  simpl. 
                  rewrite HB2. 
                  eapply match_Callstate_b...
                  - rewrite -> Regmap.gso... rewrite <- SPv1... 
                  - destruct SPG as [SPG1 _]...
                  - destruct SPG as [SPG1 SPG2].  rewrite -> H3.
                    assert (length args <= max_callee_params f). 
                    { eapply CMP. left; auto. }
                    unfold_layout; lia'. 
                  - clear P. (* just for screen space *)
                    inv MSM. 
                    econstructor... 
                  - rewrite -> Regmap.gss...  
                    econstructor...
                    + intros. eapply Mele. unfold regs_c. rewrite <- In_uniquify. simpl.
                      unfold regs_c in H. rewrite <- In_uniquify in H.  right. apply in_app. right; auto.
                    + intros. eapply CMP... simpl.  right... 
                    + rewrite -> H3. eapply CMP. left. eauto.
                    + rewrite -> Z.add_comm. eauto.
                  - rewrite -> H3. eapply map_length... 
                  - simpl. unfold frame_contents. rewrite -> H3.
                    clear - Q. 
                    setoid_rewrite -> Z.add_comm at 7. 
                    unfold match_args_sep in Q. 
                    sepa_in Q.
                    rewrite -> map_map. 
                    sepa.
                    (* my kingdom for a tactic *)
                    apply sep_swap56. 
                    apply sep_swap34.
                    apply sep_swap45.
                    apply sep_swap23.
                    apply sep_swap34.
                    apply sep_swap3...
                } 
          }
        - (* exec_Icall_M_OOM *)
          (* this case cannot happen with this oracle *)
          unfold Mem.perturb, oracle, perturb' in H0.  
          inv H0. 
        - (* exec_pass_control_M *)
          unfold transl_function in MFun. monadInv MFun. simpl. 
          rewrite sep_swap3 in SEP. 
          simpl in H. unfold stkAlloc' in H.
          monadInvDep H. destruct a as [[saddr ssize] sM'].
          inv H. 
          generalize e; intro e'.  (* dependency hell *)
          unfold stkAlloc in e.  simpl (fst (RTL.f_id f, RTL.body f)) in e. 
          maybeMonadInv e.  inv FF. 
          apply orb_false_elim in Heqb; destruct Heqb as [_ Heqb].  
          assert (sp_of_stack ((f,sz_a f) :: stk (proj1_sig sM)) >= StkLimit) by lia'.
          generalize e'; intro e.  (* dependency hell *)
          replace 
         (sp_of_stack (stk (` sM)) - Z.of_nat (max_callee_params f + Datatypes.length (locals f) + 1 + sz_a f) +
          Z.of_nat (max_callee_params f + Datatypes.length (locals f) + 1)) with
         (sp_of_stack (stk (proj1_sig sM)) - sz_a f) in e' by lia'.
          set (sp' := sp - frame_size f). 
          set (sM' := {| stk := (f, sz_a f) :: stk (proj1_sig sM); vmem := vmem (proj1_sig sM) |}).
          unfold match_sp in MSP. 
          assert (SPG: sp_good f sp'). 
          { unfold sp_good. split...
            simpl in H. 
            subst sp. subst sp'... }
          erewrite <- match_pub_sep_split_eqv with (mid := sp') in SEP...
          2: { unfold sp_good in SPG; lia'. }
          rewrite sep_assoc in SEP. 
          rewrite -> sep_swap in SEP. 
          replace sp with (sp' + frame_size f) in SEP at 1 by lia'. 
          rewrite frame_separated_eqv in SEP. sepa_in SEP. 
          unfold protect.
          edestruct stk_tag_correct with (f := f) (sp := sp') (ofs := O) (cnt := max_callee_params f) (gp1v := Vint NULL) as [M' [R1 R2]]... 
          { shelve. }
          { shelve. }
          { replace (sp' + Z_of_nat 0) with sp' by lia'. 
            rewrite match_pub_sep_trange_imp in SEP. 
            eapply SEP. }
          apply sep_swap in R2. 
          edestruct stk_tag_correct with (f := f) (sp := sp') (ofs := locals_ofs f) (cnt := length (locals f)) (gp1v:= Vint NULL) as [M'' [Q1 Q2]]...
          { shelve. }
          { shelve. }
          { rewrite match_pub_sep_trange_imp in R2. 
            eapply R2. }
          edestruct writedown_rule_v with (m := M'') (dst_t := t_pro) (a:= sp' + ra_ofs f) (priv:=hi) (mv := B # RA) as [S1 S2]...
          { rewrite ->  sep_swap3 in Q2. 
            rewrite match_pub_sep_trange_imp in Q2. 
            rewrite trange_contains_imp in Q2. 
            erewrite ->  contains_imp in Q2. 
            eapply Q2.
            - instantiate (1:= fun _ => True). auto.
            - intros. constructor. }
          eexists; split.
          + (* execution *) {
              eapply plus_star_plus;[|eapply star_trans;[|eapply star_trans]]. 
              threestep.
              - eapply step_Mmovi... 
              - eapply step_Mop...
                unfold eval_op'. 
                rewrite ->  Regmap.gso... rewrite ->  Regmap.gss. 
                rewrite ->  SPv...  
              - eapply step_Mmovi...
              - rewrite <- app_assoc. eapply R1. 
              - rewrite <- app_assoc. eapply Q1. 
              - onestep.
                eapply step_Mstore...
                + unfold lea... simpl.  
                  rewrite ->  Regmap.gso... rewrite ->  Regmap.gss...
                + rewrite ->  Regmap.gso... rewrite ->  Regmap.gso... rewrite ->  Regmap.gso...
                  rewrite <- repr_distr_sub.
                  erewrite ->  offset_arith_ok'... }
            Unshelve.
            * rewrite Regmap.gso... rewrite Regmap.gss... simpl. rewrite <- repr_distr_sub. f_equal.
            * rewrite Regmap.gss...
            * rewrite Regmap.gso... rewrite Regmap.gss... simpl. rewrite <- repr_distr_sub.  f_equal.
            * rewrite Regmap.gss...
          + (* matching *) {
              simpl. eapply match_State.
              - eauto.
              - eauto.
              - eauto.
              - rewrite ->  Regmap.gso... rewrite ->  Regmap.gss...
                rewrite <- repr_distr_sub... 
              - pose proof StkLimit_WF.  pose proof StkBase_WF.
                simpl in H...  
              - auto.
              - unfold match_sp in *. simpl... 
              - econstructor...
              - intros. eapply code_in...
              - intros. epose proof (cmp_code _ _ _ _ H0); eauto. unfold max_callee_params. lia'. 
              - unfold sp'.  replace (frame_size f + (sp - frame_size f)) with sp by lia'. eauto. 
              - simpl...
              - unfold state_contents.
                unfold frame_contents. unfold match_env_sep.
                erewrite ->  sep_swap in S2. 
                erewrite hasvalues_trange_imp in S2. 
                replace (sp' + O) with sp' in S2 by lia'. 
                rewrite ->  repeat_length in S2. 
                replace (frame_size f + sp') with sp by lia'.
                unfold match_locals_sep. 
                erewrite ->  init_regs_locals. 
                unfold match_params_sep.
                erewrite ->  init_regs_params...
                replace sp with (sp' + (params_ofs f)) in * by (unfold_layout; lia'). 
                simpl. 
                sepa. 
                eapply sep_swap56.
                eapply sep_swap67.
                eapply sep_swap6.
                eapply sep_swap5.
                eapply sep_swap23.
                eapply S2. 
            }
        -  (* exec_pass_control_M_OOM *)
          unfold transl_function in MFun. monadInv MFun. simpl. 
          sep_swap_end_in SEP. 
          simpl in H. unfold stkAlloc' in H.
          monadInvDep H; [destruct a as [[saddr ssize] sM']; inv H |]. 
          generalize e; intro e'.  (* dependency hell *)
          unfold stkAlloc in e.  simpl (fst (RTL.f_id f,RTL.body f)) in e. 
          rewrite FF in e. 
          destruct (negb (Z.of_nat (sz_a f) =? Z.of_nat (sz_a f)) || (sp_of_stack ((f, sz_a f) :: stk (` sM)) <? StkLimit)) eqn:QQ; try discriminate.
          apply orb_prop in QQ. 
          destruct QQ; try lia'. 
          assert (sp_of_stack ((f, sz_a f)::stk (proj1_sig sM)) < StkLimit) by lia'. 
          simpl in H0.
          set (sp' := sp - frame_size f). 
          eexists; split.
          + (* execution *) {
              eapply plus_star_plus. 
              - threestep.
                + eapply step_Mmovi... 
                + eapply step_Mop...
                  unfold eval_op'. 
                  rewrite ->  Regmap.gso... rewrite ->  Regmap.gss. 
                  rewrite ->  SPv...  
                + eapply step_Mmovi...
              - set (B' := ((B # GP1 <- (Vint (val_of_Z (Z_of_nat (frame_size f))))) # SP <-
                              (Vint (eval_op Osub (val_of_Z sp) (val_of_Z (Z_of_nat (frame_size f)))))) # GP1 <- 
                             (Vint NULL)).
                assert (SPv': B' # SP = Vint(val_of_Z sp')). 
                { rewrite Regmap.gso...  rewrite Regmap.gss... 
                  unfold eval_op. subst sp'. rewrite <- repr_distr_sub... }
                unfold match_sp in MSP. 
                (* first write will fail; need to figure out which code performs this. *)
                destruct (max_callee_params f) eqn:?; simpl in *. 
                + (* no parameters *)
                  destruct (length (locals f)) eqn:?; simpl in *. 
                  * (* no parameters or locals *)
                    (* so writing RA fails *)
                    assert (sp' + ra_ofs f < StkLimit). { unfold_layout; lia'. } 
                    eapply store_below_limit_fails...
                  * (* no parameters, but at least one local *)
                    eapply store_below_limit_fails... 
                + (* at least one parameter *)
                  eapply store_below_limit_fails...  }
          + (* match states *)
            econstructor. constructor.
        - (* exec_Ireturn_M *)
          unfold exit; simpl. 
          unfold state_contents in SEP. 
          simpl in H0. unfold stkFree' in H0. monadInvDep H0. inv H0. 
          generalize e; intro e'.  (* dependency hell *)
          unfold stkFree in e.
          destruct (stk (proj1_sig sM)) eqn:EE; try discriminate. 
          inv e. 
          rename s into s'. 
          set (s := stk(proj1_sig sM)). fold s in EE.
          inv MSM. inv H2. rename s'0 into s'. unfold size_of_frame in *. rename H0 into MSTK.
          rewrite <- EE in MSP. unfold match_sp in MSP. 
          set (vm := vmem(proj1_sig sM)).  fold vm in SEP,e'.
          unfold unprotect.
          (* justify the writes *)
          edestruct writedown_rule_v with (m := M) (dst_t := t_unp) (a:= sp + ra_ofs f) (priv:=hi) as [S1 S2].
          { unfold frame_contents in SEP. 
            sepa_in SEP. 
            apply sep_swap in SEP.
            unfold hasvalue in SEP. 
            eapply SEP.  }
          { intros. simpl in H. subst t'.  constructor. }
          edestruct stk_tag_correct with (f := f) (sp := sp) (ofs := O) (cnt := max_callee_params f) (gp1v := Vint NULL) (* (sM := sM1) *)
            as [M' [R1 R2]]. (* don't commit to B *)
          { auto. }
          { shelve. }
          { unfold_layout; lia'. }
          { shelve. }
          (*    { eauto. }  *)
          (*     { shelve. } *)
          { replace (sp + Z_of_nat 0) with sp by lia'.
            apply sep_swap5 in S2. 
            eapply S2. }
          edestruct stk_tag_correct with (f := f) (sp := sp) (ofs := locals_ofs f) (cnt := length (locals f)) (gp1v:= Vint NULL) as [M'' [Q1 Q2]].   (* don't commit to B *)
          { auto. }
          { shelve. }
          { unfold_layout; lia'. } 
          (*     { eauto. }  *)
          (*     { auto. }  *)
          { shelve. }
          { unfold match_env_sep, match_locals_sep in R2.
            sepa_in R2. 
            apply sep_swap3 in R2.
            rewrite hasvalues_trange_imp in R2. 
            rewrite map_length in R2. 
            eapply R2. }
          eexists; split.
          + (* execution *) {
              unfold deposit. 
              eapply plus_star_plus; [| eapply star_trans; [| eapply star_trans;[| eapply plus_star; twostep]]]. 
              fourstep.
              - eapply step_Mload...
                + unfold lea. simpl. rewrite SPv. eauto.
                + assert (rreg f in_map map).
                  { eapply map_in; eauto. apply rreg_local_or_param. }
                  erewrite offset_arith_ok...
                  eapply frame_contents_sep_load...
              - eapply step_Mload...
                + unfold lea. simpl. rewrite Regmap.gso...  rewrite SPv. eauto.
                + erewrite offset_arith_ok'...
                  unfold frame_contents in SEP. 
                  sepa_in SEP. 
                  apply sep_swap in SEP. apply sep_proj1 in SEP. 
                  eapply lookup_rule_v...
                  constructor.
              - eapply step_Mmovi...
              - eapply step_Mstore...
                + unfold lea.  simpl.  rewrite Regmap.gso... rewrite Regmap.gso... rewrite Regmap.gso... rewrite SPv. eauto.
                + erewrite offset_arith_ok'...
              - eapply R1. 
              - eapply Q1.
              - eapply step_Mmovi...
              - unfold Invariants.SourceMem.Compiler.Madd. eapply step_Mop...
                unfold eval_op'. 
                rewrite Regmap.gso... rewrite Regmap.gso... rewrite Regmap.gso... rewrite Regmap.gso... rewrite SPv.  
                rewrite Regmap.gss... }
            Unshelve.
            * destruct sM. simpl...
            * rewrite Regmap.gss... 
            * rewrite Regmap.gso...
            * rewrite Regmap.gss...
          + (* matching *) {
              assert (GG: (sp_of_stack s' - (max_callee_params f + length (locals f) + 1 + sz_a f)%nat) = sp). 
              { rewrite <- MSP.  rewrite EE. simpl. auto. }
              set (sp' := sp + frame_size f). 
              eapply match_Returnstate with (sp:= sp')...
              - rewrite Regmap.gss...
                rewrite <- repr_distr_add. 
                unfold val_of_Z. 
                f_equal. 
              - destruct SPG...
              - destruct SPG... 
              - rewrite Regmap.gso... rewrite Regmap.gso... rewrite Regmap.gso...  rewrite Regmap.gso... rewrite Regmap.gss...  constructor.
              - simpl. unfold match_sp; simpl.
                unfold stkFree in e'.  destruct (stk (proj1_sig sM)); inv e'. 
                simpl in *.
                simpl in sp'...
              - rewrite Regmap.gso... rewrite Regmap.gso... rewrite Regmap.gso...  rewrite Regmap.gss... 
                inv STACK. 
                + subst sp'.
                  rewrite Z.add_comm. rewrite <- H3.
                  econstructor...
                + subst sp'. 
                  setoid_rewrite Z.add_comm at 3. 
                  econstructor...
              - clear SEP S1 S2 R1 R2 Q1.  (* just for screen space *)
                simpl. 
                subst sp'.
                destruct SPG. 
                apply sep_swap. 
                eapply sep_swap in Q2. 
                unfold match_params_sep in Q2.
                erewrite hasvalues_trange_imp in Q2. 
                replace (sp + O) with sp in Q2 by lia'. 
                rewrite map_length in Q2. 
                rewrite Regmap.gss in Q2. 
                eapply sep_swap in Q2. 
                eapply sep_swap5 in Q2.
                eapply sep_swap in Q2.
                assert (FACTOID: forall P,
                           M'' |=
                             trange (sp + params_ofs f) (sp + params_ofs f + length (params f)) (fun t' => t' = t_pro) **
                             stack_contents cs retaddrs (sp + frame_size f) (length (params f)) (vmem (proj1_sig sM)) ** P ->
                           M'' |= stack_contents cs retaddrs (sp + frame_size f) 0 (vmem (proj1_sig sM)) ** P). 
                { intros P S.
                  destruct cs; simpl in S |-*. 
                  - apply sep_proj2 in S; auto.
                  - destruct retaddrs.
                    * apply sep_proj2 in S; auto.
                    * sepa_in S. apply sep_swap23 in S. 
                      sepa. apply sep_swap.
                      inv STACK.
                      erewrite <- trange_eqv with (mid := (sp_of_stack s + (params_ofs f) + (length (params f))))...   
                      replace ((sp_of_stack s) + (frame_size f) + 0) with ((sp_of_stack s) + frame_size f) by lia'.
                      sepa. unfold_layout. eapply S. }
                setoid_rewrite Z.add_comm in Q2 at 4. 
                eapply FACTOID in Q2; clear FACTOID.
                rewrite GG. 
                erewrite <- stack_contents_unchanged_imp with (vm := vm). 
                2: { rewrite Z.add_comm. inv STACK... econstructor. econstructor... }
                (* need some tactic support here *)
                2: { intros. unfold clear_frame_private. simpl. 
                     rewrite andb_comm. 
                     destruct (Z.ltb_spec a (sp + Z_of_nat (max_callee_params f + Datatypes.length (locals f) + 1 + sz_a f)))... }
                erewrite <- match_pub_sep_split_eqv with (mid := sp)...
                apply sep_assoc. apply sep_swap.
                erewrite frame_separated_eqv. sepa.
                erewrite <- match_pub_sep_unchanged_eqv with (vm := vm) (lo := (sp + arr_ofs f)).
                2: { intros. unfold clear_frame_private. simpl. 
                     destruct (Z.leb_spec sp a)...
                     destruct (Z.ltb_spec a (sp + Z_of_nat (max_callee_params f + Datatypes.length (locals f) + 1 + sz_a f)))...
                     simpl.
                     destruct (within_dec (sp + Z_of_nat (max_callee_params f + Datatypes.length (locals f) + 1), sz_a f) a)...
                     unfold within in n. simpl in n... }
                erewrite <- match_pub_sep_unchanged_eqv with (vm := vm) (lo := StkLimit).
                2: { intros. unfold clear_frame_private. simpl. 
                     destruct (Z.leb_spec sp a)... }
                erewrite <- hasvalues_match_pub_sep with (lo := sp). 
                2: {  intros. unfold clear_frame_private. simpl. 
                      destruct (Z.leb_spec sp a)... 
                      destruct (Z.ltb_spec a (sp + Z_of_nat (max_callee_params f + Datatypes.length (locals f) + 1 + sz_a f)))...
                      simpl.
                      destruct (within_dec (sp + Z_of_nat (max_callee_params f + Datatypes.length (locals f) + 1), sz_a f) a)...
                      unfold within in w. simpl in w... }
                erewrite <- hasvalues_match_pub_sep with (lo := sp + locals_ofs f).
                2: {  intros. unfold clear_frame_private. simpl. 
                      destruct (Z.leb_spec sp a)... 
                      destruct (Z.ltb_spec a (sp + Z_of_nat (max_callee_params f + Datatypes.length (locals f) + 1 + sz_a f)))...
                      simpl.
                      destruct (within_dec (sp + Z_of_nat (max_callee_params f + Datatypes.length (locals f) + 1), sz_a f) a)...
                      unfold within in w. simpl in w... }
                erewrite <- hasvalue_match_pub_sep.
                2: { unfold clear_frame_private. simpl. 
                     destruct (Z.leb_spec sp (sp + ra_ofs f))...
                     destruct (Z.ltb_spec (sp + ra_ofs f) (sp + Z_of_nat (max_callee_params f + Datatypes.length (locals f) + 1 + sz_a f)))...
                     simpl.
                     destruct (within_dec (sp + Z_of_nat (max_callee_params f + Datatypes.length (locals f) + 1), sz_a f) (sp + ra_ofs f))...
                     unfold within in w.  simpl in w... }
                erewrite <- heap_contents_unchanged_imp with (vm := vm). 
                2: { pose proof StkHp_disjoint. 
                     intros.  unfold clear_frame_private.  
                     unfold heap_sizes_partition in HSP. 
                     destruct (Z.leb_spec sp a)...  } 
                apply sep_swap56.
                apply sep_swap34.
                apply sep_swap45.
                apply sep_swap23.
                apply sep_swap34.
                apply sep_swap23.
                apply sep_swap... }
        - (* exec_return_control_M *)
          unfold Mem.perturb in H.  simpl in H. unfold perturb' in H. 
          monadInvDep H. inv H. unfold perturb in e. inversion e.  subst a. 
          inv STACK.
          unfold compile_from_retaddr in RAG. 
          unfold stack_contents in SEP. fold stack_contents in SEP.
          destruct retaddrs as [|retaddr retaddrs'] ; [ apply sep_pure in SEP; intuition|].
          sepa_in SEP.
          (* justify the write *)
          edestruct frame_contents_hi_update as [R1 R2]...
          eexists; split...
          + (* execution *) {
              twostep.
              - eapply step_return...
              - econstructor.
                * unfold lea. simpl.  rewrite -> SPv...
                * erewrite offset_arith_ok... inv RVv.  eapply R1.  }
          +  (* matching *) {
              econstructor...
              - inv MSM. econstructor... 
              - rewrite -> Z.add_comm...  
              - replace (sp + Z_of_nat 0) with sp in R2 by lia'. 
                apply sep_swap23 in R2. 
                unfold state_contents... 
                rewrite -> Z.add_comm...
            }
        - (* exec_return_control_OOM *)
          (* this case cannot happen with this oracle *)
          unfold Mem.perturb, oracle, perturb' in H.  
          inv H. 
        - (* exec_builtin_M *)
          destruct mb. 
          (* malloc *)
          + { inv Mbuilt; simpl in H; maybeMonadInv H.  
              unfold hpAlloc' in Heqo. 
              monadInvDep Heqo. 
              destruct a.  inv Heqo. 
              sep_swap_end_in SEP. 
              destruct (hpAlloc_impl_match _ _ _ _ _ _ _ HSP e SEP) as [rv [M' [P1 [P2 P3]]]]. 
              eexists. 
              split.
              + (* execution *) {
                  onestep.
                  eapply step_Mbuiltin. simpl. 
                  unfold Bmalloc_impl. 
                  rewrite SPv.  simpl. 
                  replace (unsigned(val_of_Z sp)) with sp... 
                  2: { unfold val_of_Z.
                       pose proof StkBase_WF. pose proof StkLimit_WF. 
                       inv MSP.  rewrite unsigned_repr... }
                  erewrite lookup_rule_v... 
                  2: { rewrite sep_swap3 in SEP.  apply sep_proj1 in SEP. simpl in SEP. apply sep_proj1 in SEP. eauto. }
                  2: constructor.
                  simpl. 
                  rewrite P1. simpl. eauto. }
              +  (* matching *) {
                  eapply match_Returnstate...
                  - rewrite Regmap.gss. rewrite P2... constructor. 
                  - simpl. erewrite hpAlloc_stk...  
                  - simpl. erewrite hpAlloc_stk...  
                  - rewrite Regmap.gso...
                    inv STACK. econstructor... 
                  - simpl. eapply hpAlloc_partitions... 
                  - simpl.  apply sep_swap3 in P3. simpl hasvalues in P3.
                    rewrite -> sep_assoc in P3.  apply sep_swap in P3. apply sep_pure in P3. destruct P3 as [_ P3].
                    rewrite <- sep_assoc in P3. sep_swap_end.  apply sep_swap.
                    erewrite <- hpAlloc_vmem in P3...
                    destruct cs. 
                    * simpl in P3 |-*.
                      rewrite sep_pure; split; auto. 
                      rewrite sep_assoc in P3. apply sep_swap in P3.  do 2 apply sep_drop in P3.  auto.
                    * simpl in P3 |-*. 
                      destruct retaddrs. 
                      -- rewrite sep_assoc in P3. apply sep_swap in P3.  apply sep_pure in P3. intuition. 
                      -- sepa_in P3.  rewrite sep_swap in P3. 
                         erewrite <- trange_eqv with (mid := sp + 1)... 
                         2: { inv STACK.  simpl in PCNT... }
                         erewrite hasvalue_hasvalues_imp in P3. 
                         rewrite hasvalues_trange_imp in P3.  simpl in P3.  replace (sp + 0) with sp by lia'.
                         rewrite sep_assoc. rewrite sep_assoc. rewrite sep_assoc. auto.
                } 
            }
          (* free *)
          + { inv Mbuilt; simpl in H.  maybeMonadInv H.  
              - (* freeing NULL *)
                eexists. 
                split.
                + (* execution *) {
                    onestep.                          
                    eapply step_Mbuiltin. simpl. unfold Bfree_impl. 
                    rewrite SPv.  simpl. 
                    replace (unsigned(val_of_Z sp)) with sp... 
                    2: { unfold val_of_Z.
                         pose proof StkBase_WF. pose proof StkLimit_WF. 
                         inv MSP.  rewrite unsigned_repr... }
                    erewrite lookup_rule_v... 
                    2: { rewrite sep_swap2 in SEP.  apply sep_proj1 in SEP. simpl in SEP. apply sep_proj1 in SEP. eauto. }
                    2: constructor.
                    simpl. 
                    rewrite e. unfold NULL. rewrite unsigned_zero. rewrite Z.eqb_refl.
                    simpl.  auto. }
                + (* matching *) {
                    eapply match_Returnstate...
                    - rewrite Regmap.gss... constructor.
                    - rewrite Regmap.gso...
                      inv STACK. econstructor... 
                    - apply sep_swap in SEP.
                      destruct cs. 
                      * simpl in SEP |-*.
                        rewrite sep_pure; split; auto. 
                        rewrite sep_assoc in SEP. apply sep_swap in SEP.  do 3 apply sep_drop in SEP.  auto.
                      * simpl in SEP |-*. 
                        destruct retaddrs. 
                        -- rewrite sep_assoc in SEP.  apply sep_swap3 in SEP. apply sep_pure in SEP. intuition.
                        -- sepa_in SEP.  rewrite sep_swap in SEP. 
                           erewrite <- trange_eqv with (mid := sp + 1)... 
                           2: { inv STACK.  simpl in PCNT... }
                           erewrite hasvalue_hasvalues_imp in SEP. 
                           rewrite hasvalues_trange_imp in SEP.  simpl in SEP.  replace (sp + 0) with sp by lia'.
                           apply sep_pure in SEP. destruct SEP as [_ SEP]. apply sep_swap in SEP.
                           rewrite sep_assoc. rewrite sep_assoc. rewrite sep_assoc. auto.
                  } 
              - (* freeing for real  *)
                unfold hpFree' in Heqo. 
                monadInvDep Heqo. 
                inv Heqo. 
                sep_swap_end_in SEP. 
                destruct (hpFree_impl_match _ _ _ _ _ HSP e SEP) as [M' [P1 P2]].  
                eexists. 
                split.
                + (* execution *) {
                    onestep.
                    eapply step_Mbuiltin. simpl. 
                    unfold Bfree_impl. 
                    rewrite SPv.  simpl. 
                    replace (unsigned(val_of_Z sp)) with sp... 
                    2: { unfold val_of_Z.
                         pose proof StkBase_WF. pose proof StkLimit_WF. 
                         inv MSP.  rewrite unsigned_repr... }
                    erewrite lookup_rule_v... 
                    2: { rewrite sep_swap3 in SEP.  apply sep_proj1 in SEP. simpl in SEP. apply sep_proj1 in SEP. eauto. }
                    2: constructor.
                    simpl. 
                    rewrite P1. simpl. 
                    unfold NULL in n.  clear Heqs. rewrite unsigned_zero in n.  
                    destruct (Z.eqb_spec (unsigned v0) 0); try lia'. 
                    simpl.  eauto. }
                +  (* matching *) {
                    eapply match_Returnstate...
                    - rewrite Regmap.gss... constructor.
                    - simpl. erewrite hpFree_stk...  
                    - simpl. erewrite hpFree_stk...  
                    - rewrite Regmap.gso...
                      inv STACK. econstructor... 
                    - simpl. eapply hpFree_partitions... 
                    - simpl.  apply sep_swap3 in P2. simpl hasvalues in P2.
                      rewrite -> sep_assoc in P2.  apply sep_swap in P2. apply sep_pure in P2. destruct P2 as [_ P2].
                      rewrite <- sep_assoc in P2. sep_swap_end.  apply sep_swap.
                      pose proof StkHp_disjoint as SHD.
                      destruct cs. 
                      * simpl in P2 |-*.
                        rewrite sep_pure; split; auto. 
                        rewrite sep_assoc in P2. apply sep_swap in P2.  do 2 apply sep_drop in P2. 
                        erewrite match_pub_sep_unchanged_eqv with (vm' := (vmem (` sM))); eauto.
                        intros. 
                        eapply hpFree_vmem; eauto; lia'.   
                      * simpl in P2 |-*. 
                        destruct retaddrs. 
                        -- rewrite sep_assoc in P2. apply sep_swap in P2.  apply sep_pure in P2. intuition. 
                        -- sepa_in P2.  rewrite sep_swap in P2. 
                           inv STACK. 
                           erewrite <- trange_eqv with (mid := sp + 1)... 
                           2: simpl in PCNT... 
                           erewrite hasvalue_hasvalues_imp in P2. 
                           rewrite hasvalues_trange_imp in P2.  simpl in P2.  replace (sp + 0) with sp by lia'.
                           rewrite sep_assoc. rewrite sep_assoc. rewrite sep_assoc. 
                           erewrite frame_contents_unchanged_eqv with (vm' := (vmem (` sM))); eauto. 
                           2:  intros; eapply hpFree_vmem; eauto; lia'.
                           erewrite stack_contents_unchanged_imp with (vm' := (vmem (` sM))); eauto.
                           2: intros; eapply hpFree_vmem; eauto; lia'. 
                           erewrite match_pub_sep_unchanged_eqv with (vm' := (vmem (` sM))); eauto.
                           intros; eapply hpFree_vmem; eauto; lia'.
                  } 
            }
        - (* exec_builtin_M_Fail *)
          destruct mb. 
          + (* malloc *)
            { inv Mbuilt; simpl in H; maybeMonadInv H. 
              unfold hpAlloc' in Heqo. 
              monadInvDep Heqo.               
              - destruct a. discriminate.
              - destruct sM.  simpl in *.
                sep_swap_end_in SEP. 
                epose proof (hpAlloc_fail_match _ _ _ _ _ HSP e) as [c P]; eauto.
                eexists. 
                split. 
                * { (*execution *)
                    onestep.
                    eapply step_Mbuiltin_FS. simpl. 
                    unfold Bmalloc_impl. 
                    rewrite SPv.  simpl. 
                    replace (unsigned(val_of_Z sp)) with sp... 
                    2: { unfold val_of_Z.
                         pose proof StkBase_WF. pose proof StkLimit_WF. 
                         inv MSP.  rewrite unsigned_repr... }
                    erewrite lookup_rule_v... 
                    2: { rewrite sep_swap3 in SEP.  apply sep_proj1 in SEP. eauto. }
                    2: constructor.
                    simpl. 
                    rewrite P. simpl. eauto.
                  }
                * (* matching *)
                  econstructor. constructor.
            }
          + (* free *)
            { inv Mbuilt; simpl in H; maybeMonadInv H. 
              unfold hpFree' in Heqo.
              monadInvDep Heqo.
              destruct sM.  simpl in *. 
              sep_swap_end_in SEP. 
              epose proof (hpFree_fail_match _ _ _ _ HSP e) as [c P]; eauto.
              eexists. 
              split. 
              * { (*execution *)
                  onestep.
                  eapply step_Mbuiltin_FS. simpl. 
                  unfold Bfree_impl. 
                  rewrite SPv.  simpl. 
                  replace (unsigned(val_of_Z sp)) with sp... 
                  2: { unfold val_of_Z.
                       pose proof StkBase_WF. pose proof StkLimit_WF. 
                       inv MSP.  rewrite unsigned_repr... }
                  erewrite lookup_rule_v... 
                  2: { rewrite sep_swap3 in SEP.  apply sep_proj1 in SEP. eauto. }
                  2: constructor.
                  simpl. 
                  unfold NULL in n.  clear Heqs. rewrite unsigned_zero in n.  
                  destruct (Z.eqb_spec (unsigned v) 0); try lia'. 
                  rewrite P. simpl. eauto.
                }
              * (* matching *)
                econstructor. constructor.
            }
      Qed.
      
      Theorem match_initial: forall S T,
          RTLS.initial_state (oracle prog) prog S -> 
          MacS.initial_state tprog T -> 
          match_states S T. 
      Proof with (eauto with DB; try (unfold_layout; lia')).
        intros.
        inv H. 
        inv H0.
        simpl. 
        inv TRANSL.
        - inv H1. 
        - inv H1. inv H. 
          unfold initial_mem'. 
          econstructor...
          + simpl.  rewrite Pos.eqb_refl. auto.
          + subst B0. rewrite Regmap.gss...
          + eapply StkBaseLimit_WF.
          + rewrite H2; simpl; lia'. 
          + unfold match_sp... 
          + econstructor...
          + rewrite H2. simpl. subst B0. rewrite Regmap.gso... rewrite Regmap.gss...  econstructor. 
          + rewrite H2...
          + pose proof HpBaseLimit_WF. simpl. unfold initial_heap. unfold heap_sizes_partition. hsize.  lia'. 
          + unfold initm.  simpl. 
            sep_swap_end.
            rewrite sep_pure. rewrite sep_pure. rewrite sep_pure.
            do 3 (split;auto).
            apply sep_swap.
            unfold hasvalue. 
            pose proof HpBaseLimit_WF.
            pose proof StkHp_disjoint.
            rewrite Z2Nat.id...  
            unfold sepconj at 1; simpl. 
            split; [|split].
            * split; unfold in_bounds... 
              rewrite Z.eqb_refl. split; simpl...  f_equal; f_equal...
            * unfold sepconj at 1; simpl. 
              split; [|split].
              -- intros. unfold in_bounds. split; [left; auto|].  
                 destruct (Z.eqb_spec a HpBase); subst... 
              -- intros. 
                 split. 
                 ++ unfold in_bounds... 
                 ++ destruct (Z.eqb_spec a HpBase); subst... 
              -- unfold disjoint_footprint. simpl.  intros...
            * unfold disjoint_footprint. unfold contains; simpl.  intros. subst. 
              inv H3;  simpl in H1... 
      Qed.

      Theorem match_final: forall S T v, 
          match_states S T ->
          (RTLS.final_state (oracle prog) S v <->
             MacS.final_state T v).
      Proof.
        intros.
        split.
        - intros.
          inv H0.  inv H.
          inv STACK.
          inv RVv. rewrite H2. 
          econstructor; auto.
        - intros.
          inv H0.  inv H.
          + unfold exit in Mpcs. destruct (transl_instrs map (val_of_Z (Z_of_nat (arr_ofs f))) pc); inv Mpcs.
          + unfold transl_function in MFun. monadInv MFun. simpl in H5. inv H5. 
          + rewrite H1 in RVv. inv RVv.
            inv STACK. 
            * econstructor.
            * unfold compile_from_retaddr in RAG. rewrite H2 in RAG. inv RAG.
      Qed.

      
      Lemma transl_initial_states_ex:
        forall S, RTLS.initial_state (oracle prog) prog S ->
                  exists R, MacS.initial_state tprog R /\ match_states S R.
      Proof.
        intros.
        assert (G: exists R, MacS.initial_state tprog R). 
        { inv H. 
          destruct prog; inv H0. inv TRANSL.
          eexists. econstructor. simpl.  eauto. }
        destruct G as [R P]. 
        eexists R; split; auto. 
        eapply match_initial; eauto.
      Qed.


      Lemma transl_final_states:
        forall S R v,
          match_states S R ->
          RTLS.final_state (oracle prog) S v ->
          exists tv, MacS.final_state R tv /\ match_vals v tv.
      Proof.
        intros. 
        eexists. split. 
        - eapply match_final; eauto.
        - econstructor.
      Qed.


      Lemma transl_error_states:
        forall S R f, match_states S R ->
                      RTLS.failstop_state (oracle prog) S f ->
                      exists tf, MacS.failstop_state R tf /\ match_failures f tf.
      Proof.
        intros.
        inv H0. 
        inv H. 
        eexists. split.
        - econstructor.
        - econstructor.
      Qed.


      Let SrcProg := RTLS.RTL_semantics (SourceMem.oracle prog)  prog.
      Let TgtProg := MacS.Mach_semantics tprog.

      Theorem compiler_FS : forward_simulation SrcProg TgtProg match_vals match_failures.
      Proof with eauto.
        eapply forward_simulation_plus; 
          [ (instantiate (1:= match_states' prog); exact transl_initial_states_ex)
          | exact transl_final_states
          | exact transl_error_states
          | exact transl_step_correct].
      Qed.

      
      (* Our Toplevel correctness theorem *)
      Theorem refinement_for_safe_programs :
        (forall behS, program_behaves SrcProg behS -> not_wrong behS) ->
        forall behT, program_behaves TgtProg behT -> exists behS,
            program_behaves SrcProg behS /\ behaviour_matches match_vals  match_failures behS behT.
      Proof.
        apply backward_simulation_same_safe_behavior,
          forward_to_backward_simulation;
          [ apply compiler_FS
          | apply MacS.deterministic].
      Qed.

      Corollary refinement_for_typed_programs:
        wt_program prog -> 
        forall behT, program_behaves TgtProg behT -> exists behS,
            program_behaves SrcProg behS /\ behaviour_matches match_vals match_failures behS behT.
      Proof.
        intros.
        eapply refinement_for_safe_programs; eauto.
        intros.
        eapply Progress.well_typed_not_wrong; eauto.
      Qed.

      Theorem reverse_refinement_for_safe_programs :
        forall behS,
          program_behaves SrcProg behS -> 
          not_wrong behS -> 
          exists behT,
            program_behaves TgtProg behT /\ behaviour_matches match_vals  match_failures behS behT.
      Proof.
        apply forward_simulation_same_safe_behavior.
        eapply compiler_FS. 
      Qed.

      Corollary reverse_refinement_for_typed_programs:
        wt_program prog -> 
        forall behS,
          program_behaves SrcProg behS -> 
          exists behT,
            program_behaves TgtProg behT /\ behaviour_matches match_vals  match_failures behS behT.
      Proof.
        intros.
        eapply reverse_refinement_for_safe_programs; eauto.
        eapply Progress.well_typed_not_wrong; eauto.
      Qed.
      
    End CORRECTNESS.

  End WithAssumptions.

End    Proofs.


