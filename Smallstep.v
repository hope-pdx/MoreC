(* Modified from CompCert *)

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Relations.
Close Scope Z.
Set Implicit Arguments.


(** * 1 Closures of small step semantics' steps *)


Section CLOSURES.

Variable (genv state: Type) (step : genv -> state -> state -> Prop).

Definition nostep (ge: genv) (s: state) : Prop :=
forall s', ~ step ge s s'.

(** Kleene (reflexive, transitive) closures over steps *)

Inductive star (ge: genv): state -> state -> Prop :=
  | star_refl : forall s,
      star ge s s
  | one_star_star : forall s1 s2 s3,
      step ge s1 s2 -> star ge s2 s3 -> star ge s1 s3.

Lemma star_one: forall ge s1 s2,
  step ge s1 s2 -> star ge s1 s2.
Proof.
  intros. eapply one_star_star; eauto.
  left.
Qed.

Lemma star_two:
  forall ge s1 s2 s3,
  step ge s1 s2 -> step ge s2 s3 ->
  star ge s1 s3.
Proof.
  intros. eapply one_star_star; eauto.
  apply star_one; auto.
Qed.

Lemma star_three:
  forall ge s1 s2 s3 s4,
  step ge s1 s2 -> step ge s2 s3 ->
  step ge s3 s4 -> star ge s1 s4.
Proof.
  intros. eapply one_star_star; eauto.
  eapply star_two; eauto.
Qed.

Lemma star_four:
  forall ge s1 s2 s3 s4 s5,
  step ge s1 s2 -> step ge s2 s3 ->
  step ge s3 s4 -> step ge s4 s5 ->
  star ge s1 s5.
Proof.
  intros. eapply one_star_star; eauto.
  eapply star_three; eauto.
Qed.

Lemma star_trans:
  forall ge s1 s2 (X:star ge s1 s2)
  s3 (Y:star ge s2 s3),
  star ge s1 s3.
Proof with eauto.
  induction 1; intros...
  eapply one_star_star...
Qed.


Lemma star_one_star:
  forall ge s1 s2 s3
  (X:star ge s1 s2) (H:step ge s2 s3),
  star ge s1 s3.
Proof with eauto.
  intros. eapply star_trans;
  [|apply star_one]...
Qed.

(** Irreflexive, transitive closures over steps *)

Inductive plus (ge: genv) : state -> state -> Prop :=
  | one_star_plus: forall s1 s2 s3,
      step ge s1 s2 -> star ge s2 s3 -> plus ge s1 s3.

Lemma plus_one: forall ge s1 s2,
  step ge s1 s2 -> plus ge s1 s2.
Proof.
  intros. apply one_star_plus with s2;[auto|left].
Qed.

Lemma plus_star: forall ge s1 s2,
  plus ge s1 s2 -> star ge s1 s2.
Proof.
  inversion 1; subst.
  eapply one_star_star; eauto.
Qed.

Lemma star_one_plus: forall ge s1 s2 s3
  (X:star ge s1 s2) (H:step ge s2 s3),
  plus ge s1 s3.
Proof.
  intros. inv X; 
  [ apply plus_one
  | eapply one_star_plus, star_one_star
  ]; eauto.
Qed.

Lemma one_plus_plus: forall ge s1 s2 s3
  (H:step ge s1 s2) (X:plus ge s2 s3),
  plus ge s1 s3.
Proof with eauto.
  intros. inv X.
  eapply one_star_plus...
  apply plus_star.
  eapply one_star_plus...
Qed.

Lemma one_one_plus: forall ge s1 s2 s3
  (H:step ge s1 s2) (X:step ge s2 s3),
  plus ge s1 s3.
Proof with eauto.
  intros. econstructor...
  eapply star_one...
Qed.


Lemma plus_one_plus: forall ge s1 s2 s3
  (X:plus ge s1 s2) (H:step ge s2 s3),
  plus ge s1 s3.
Proof with eauto.
  intros. eapply star_one_plus...
  apply plus_star...
Qed.

Lemma plus_star_plus: forall ge s1 s2 s3
  (X:plus ge s1 s2) (Y:star ge s2 s3), plus ge s1 s3.
Proof with eauto.
  intros. inv X...
  econstructor...
  eapply star_trans...
Qed.

Lemma star_plus_plus: forall ge s1 s2 s3
  (X:star ge s1 s2) (Y:plus ge s2 s3), plus ge s1 s3.
Proof with eauto.
  intros. inv Y...
  eapply plus_star_plus;
  [eapply star_one_plus|]...
Qed.

Lemma plus_star_star: forall ge s1 s2 s3,
  plus ge s1 s2 -> star ge s2 s3 -> star ge s1 s3.
Proof with eauto.
  intros. eapply plus_star, plus_star_plus...
Qed.

Lemma star_plus_star: forall ge s1 s2 s3,
  star ge s1 s2 -> plus ge s2 s3 -> star ge s1 s3.
Proof with eauto.
  intros. eapply plus_star, star_plus_plus...
Qed.

Lemma plus_trans: forall ge s1 s2
  (X:plus ge s1 s2) s3 (Y:plus ge s2 s3), plus ge s1 s3.
Proof with eauto.
  intros. eapply plus_star_plus...
  apply plus_star...
Qed.
Definition plus_plus_plus := plus_trans.

Lemma plus_inv: forall ge s1 s2,
  plus ge s1 s2 ->
    step ge s1 s2 \/
    exists s', step ge s1 s' /\ plus ge s' s2.
Proof with eauto.
  inversion 1; subst.
  inversion H1; subst.
  - left...
  - right. exists s3.
    split...
    econstructor...
Qed.

Lemma star_inv: forall ge s1 s2,
  star ge s1 s2 -> s2 = s1 \/ plus ge s1 s2.
Proof.
  induction 1; [left|right];
  econstructor; eauto.
Qed.

Lemma plus_ind2:
  forall ge (P: state -> state -> Prop),
  (forall S1 S2, step ge S1 S2 -> P S1 S2) ->
  (forall S1 S2 S3,
    step ge S1 S2 -> plus ge S2 S3 -> P S2 S3 -> P S1 S3) ->
  forall S1 S2, plus ge S1 S2 -> P S1 S2.
Proof with eauto.
  intros ge P BASE IND.
  assert (forall s1 s2, star ge s1 s2 ->
          forall s0, step ge s0 s1 ->
          P s0 s2).
  induction 1; intros.
  apply BASE...
  eapply IND...
  econstructor...
  intros. inv H0...
Qed.

CoInductive forever (ge: genv): state -> Prop :=
  | forever_intro: forall s1 s2,
      step ge s1 s2 -> forever ge s2 ->
      forever ge s1.

Lemma star_forever: forall ge s1 s2, star ge s1 s2 ->
  forever ge s2 -> forever ge s1.
Proof with eauto.
  induction 1; intros; simpl...
  econstructor...
Qed.

Remark cycle_forever: forall ge st,
  step ge st st -> forever ge st.
Proof.
  intros. cofix X.
  apply (@forever_intro ge st st); assumption.
Qed.

Lemma forever_coinduction_principle:
  forall (ge: genv) (P: state -> Prop),
  (forall st, P st -> exists st', step ge st st' /\ P st') ->
  forall st, P st -> forever ge st.
Proof.
  intros ge P IH. cofix CoIH; intros.
  destruct (IH st H) as [st' [Hstep H']].
  apply forever_intro with st'; auto.
Qed.

Lemma forever_coinduction_principle_plus:
  forall (ge: genv) (P: state -> Prop),
  (forall st, P st -> exists st', plus ge st st' /\ P st') ->
  forall st, P st -> forever ge st.
Proof with auto.
  intros.
  apply forever_coinduction_principle with
    (P := fun st => exists st', star ge st st' /\ P st').
  clear H0 st.
  - intros st [st' [Hstar Hst']].
    inversion Hstar as [|a s1 b]; subst.
    + destruct (H st' Hst') as [st2 [Hplus Hst2]].
      inversion Hplus as [a st1 b H1 H2 A B]; subst a b.
      exists st1. split;[|exists st2]...
    + exists s1 . split;[|exists st']...
  - exists st; split... left.
Qed.


Inductive starN (ge: genv): nat -> state -> state -> Prop :=
  | starN_refl: forall s,
      starN ge O s s
  | starN_step: forall n s s' s'',
      step ge s s' -> starN ge n s' s'' -> starN ge (S n) s s''.

Remark starN_star: forall ge n s s',
  starN ge n s s' -> star ge s s'.
Proof.
  induction 1; econstructor; eauto.
Qed.

Remark star_starN: forall ge s s',
  star ge s s' -> exists n, starN ge n s s'.
Proof.
  induction 1 as [|s1 s2 s3 Hstp Hstr [n IH]];
  [ exists 0
  | exists (S n)];
  econstructor; eauto.
Qed.

Variable A: Type.
Variable order: A -> A -> Prop.

CoInductive forever_N (ge: genv) : A -> state -> Prop :=
  | forever_N_star: forall s1 s2 a1 a2,
      star ge s1 s2 ->
      order a2 a1 ->
      forever_N ge a2 s2 ->
      forever_N ge a1 s1
  | forever_N_plus: forall s1 s2 a1 a2,
      plus ge s1 s2 ->
      forever_N ge a2 s2 ->
      forever_N ge a1 s1.

Hypothesis order_wf: well_founded order.

Lemma forever_N_inv: forall ge a s,
  forever_N ge a s ->
  exists s', exists a',
    step ge s s' /\ forever_N ge a' s'.
Proof with eauto.
  intros ge a0. pattern a0. apply (well_founded_ind order_wf).
  intros. inv H0.
  (* star case *)
  inv H1.
  (* no transition *)
  apply H with a2... auto. auto.
  (* at least one transition *)
  exists s0. exists x. split. auto. eapply forever_N_star...
  (* plus case *)
  inv H1. exists s0; exists a2. split...
  inv H3... eapply forever_N_plus...
  econstructor...
Qed.

Lemma forever_N_forever: forall ge a s,
  forever_N ge a s -> forever ge s.
Proof.
  cofix CoIH; intros.
  destruct (forever_N_inv H) as [s' [a' [P Q]]].
  apply forever_intro with s'. auto.
  apply CoIH with a'; auto.
Qed.

CoInductive forever_plus (ge: genv) : state -> Prop :=
  | forever_plus_intro: forall s1 s2,
      plus ge s1 s2 ->
      forever_plus ge s2 ->
      forever_plus ge s1.

Lemma forever_plus_inv: forall ge s,
  forever_plus ge s ->
  exists s', step ge s s' /\ forever_plus ge s'.
Proof.
  intros. inv H. inv H0. exists s0. split; auto.
  exploit star_inv; eauto. intros [P | R].
  subst. auto. econstructor; eauto.
Qed.

Lemma forever_plus_forever: forall ge s,
  forever_plus ge s -> forever ge s.
Proof.
  cofix COIH; intros.
  destruct (forever_plus_inv H) as [s' [P Q]].
  econstructor; eauto.
Qed.


End CLOSURES.







Record semantics : Type := Semantics_gen {
  state: Type;
  genvtype: Type;
  value: Type;
  error: Type;
  step: genvtype -> state -> state -> Prop;
  initial_state: state -> Prop;
  final_state: state -> value -> Prop;
  error_state: state -> error -> Prop;
  fin_err_disjoint: forall s res err,
    ~(final_state s res /\ error_state s err);
  globalenv: genvtype
}.


Declare Scope smallstep_scope.
Notation " 'Step' L " :=
    (step L (L.(globalenv))) (at level 1) : smallstep_scope.
Notation " 'Star' L " :=
    (star (L.(step)) (L.(globalenv))) (at level 1) : smallstep_scope.
Notation " 'Plus' L " :=
    (plus (L.(step)) (L.(globalenv))) (at level 1) : smallstep_scope.
Notation " 'Nostep' L " :=
    (nostep (L.(step)) (L.(globalenv))) (at level 1) : smallstep_scope.
Notation " 'Forever' L" :=
    (forever (L.(step)) (L.(globalenv))) (at level 1) : smallstep_scope.

Open Scope smallstep_scope.




Record determinate (L: semantics) : Prop := Determinate {
  sd_determ: forall s s1 s2,
    Step L s s1 -> Step L s s2 -> s1 = s2;
  sd_initial_determ: forall s1 s2,
    initial_state L s1 -> initial_state L s2 -> s1 = s2;
  sd_final_nostep: forall s res,
    final_state L s res -> Nostep L s;
  sd_final_determ: forall s r1 r2,
    final_state L s r1 -> final_state L s r2 -> r1 = r2;
  sd_error_nostep: forall s err,
    error_state L s err -> Nostep L s;
  sd_error_determ: forall s e1 e2,
    error_state L s e1 -> error_state L s e2 -> e1 = e2
}.

Section DETERMINACY.
Variable L: semantics.
Hypothesis DET: determinate L.

Lemma star_determinacy:
  forall s s', Star L s s' ->
  forall s'', Star L s s'' -> Star L s' s'' \/ Star L s'' s'.
Proof with eauto.
  induction 1; intros s5;
  [ intros star_s_s5
  | intros star_s1_s5]...
  inv star_s1_s5.
  - right. eapply one_star_star...
  - apply IHstar.
    erewrite (sd_determ DET _ _ _ H H1)...
Qed.

End DETERMINACY.

Definition safe (L: semantics) (s: L.(state)) : Prop :=
  forall s', Star L s s' ->
    (exists res, final_state L s' res)
 \/ (exists err, error_state L s' err)
 \/ (exists s'', Step L s' s'').

Lemma star_safe:
  forall (L: semantics) s s',
  Star L s s' -> safe L s -> safe L s'.
Proof.
  intros L s1 s2 star12 safe1; red;
  intros s3 star23. apply safe1.
  eapply star_trans; eauto.
Qed.


Definition matching_of (A: semantics -> Type) (L1 L2: semantics) := A L1 -> A L2 -> Prop.

Record fsim_properties
      (L1 L2: semantics) (index: Type)
      (order: index -> index -> Prop)
      (match_value :  matching_of value L1 L2)
      (match_error :  matching_of error L1 L2)
      (match_states: (matching_of value L1 L2) ->
                     (matching_of error L1 L2) -> index -> (matching_of state L1 L2))
      : Prop := {
  fsim_order_wf: well_founded order;
  fsim_match_initial_states:
    forall s1, initial_state L1 s1 ->
    exists i, exists s2, initial_state L2 s2 /\ match_states match_value match_error i s1 s2;
  fsim_match_final_states:
    forall i s1 s2 r1,
    match_states match_value match_error i s1 s2 ->
    final_state L1 s1 r1 -> 
    exists r2, final_state L2 s2 r2 /\ match_value r1 r2;
  fsim_match_error_states:
    forall i s1 s2 e1,
    match_states match_value match_error i s1 s2 ->
    error_state L1 s1 e1 ->
    exists e2, error_state L2 s2 e2 /\ match_error e1 e2;
  fsim_simulation:
    forall s1 s1', Step L1 s1 s1' ->
    forall i s2, match_states match_value match_error i s1 s2 ->
    exists i' s2',
      (Plus L2 s2 s2' \/ (Star L2 s2 s2' /\ order i' i))
    /\ match_states match_value match_error i' s1' s2';
}.

Arguments fsim_properties: clear implicits.

Inductive forward_simulation (L1 L2: semantics)
(match_values : matching_of value L1 L2)
(match_errors : matching_of error L1 L2) : Prop :=
  Forward_simulation
      (index: Type)
      (order: index -> index -> Prop)
      (match_states: (matching_of value L1 L2) ->
                     (matching_of error L1 L2) -> index -> (matching_of state L1 L2))
      (props: fsim_properties L1 L2 index order match_values match_errors match_states).

Arguments forward_simulation L1 L2 match_values match_errors : clear implicits.
Arguments Forward_simulation L1 L2 match_values match_errors {index} order match_states props.

Lemma fsim_simulation':
  forall L1 L2 index order match_values match_errors match_states,
  fsim_properties L1 L2 index order match_values match_errors match_states ->
  forall i s1 s1', Step L1 s1 s1' ->
  forall s2, match_states match_values match_errors i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 s2' /\ match_states match_values match_errors i' s1' s2')
  \/ (exists i', order i' i /\ match_states match_values match_errors i' s1' s2).
Proof with eauto.
  intros. exploit fsim_simulation...
  intros [i' [s2' [A B]]]. intuition.
  - left; exists i', s2'...
  - inv H3.
    + right; exists i'...
    + left; exists i', s2'; split... econstructor...
Qed.










Section FORWARD_SIMU_DIAGRAMS.

Variable L1 L2: semantics.

Variable match_values : matching_of value L1 L2.
Variable match_errors : matching_of error L1 L2.
Variable match_states : matching_of value L1 L2 ->
                        matching_of error L1 L2 ->
                        matching_of state L1 L2.

Hypothesis match_initial_states:
  forall s1, initial_state L1 s1 ->
  exists s2, initial_state L2 s2 /\ match_states match_values match_errors s1 s2.

Hypothesis match_final_states:
  forall s1 s2 r1,
  match_states match_values match_errors s1 s2 ->
  final_state L1 s1 r1 ->
  exists r2, final_state L2 s2 r2 /\ match_values r1 r2.

Hypothesis match_error_states:
  forall s1 s2 e1,
  match_states match_values match_errors s1 s2 ->
  error_state L1 s1 e1 ->
  exists e2, error_state L2 s2 e2 /\ match_errors e1 e2.



Section SIMULATION_STAR_WF.
Variable order: state L1 -> state L1 -> Prop.
Hypothesis order_wf: well_founded order.
Hypothesis simulation:
  forall s1 s1', Step L1 s1 s1' ->
  forall s2, match_states match_values match_errors s1 s2 ->
  exists s2',
  (Plus L2 s2 s2' \/ (Star L2 s2 s2' /\ order s1' s1))
  /\ match_states match_values match_errors s1' s2'.

Lemma forward_simulation_star_wf: forward_simulation L1 L2 match_values match_errors.
Proof with eauto.
  apply Forward_simulation with
    (state L1)
    order
    (fun mv me idx s1 s2 => idx = s1 /\ match_states mv me s1 s2)
  . constructor...
  - intros. exploit match_initial_states...
    intros [s2 [A B]]. exists s1, s2...
  - intros * [ ?] ?. edestruct match_final_states...
  - intros * [_ ?] ?. edestruct match_error_states...
  - intros * ? * [-> ?]. exploit simulation...
    intros [s2' [A B]]. exists s1', s2'; intuition auto.
Qed.
End SIMULATION_STAR_WF.



Section SIMULATION_STAR.
Variable measure: state L1 -> nat.
Hypothesis simulation:
  forall s1 s1', Step L1 s1 s1' ->
  forall s2, match_states match_values match_errors s1 s2 ->
  (exists s2', Plus L2 s2 s2' /\ match_states match_values match_errors s1' s2')
  \/ (measure s1' < measure s1 /\ match_states match_values match_errors s1' s2)%nat.

Lemma forward_simulation_star: forward_simulation L1 L2 match_values match_errors.
Proof with eauto.
  apply forward_simulation_star_wf with (ltof _ measure).
  apply well_founded_ltof.
  intros. exploit simulation...
  intros [[s2' [A B]] | [A B]].
  - exists s2'...
  - exists s2; split...
    + right; split... apply star_refl.
Qed.
End SIMULATION_STAR.



Section SIMULATION_PLUS.
Hypothesis simulation:
  forall s1 s1', Step L1 s1 s1' ->
  forall s2, match_states match_values match_errors s1 s2 ->
  exists s2', Plus L2 s2 s2' /\ match_states match_values match_errors s1' s2'.

Lemma forward_simulation_plus: forward_simulation L1 L2 match_values match_errors.
Proof.
  apply forward_simulation_star with (measure := fun _ => O).
  intros. exploit simulation; eauto.
Qed.
End SIMULATION_PLUS.


Section SIMULATION_LOCKSTEP.
Hypothesis simulation:
  forall s1 s1', Step L1 s1 s1' ->
  forall s2, match_states match_values match_errors s1 s2 ->
  exists s2', Step L2 s2 s2' /\ match_states match_values match_errors s1' s2'.

Lemma forward_simulation_lockstep: forward_simulation L1 L2 match_values match_errors.
Proof with eauto.
  apply forward_simulation_plus. intros.
  exploit simulation... intros [s2' [A B]].
  exists s2'; split... apply plus_one...
Qed.
End SIMULATION_LOCKSTEP.



Section SIMULATION_OPT.
Variable measure: state L1 -> nat.
Hypothesis simulation:
  forall s1 s1', Step L1 s1 s1' ->
  forall s2, match_states match_values match_errors s1 s2 ->
  (exists s2', Step L2 s2 s2' /\ match_states match_values match_errors s1' s2')
  \/ (measure s1' < measure s1 /\ match_states match_values match_errors s1' s2)%nat.

Lemma forward_simulation_opt: forward_simulation L1 L2 match_values match_errors.
Proof with eauto.
  apply forward_simulation_star with measure. intros.
  exploit simulation... intros [[s2' [A B]] | [A B]].
  - left; exists s2'; split... apply plus_one...
  - right...
Qed.
End SIMULATION_OPT.


End FORWARD_SIMU_DIAGRAMS.





Section SIMULATION_SEQUENCES.

Context L1 L2 index order match_values match_errors match_states
  (S: fsim_properties L1 L2 index order match_values match_errors match_states).

Lemma simulation_star:
  forall s1 s1', Star L1 s1 s1' ->
  forall i s2, match_states match_values match_errors i s1 s2 ->
  exists i', exists s2', Star L2 s2 s2' /\ match_states match_values match_errors i' s1' s2'.
Proof with eauto.
  induction 1; intros.
  - exists i, s2; split... apply star_refl.
  - exploit fsim_simulation... intros [i' [s2' [A B]]].
    exploit IHstar... intros [i'' [s2'' [C D]]].
    exists i'', s2''; split... eapply star_trans...
    intuition auto. apply plus_star...
Qed.

Lemma simulation_plus:
  forall s1 s1', Plus L1 s1 s1' ->
  forall i s2, match_states match_values match_errors i s1 s2 ->
  (exists i', exists s2', Plus L2 s2 s2' /\ match_states match_values match_errors i' s1' s2')
  \/ (exists i', clos_trans _ order i' i /\ match_states match_values match_errors i' s1' s2).
Proof with eauto.
  induction 1 using plus_ind2; intros.
  - (* base case *)
    exploit fsim_simulation'...
    intros [A | [i' A]].
    + left; auto.
    + right; exists i'; intuition.
  - (* inductive case *)
    exploit fsim_simulation'...
    intros [[i' [s2' [A B]]] | [i' [A B]]].
    + exploit simulation_star;
      [ apply plus_star; eauto
      | eauto
      | ].
      intros [i'' [s2'' [P Q]]].
      left; exists i'', s2''; split...
      eapply plus_star_plus...
    + exploit IHplus...
      intros [[i'' [s2'' [P Q]]] | [i'' [P Q]]].
      * left; exists i'', s2''...
      * right; exists i''; intuition auto.
        eapply t_trans... eapply t_step...
Qed.

Lemma simulation_forever:
  forall i s1 s2,
  Forever L1 s1 -> match_states match_values match_errors i s1 s2 ->
  Forever L2 s2.
Proof with eauto.
  assert (forall i s1 s2,
          Forever L1 s1 -> match_states match_values match_errors i s1 s2 ->
          forever_N (step L2) order (globalenv L2) i s2). {
    cofix COINDHYP; intros.
    inv H. destruct (fsim_simulation S _ _ H1 _ _ H0) as [i' [s2' [A B]]].
    destruct A as [C | [C D]].
    eapply forever_N_plus...
    eapply forever_N_star...
  }
  intros. eapply forever_N_forever...
  eapply fsim_order_wf...
Qed.

End SIMULATION_SEQUENCES.








Record bsim_properties
      (L1 L2: semantics) (index: Type)
      (order: index -> index -> Prop)
      (match_values:  matching_of value L1 L2)
      (match_errors:  matching_of error L1 L2)
      (match_states: (matching_of value L1 L2) ->
                     (matching_of error L1 L2) -> index -> (matching_of state L1 L2))
      : Prop := {
  bsim_order_wf: well_founded order;
  bsim_initial_states_exist:
    forall s1, initial_state L1 s1 -> exists s2, initial_state L2 s2;
  bsim_match_initial_states:
    forall s1 s2, initial_state L1 s1 -> initial_state L2 s2 ->
    exists i s1', initial_state L1 s1' /\ match_states match_values match_errors i s1' s2;
  bsim_match_final_states:
    forall i s1 s2 r2,
    match_states match_values match_errors i s1 s2 ->
    safe L1 s1 -> final_state L2 s2 r2 ->
    exists s1' r1, Star L1 s1 s1' /\ final_state L1 s1' r1 /\ match_values r1 r2;
  bsim_match_error_states:
    forall i s1 s2 e2,
    match_states match_values match_errors i s1 s2 ->
    safe L1 s1 -> error_state L2 s2 e2 ->
    exists s1' e1, Star L1 s1 s1' /\ error_state L1 s1' e1 /\ match_errors e1 e2;
  bsim_progress:
    forall i s1 s2, match_states match_values match_errors i s1 s2 -> safe L1 s1 ->
    (exists res, final_state L2 s2 res) \/
    (exists err, error_state L2 s2 err) \/
    (exists s2', Step L2 s2 s2');
  bsim_simulation:
    forall s2 s2', Step L2 s2 s2' ->
    forall i s1, match_states match_values match_errors i s1 s2 -> safe L1 s1 ->
    exists i' s1',
      (Plus L1 s1 s1' \/ (Star L1 s1 s1' /\ order i' i))
    /\ match_states match_values match_errors i' s1' s2'
}.

Arguments bsim_properties: clear implicits.

Inductive backward_simulation (L1 L2: semantics)
(match_values:  matching_of value L1 L2)
(match_errors:  matching_of error L1 L2) : Prop :=
  Backward_simulation
      (index: Type)
      (order: index -> index -> Prop)
      (match_states: (matching_of value L1 L2) ->
                     (matching_of error L1 L2) -> index -> (matching_of state L1 L2))
      (props: bsim_properties L1 L2 index order match_values match_errors match_states).


Arguments backward_simulation L1 L2 match_values match_errors : clear implicits.


Section FORWARD_TO_BACKWARD.

Context L1 L2 index order match_values match_errors match_states
  (FS: fsim_properties L1 L2 index order match_values match_errors match_states).
Hypothesis L2_determinate: determinate L2.


Inductive f2b_transitions: state L1 -> state L2 -> Prop :=
  | f2b_trans_final: forall s1 s2 s1' r1 r2,
      Star L1 s1 s1' ->
      match_values r1 r2 ->
      final_state L1 s1' r1 ->
      final_state L2 s2  r2 ->
      f2b_transitions s1 s2
  | f2b_trans_error: forall s1 s2 s1' e1 e2,
      Star L1 s1 s1' ->
      match_errors e1 e2 ->
      error_state L1 s1' e1 ->
      error_state L2 s2  e2 ->
      f2b_transitions s1 s2
  | f2b_trans_step: forall s1 s2 s1' s1'' s2' i' i'',
      Star L1 s1 s1' ->
      Step L1 s1' s1'' ->
      Plus L2 s2 s2' ->
      match_states match_values match_errors i'  s1'  s2  ->
      match_states match_values match_errors i'' s1'' s2' ->
      f2b_transitions s1 s2.

Lemma f2b_progress: forall i s1 s2,
  match_states match_values match_errors i s1 s2 -> safe L1 s1 ->
  f2b_transitions s1 s2.
Proof with eauto.
  intros i0; pattern i0.
  apply well_founded_ind with (R := order).
  - eapply fsim_order_wf...
  - intros i REC s1 s2 MATCH SAFE.
    destruct (SAFE s1) as [[res FINAL] | [[err ERROR] | [s1' STEP1]]].
    + apply star_refl.
    + (* final state reached *)
      edestruct fsim_match_final_states as [r2 [FIN2 MV]];
      [exact FS|exact MATCH|exact FINAL|].
      eapply f2b_trans_final;
      [ apply star_refl | | |]...
    + (* error state reached *)
      edestruct fsim_match_error_states as [r2 [FIN2 MV]];
      [exact FS|exact MATCH|exact ERROR|].
      eapply f2b_trans_error;
      [ apply star_refl | | |]...
    + (* L1 can make one step *)
      exploit (fsim_simulation FS)... intros [i' [s2' [A MATCH']]].
      assert (B: Plus L2 s2 s2' \/ (s2' = s2 /\ order i' i)). {
        intuition auto. destruct (star_inv H0); intuition auto. }
      clear A. destruct B as [PLUS2 | [EQ1 ORDER]].
      * eapply f2b_trans_step... apply star_refl.
      * subst. exploit REC...
        --eapply star_safe... apply star_one...
        --intros TRANS; inv TRANS.
          ++eapply f2b_trans_final... eapply one_star_star...
          ++eapply f2b_trans_error... eapply one_star_star...
          ++eapply f2b_trans_step...  eapply one_star_star...
Qed.



Lemma f2b_determinacy_inv:
  forall s2 s2' s2'',
  Step L2 s2 s2' -> Step L2 s2 s2'' ->
  s2' = s2''.
Proof with eauto.
  intros. eapply sd_determ...
Qed.


Inductive f2b_index : Type :=
  | F2BI_before (n: nat)
  | F2BI_after (n: nat).

Inductive f2b_order: f2b_index -> f2b_index -> Prop :=
  | f2b_order_before: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_before n') (F2BI_before n)
  | f2b_order_after: forall n n',
      (n' < n)%nat ->
      f2b_order (F2BI_after n') (F2BI_after n)
  | f2b_order_switch: forall n n',
      f2b_order (F2BI_before n') (F2BI_after n).

Lemma wf_f2b_order:
  well_founded f2b_order.
Proof with auto.
  assert (ACC1: forall n, Acc f2b_order (F2BI_before n)). {
    intros n; pattern n; apply lt_wf_ind; intros.
    constructor; intros. inv H0... }
  assert (ACC2: forall n, Acc f2b_order (F2BI_after n)). {
    intros n; pattern n; apply lt_wf_ind; intros.
    constructor; intros. inv H0... }
  intros []...
Qed.

Inductive f2b_match_states: f2b_index -> state L1 -> state L2 -> Prop :=
  | f2b_match_at: forall i s1 s2,
      match_states match_values match_errors i s1 s2 ->
      f2b_match_states (F2BI_after O) s1 s2
  | f2b_match_after: forall n s2 s2a s1 i,
      starN (step L2) (globalenv L2) (S n) s2 s2a ->
      match_states match_values match_errors i s1 s2a ->
      f2b_match_states (F2BI_after (S n)) s1 s2.

Remark f2b_match_after':
  forall n s2 s2a s1 i,
  starN (step L2) (globalenv L2) n s2 s2a ->
  match_states match_values match_errors i s1 s2a ->
  f2b_match_states (F2BI_after n) s1 s2.
Proof with eauto.
  intros. inv H.
  - econstructor...
  - econstructor... econstructor...
Qed.


Lemma f2b_simulation_step:
  forall s2 s2', Step L2 s2 s2' ->
  forall i s1, f2b_match_states i s1 s2 -> safe L1 s1 ->
  exists i' s1',
    (Plus L1 s1 s1' \/ (Star L1 s1 s1' /\ f2b_order i' i))
     /\ f2b_match_states i' s1' s2'.
Proof with eauto.
  intros s2 s2' STEP2 i s1 MATCH SAFE. inv MATCH.
  - exploit f2b_progress... intros TRANS; inv TRANS.
    + (* 1.1 L1 can reach final state and
         L2 is at final state: impossible! *)
      exploit (sd_final_nostep L2_determinate)...
      contradiction.
    + exploit (sd_error_nostep L2_determinate)...
      contradiction.
    + (* 1.2 L1 can make 0 or more steps; L2
         can make 1 or more matching steps *)
      inv H2. exploit f2b_determinacy_inv;
      [ eexact H5
      | eexact STEP2
      | intros <-].
      destruct (star_starN H6) as [n STEPS2].
      exists (F2BI_after n); exists s1''; split.
      left.
      * eapply star_one_plus...
      * eapply f2b_match_after'...
  - inv H. exploit f2b_determinacy_inv;
    [ eexact H2
    | eexact STEP2| intros <-].
    exists (F2BI_after n), s1; split.
    + right; split.
      * apply star_refl.
      * repeat constructor.
    + eapply f2b_match_after'...
Qed.

End FORWARD_TO_BACKWARD.

Lemma forward_to_backward_simulation:
  forall L1 L2 match_values match_errors,
  forward_simulation L1 L2 match_values match_errors -> determinate L2 ->
  backward_simulation L1 L2 match_values match_errors.
Proof with eauto.
  intros L1 L2 mv me [index order ms FS] L2D.
  eapply Backward_simulation with
    (order := f2b_order)
    (match_states := fun mv' me' => (@f2b_match_states L1 L2 index mv' me' ms)).
  constructor.
  - (* well founded *)
    apply wf_f2b_order.
  - (* initial states exist *)
    intros. exploit (fsim_match_initial_states FS)...
    intros [i [s2 [A B]]]. exists s2...
  - (* initial states *)
    intros. exploit (fsim_match_initial_states FS)...
    intros [i [s2' [A B]]]. replace s2' with s2 in *
      by (eapply sd_initial_determ; eauto).
    exists (F2BI_after O), s1. split...
    econstructor...
  - (* final states *)
    intros. inv H.
    + exploit f2b_progress... intros TRANS; inv TRANS.
      * erewrite (sd_final_determ L2D _ _ _ H1 H5)...
      * exfalso; eapply fin_err_disjoint...
      * exfalso. inv H4.
        eapply (sd_final_nostep L2D _ _ H1)...
    + exfalso. inv H2.
      eapply (sd_final_nostep L2D _ _ H1)...
  - (* error states *)
    intros. inv H.
    + exploit f2b_progress... intros TRANS; inv TRANS.
      * exfalso; eapply fin_err_disjoint...
      * erewrite (sd_error_determ L2D _ _ _ H1 H5)...
      * exfalso. inv H4.
        eapply (sd_error_nostep L2D)...
    + exfalso. inv H2.
      eapply (sd_error_nostep L2D)...
  - (* progress *)
    intros. inv H.
    + exploit f2b_progress... intro TRANS; inv TRANS;
      [ left; exists r2
      | right; left
      | right; inv H3]...
    + inv H1...
  - (* simulation *)
    eapply f2b_simulation_step...
Qed.

