(* Modified from Compert *)

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

Require Import Classical
               ClassicalEpsilon
               Program.
Require Import Coqlib Smallstep.

Create HintDb semMetaThy.


Inductive behaviour {value error: Type} : Type :=
  | Terminates: value -> behaviour
  | Faultstops: error -> behaviour
  | Diverges: behaviour
  | Goes_wrong: behaviour.

Inductive state_behaves (L: semantics) (s: state L)
  : behaviour -> Prop :=
  | state_terminates: forall s' res,
      Star L s s' -> final_state L s' res ->
      state_behaves L s (Terminates res)
  | state_fstops: forall s' err,
      Star L s s' -> error_state L s' err ->
      state_behaves L s (Faultstops err)
  | state_diverges: forall s',
      Star L s s' -> Forever L s' ->
      state_behaves L s Diverges
  | state_goes_wrong: forall s',
      Star L s s' ->
      Nostep L s' ->
      (forall res, ~final_state L s' res) ->
      (forall err, ~error_state L s' err) ->
      state_behaves L s Goes_wrong.

Definition not_wrong {value error: Type}
                     (beh: @behaviour value error) :=
  match beh with
  | Goes_wrong => False
  | _          => True
  end.

Definition behaviour_matches
  {v1 e1 v2 e2: Type}
  (mv: v1 -> v2 -> Prop)
  (me: e1 -> e2 -> Prop)
  (beh1: @behaviour v1 e1)
  (beh2: @behaviour v2 e2) : Prop :=
  match beh1, beh2 with
  | Diverges  , Diverges
  | Goes_wrong, Goes_wrong => True
  | Terminates res1, Terminates res2 => mv res1 res2
  | Faultstops err1, Faultstops err2 => me err1 err2
  | _, _ => False
  end.

Definition behaviour_improves
  {v1 e1 v2 e2: Type}
  (mv: v1 -> v2 -> Prop)
  (me: e1 -> e2 -> Prop)
  (beh1: @behaviour v1 e1)
  (beh2: @behaviour v2 e2) : Prop :=
  match beh1, beh2 with
  | Goes_wrong, _
  | Diverges  , Diverges => True
  | Terminates res1, Terminates res2 => mv res1 res2
  | Faultstops err1, Faultstops err2 => me err1 err2
  | _, _ => False
  end.

#[export] Hint Unfold behaviour_matches behaviour_improves : semMetaThy.

Lemma matching_behaviour_improves:
  forall
  {v1 e1 v2 e2: Type}
  (mv: v1 -> v2 -> Prop)
  (me: e1 -> e2 -> Prop)
  (beh1: @behaviour v1 e1)
  (beh2: @behaviour v2 e2),
  @behaviour_matches  v1 e1 v2 e2 mv me beh1 beh2 ->
  @behaviour_improves v1 e1 v2 e2 mv me beh1 beh2.
Proof ltac:(
  destruct beh1, beh2; simpl;auto).

Lemma behaviour_improves_refl:
  forall {v e: Type}
  (mv: v -> v -> Prop)
  (me: e -> e -> Prop) beh,
  (forall x, mv x x) ->
  (forall x, me x x) ->
  @behaviour_improves v e v e mv me beh beh.
Proof with auto with semMetaThy.
  destruct beh; intros mv_refl me_refl...
Qed.

Lemma behaviour_improves_trans:
  forall {v1 e1 v2 e2 v3 e3: Type}
  (mv12: v1 -> v2 -> Prop)
  (me12: e1 -> e2 -> Prop)
  (mv23: v2 -> v3 -> Prop)
  (me23: e2 -> e3 -> Prop)
    (beh1: @behaviour v1 e1)
    (beh2: @behaviour v2 e2)
    (beh3: @behaviour v3 e3),
  @behaviour_improves v1 e1 v2 e2 mv12 me12 beh1 beh2 ->
  @behaviour_improves v2 e2 v3 e3 mv23 me23 beh2 beh3 ->
  @behaviour_improves v1 e1 v3 e3 (fun x1 x3 => exists x2, mv12 x1 x2 /\ mv23 x2 x3)
(fun x1 x3 => exists x2, me12 x1 x2 /\ me23 x2 x3)
 beh1 beh3.
Proof with auto.
  destruct beh1, beh2, beh3;
  try solve [inversion 1|auto with semMetaThy];
  unfold behaviour_improves in *; intros.
  - exists v0...
  - exists e0...
Qed.


Section PROGRAM_BEHAVIOURS.
Variable L: semantics.

Inductive program_behaves: behaviour -> Prop :=
  | program_runs: forall s beh,
      initial_state L s -> state_behaves L s beh ->
      program_behaves beh
  | program_goes_initially_wrong:
      (forall s, ~initial_state L s) ->
      program_behaves Goes_wrong.


Lemma diverges_forever:
  forall s0,
  (forall s1, Star L s0 s1 ->
   exists s2, Step L s1 s2) ->
  Forever L s0.
Proof with eauto.
  cofix COINDHYP; intros.
  destruct (H s0) as [s1 ST].
  - constructor.
  - econstructor...
    apply COINDHYP. intros.
    eapply H. eapply one_star_star...
Qed.

Lemma state_behaves_exists:
  forall s, exists beh, state_behaves L s beh.
Proof with eauto; try econstructor; eauto.
  intros s0.
  destruct (classic
    (forall s1, Star L s0 s1 ->
     exists s2, Step L s1 s2)).
  - exists Diverges. econstructor;
    [ econstructor
    | apply diverges_forever]...
  - destruct (not_all_ex_not _ _ H)
      as [s1 A]; clear H.
    destruct (not_all_ex_not _ _ A)
      as [t1 H]; clear A.
    destruct (classic
      (exists r, final_state L s1 r))
      as [[r FINAL] | NOTFINAL].
    + exists (Terminates r)...
    + destruct (classic
        (exists e, error_state L s1 e))
        as [[e ERR] | NOTERR].
      * exists (Faultstops e)...
      * exists Goes_wrong...
        intros s'.
        exact (not_ex_all_not _ _ H s').
Qed.

Theorem program_behaves_exists:
  exists beh, program_behaves beh.
Proof with eauto.
  destruct (classic
    (exists s, initial_state L s))
    as [[s0 INIT] | NOTINIT].
(* 1. Initial state is defined. *)
  - destruct (state_behaves_exists s0) as [beh SB].
    exists beh; econstructor...
(* 2. Initial state is undefined *)
  - exists Goes_wrong.
    apply program_goes_initially_wrong.
    intros. eapply not_ex_all_not...
Qed.

Theorem program_behaves_one_of_four:
  (exists v, program_behaves (Terminates v)) \/
  (exists e, program_behaves (Faultstops e)) \/
  program_behaves Diverges \/
  program_behaves Goes_wrong.
Proof with eauto.
  destruct program_behaves_exists as [[] ?];
  [
  | right
  | right; right
  | right; right; right]...
Qed.


End PROGRAM_BEHAVIOURS.


Section FORWARD_SIMULATIONS.

Context L1 L2 index order match_values match_errors match_states
  (S: fsim_properties L1 L2 index order match_values match_errors match_states).


Local Notation b_improvs :=
(@behaviour_improves
  (value L1) (error L1)
  (value L2) (error L2)
  match_values match_errors).

Lemma forward_simulation_state_behaves:
  forall i s1 s2 beh1,
  match_states match_values match_errors i s1 s2 -> state_behaves L1 s1 beh1 ->
  exists beh2, state_behaves L2 s2 beh2
            /\ b_improvs beh1 beh2.
Proof with eauto.
  intros. inv H0.
  - (* termination *)
    exploit simulation_star... intros [i' [s2' [A B]]].
    exploit fsim_match_final_states... intros [res2 [FIN2 MV2]].
    exists (Terminates res2). split; [econstructor|]...
  - (* fault stop *)
    exploit simulation_star... intros [i' [s2' [A B]]].
    exploit fsim_match_error_states... intros [err2 [ERS2 ME2]].
    exists (Faultstops err2). split; [econstructor|]...
  - (* divergence *)
    exploit simulation_star... intros [i' [s2' [A B]]].
    exploit simulation_forever... intros.
    exists Diverges; split; simpl... econstructor...
  - (* going wrong *)
    exploit simulation_star... intros [i' [s2' [A B]]].
    destruct (state_behaves_exists L2 s2) as [beh' SB].
    exists beh'; split; simpl...
Qed.


End FORWARD_SIMULATIONS.


Theorem forward_simulation_behavior_improves:
  forall L1 L2 mv me,
  forward_simulation L1 L2 mv me ->
  forall beh1, program_behaves L1 beh1 ->
  exists beh2, program_behaves L2 beh2
  /\ behaviour_improves mv me beh1 beh2.
Proof with eauto.
  do 2 (inversion 1; subst).
  - (* initial state defined *)
    exploit (fsim_match_initial_states props)... intros [i [s' [INIT MATCH]]].
    exploit forward_simulation_state_behaves... intros [beh2 [SB Bimpl]].
    exists beh2; split... * econstructor...
  - (* initial state undefined *)
    destruct (classic (exists s', initial_state L2 s')) as
    [[s' INIT]| noINIT].
    + destruct (state_behaves_exists L2 s') as [beh' SB].
      exists beh'; split; simpl... * econstructor...
    + exists Goes_wrong; split; simpl...
      * apply program_goes_initially_wrong.
        intros * ?. apply noINIT; exists s...
Qed.


Corollary forward_simulation_same_safe_behavior:
  forall L1 L2 mv me,
  forward_simulation L1 L2 mv me ->
  forall beh1, program_behaves L1 beh1 ->
  not_wrong beh1 ->
    exists beh2, program_behaves L2 beh2
 /\ behaviour_matches mv me beh1 beh2.
Proof with eauto.
  intros.
  exploit forward_simulation_behavior_improves...
  intros [beh2 [A B]]. exists beh2; split...
  destruct beh1, beh2...
Qed.



Section BACKWARD_SIMULATIONS.

Context L1 L2 index order match_values match_errors match_states
    (S: bsim_properties L1 L2 index order match_values match_errors match_states).


Remark not_safe:
  forall s,
  ~ safe L1 s ->
  exists s',
     Star L1 s s'
  /\ Nostep L1 s'
  /\ (forall r, ~final_state L1 s' r)
  /\ (forall e, ~error_state L1 s' e).
Proof with eauto.
  intros.
  destruct (not_all_ex_not _ _ H) as [s' A]; clear H.
  destruct (not_all_ex_not _ _ A) as [B C]; clear A.
  destruct (not_or_and _ _ C) as [P Q]; clear C.
  exists s'. repeat split...
  - intros s''' ?. apply Q...
Qed.

Lemma backward_simulation_star:
  forall s2 s2', Star L2 s2 s2' ->
  forall i s1, match_states match_values match_errors i s1 s2 -> safe L1 s1 ->
  exists i', exists s1', Star L1 s1 s1'
          /\ match_states match_values match_errors i' s1' s2'.
Proof with eauto.
  induction 1; intros.
  - exists i, s1; split... apply star_refl.
  - exploit (bsim_simulation S)...
    intros [i' [s1' [A B]]].
    assert (Star L1 s0 s1'). {
      intuition.  apply plus_star...
    }
    exploit IHstar...
    + eapply star_safe...
    + intros [i'' [s2'' [C D]]].
      exists i'', s2''; split...
      eapply star_trans...
Qed.

Lemma backward_simulation_forever:
  forall i s1 s2,
  Forever L2 s2 -> match_states match_values match_errors i s1 s2 ->
  safe L1 s1 -> Forever L1 s1.
Proof with eauto.
  assert
  (forall i s1 s2,
    Forever L2 s2 -> match_states match_values match_errors i s1 s2 -> safe L1 s1 ->
    forever_N (step L1) order (globalenv L1) i s1). {
      cofix COINDHYP; intros. inv H.
      destruct (bsim_simulation S _ _ H2 _ H0 H1)
        as [i' [s2' [A B]]].
      destruct A as [C | [C D]].
      eapply forever_N_plus...
      eapply COINDHYP...
      eapply star_safe...
      apply plus_star...
      eapply forever_N_star...
      eapply COINDHYP...
      eapply star_safe... }
  intros.
  eapply forever_N_forever...
  eapply bsim_order_wf...
Qed.


Lemma backward_simulation_state_behaves:
  forall i s1 s2 beh2,
  match_states match_values match_errors i s1 s2 -> state_behaves L2 s2 beh2 ->
  exists beh1, state_behaves L1 s1 beh1
            /\ behaviour_improves match_values match_errors beh1 beh2.
Proof with eauto with semMetaThy.
  intros. destruct (classic (safe L1 s1)).
  - (* 1. Safe *)
    inv H0;
    exploit backward_simulation_star; eauto;
    intros [i' [s1' [A B]]].
    + (* termination *)
      exploit (bsim_match_final_states S)...
      * eapply star_safe...
      * intros [s1'' [res1 [D [FIN MV]]]].
        exists (Terminates res1); split;
        [ eapply (state_terminates _ _ _ _ (star_trans A D) FIN)
        | ]...
    + (* fault stop *)
      exploit (bsim_match_error_states S)...
      * eapply star_safe...
      * intros [s1'' [err1 [C [ERR ME]]]].
        exists (Faultstops err1); split;
        [ eapply (state_fstops _ _ _ _ (star_trans A C) ERR)
        | ]...
    + (* divergence *)
      exists Diverges; split;
      [ econstructor;
        [ exact A
        | eapply backward_simulation_forever, star_safe]
      |]...
    + (* goes wrong *)
      exploit (bsim_progress S)...
      * eapply star_safe...
      * intros [[r FIN] | [[e ERROR] | [s2' STEP2]]]; exfalso;
        [ exact (H4 _ FIN)
        | exact (H5 _ ERROR)
        | exact (H3 _ STEP2)].
  - (* 2. Not safe along *)
    exploit not_safe...
    intros [s1' [STEPS [NOSTEP [NOFIN NOERR]]]].
    exists Goes_wrong; split;
    [ econstructor
    | simpl ]...
Qed.

End BACKWARD_SIMULATIONS.

Theorem backward_simulation_behavior_improves:
  forall L1 L2 mv me, backward_simulation L1 L2 mv me ->
  forall beh2, program_behaves L2 beh2 ->
  exists beh1, program_behaves L1 beh1
 /\ behaviour_improves mv me beh1 beh2.
Proof with eauto.
  intros * S beh2 H.
  destruct S as [index order match_states S]. inv H.
  - (* L2's initial state is defined. *)
    destruct (classic (exists s1, initial_state L1 s1))
      as [[s1 INIT] | NOINIT].
    + (* L1's initial state is defined too. *)
      exploit (bsim_match_initial_states S)...
      intros [i [s1' [INIT1' MATCH]]].
      exploit backward_simulation_state_behaves...
      intros [beh1 [A B]]. exists beh1; split...
      econstructor...
    + (* L1 has no initial state *)
      exists Goes_wrong; split.
      * apply program_goes_initially_wrong.
        intros * ?. destruct NOINIT. exists s0...
      * simpl...
  - (* L2 has no initial state *)
    exists Goes_wrong; split.
    + apply program_goes_initially_wrong. intros * INIT1.
      exploit (bsim_initial_states_exist S)...
      intros [s2 INIT2]. destruct (H0 s2)...
    + simpl...
Qed.

Corollary backward_simulation_same_safe_behavior:
  forall L1 L2 mv me, backward_simulation L1 L2 mv me ->
  (forall beh, program_behaves L1 beh -> not_wrong beh) ->
  (forall beh2, program_behaves L2 beh2 -> exists beh1,
  program_behaves L1 beh1 /\ behaviour_matches mv me beh1 beh2).
Proof with eauto.
  intros.
  exploit backward_simulation_behavior_improves...
  intros [beh [A B]]. pose proof (H0 _ A) as C.
  exists beh; split...
  destruct beh, beh2; simpl in *; try solve [inv B|inv C]...
Qed.
