(* Modified from CompCert *)


(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris                                  *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Assertions on memory states, in the style of separation logic *)

(** This library defines a number of useful logical assertions about
  CompCert memory states, such as "block [b] at offset [ofs] contains
  value [v]".  Assertions can be grouped using a separating conjunction
  operator in the style of separation logic.

  Currently, this library is used only in module [Stackingproof]
  to reason about the shapes of stack frames generated during the
  [Stacking] pass.

  This is not a full-fledged separation logic because there is no
  program logic (Hoare triples) to speak of.  Also, there is no general
  frame rule; instead, a weak form of the frame rule is provided
  by the lemmas that help us reason about the logical assertions. *)

Require Import Setoid Program.Basics.
Require Import Coqlib. 
Require Import Defns Mem.
Require Import Mach.

Module Type MachSemanticsType (Import mparams:MachParameters).
  Include Mach.Semantics(mparams). 
End MachSemanticsType. 


Module Separation (Import mparams: MachParameters) (Import MacS: MachSemanticsType(mparams)).


(** * Assertions about (machine) memory *)

(** An assertion is composed of:
- a predicate over memory states (of type [mem -> Prop])
- a set of addrs that represents the memory footprint of the assertion
- a proof that the predicate is invariant by changes of memory outside of the footprint
- a proof that the footprint contains only valid addrs.

This presentation (where the footprint is part of the assertion) makes
it possible to define separating conjunction without explicitly
defining a separation algebra over CompCert memory states (i.e. the
notion of splitting a memory state into two disjoint halves).  *)

  Local Open Scope Z.

  Definition unchanged_on (in_footprint: Z -> Prop) (m m': mmem) :=
    forall a, in_footprint a -> m a = m' a. 

  Lemma unchanged_on_refl:
    forall P m, unchanged_on P m m.
  Proof.
    intros; constructor. 
  Qed.

  Lemma unchanged_on_implies:
    forall (P Q: Z -> Prop) m m',
      unchanged_on P m m' ->
      (forall a, Q a -> P a) -> 
      unchanged_on Q m m'.
  Proof.
    intros. unfold unchanged_on in *.  intros. eauto. 
  Qed.

  Record massert : Type := {
      m_pred : mmem -> Prop;
      m_footprint: Z -> Prop;
      m_invar: forall m m', m_pred m -> unchanged_on m_footprint m m' -> m_pred m';
      m_valid: forall m a, m_pred m -> m_footprint a -> in_bounds a; 
    }.

  Declare Scope sep_scope.

  Notation "m |= p" := (m_pred p m) (at level 74, no associativity) : sep_scope.

  (** Implication and logical equivalence between memory predicates *)

  Definition massert_imp (P Q: massert) : Prop :=
    (forall m, m_pred P m -> m_pred Q m) /\ (forall a, m_footprint Q a -> m_footprint P a).
  Definition massert_eqv (P Q: massert) : Prop :=
    massert_imp P Q /\ massert_imp Q P.

  Remark massert_imp_refl: forall p, massert_imp p p.
  Proof.
    unfold massert_imp; auto.
  Qed.

  Remark massert_imp_trans: forall p q r, massert_imp p q -> massert_imp q r -> massert_imp p r.
  Proof.
    unfold massert_imp; intros; firstorder auto.
  Qed.

  Remark massert_eqv_refl: forall p, massert_eqv p p.
  Proof.
    unfold massert_eqv, massert_imp; intros. tauto.
  Qed.

  Remark massert_eqv_sym: forall p q, massert_eqv p q -> massert_eqv q p.
  Proof.
    unfold massert_eqv, massert_imp; intros. tauto.
  Qed.

  Remark massert_eqv_trans: forall p q r, massert_eqv p q -> massert_eqv q r -> massert_eqv p r.
  Proof.
    unfold massert_eqv, massert_imp; intros. firstorder auto.
  Qed.

  (** Record [massert_eqv] and [massert_imp] as relations so that they can be used by rewriting tactics. *)
  Add Relation massert massert_imp
      reflexivity proved by massert_imp_refl
      transitivity proved by massert_imp_trans
      as massert_imp_prel.

  Add Relation massert massert_eqv
      reflexivity proved by massert_eqv_refl
      symmetry proved by massert_eqv_sym
      transitivity proved by massert_eqv_trans
      as massert_eqv_prel.

  Add Morphism m_pred
      with signature massert_imp ==> eq ==> impl
        as m_pred_morph_1.
  Proof.
    intros P Q [A B]. auto.
  Qed.

  Add Morphism m_pred
      with signature massert_eqv ==> eq ==> iff
        as m_pred_morph_2.
  Proof.
    intros P Q [[A B] [C D]]. split; auto.
  Qed.

  Global Hint Resolve massert_imp_refl massert_eqv_refl : sep.

  Add Morphism m_footprint 
      with signature massert_eqv ==> eq ==> iff
        as m_footprint_morph_2.
  Proof.
    intros P Q [[A B] [C D]]. split; auto.
  Qed.


  (** * Separating conjunction *)

  Definition disjoint_footprint (P Q: massert) : Prop :=
    forall a, m_footprint P a -> m_footprint Q a  -> False.

  Program Definition sepconj (P Q: massert) : massert := {|
    m_pred := fun m => m_pred P m /\ m_pred Q m /\ disjoint_footprint P Q;
    m_footprint := fun a => m_footprint P a \/ m_footprint Q a
  |}.
  Next Obligation.
    repeat split; auto.
    - apply (m_invar P) with m; auto. eapply unchanged_on_implies; eauto. simpl; auto.
    - apply (m_invar Q) with m; auto. eapply unchanged_on_implies; eauto. simpl; auto.
  Qed.
  Next Obligation.
    destruct H0; [eapply (m_valid P) | eapply (m_valid Q)]; eauto.
  Qed.

  Add Morphism sepconj
      with signature massert_imp ==> massert_imp ==> massert_imp
        as sepconj_morph_1.
  Proof.
    intros P1 P2 [A B] Q1 Q2 [C D].
    red; simpl; split; intros.
    - intuition auto. red; intros. apply (H2 a); auto. 
    - intuition auto.
  Qed.

  Add Morphism sepconj
      with signature massert_eqv ==> massert_eqv ==> massert_eqv
        as sepconj_morph_2.
  Proof.
    intros. destruct H, H0. split; apply sepconj_morph_1; auto.
  Qed.

  Infix "**" := sepconj (at level 60, right associativity) : sep_scope.

  Local Open Scope sep_scope.

  Lemma sep_imp:
    forall P P' Q Q' m,
      m |= P ** Q -> massert_imp P P' -> massert_imp Q Q' -> m |= P' ** Q'.
  Proof.
    intros. rewrite <- H0, <- H1; auto.
  Qed.

  Lemma sep_cancel: forall P Q,
      massert_imp P Q ->
      forall R, massert_imp (R ** P) (R ** Q). 
  Proof.
    intros. unfold massert_imp in *. 
    inv H.
    split; intros.
    - unfold sepconj in *; simpl in *.
      destruct H as [J1 [J2 J3]].
      split; auto.
      split; auto. 
      unfold disjoint_footprint in *.  intros.
      eapply J3; eauto. 
    - unfold sepconj in *; simpl in *. 
      intuition.
  Qed.

  Lemma sep_comm_1:
    forall P Q,  massert_imp (P ** Q) (Q ** P).
  Proof.
    unfold massert_imp; simpl; split; intros.
    - intuition auto. red; intros; eapply H2; eauto.
    - intuition auto.
  Qed.

  Lemma sep_comm:
    forall P Q, massert_eqv (P ** Q) (Q ** P).
  Proof.
    intros; split; apply sep_comm_1.
  Qed.

  Lemma sep_assoc_1:
    forall P Q R, massert_imp ((P ** Q) ** R) (P ** (Q ** R)).
  Proof.
    intros. unfold massert_imp, sepconj, disjoint_footprint; simpl; firstorder auto.
  Qed.

  Lemma sep_assoc_2:
    forall P Q R, massert_imp (P ** (Q ** R)) ((P ** Q) ** R).
  Proof.
    intros. unfold massert_imp, sepconj, disjoint_footprint; simpl; firstorder auto.
  Qed.

  Lemma sep_assoc:
    forall P Q R, massert_eqv ((P ** Q) ** R) (P ** (Q ** R)).
  Proof.
    intros; split. apply sep_assoc_1. apply sep_assoc_2.
  Qed.

  Lemma sep_swap:
    forall P Q R, massert_eqv (P ** Q ** R) (Q ** P ** R).
  Proof.
    intros. rewrite <- sep_assoc. rewrite (sep_comm P). rewrite sep_assoc. reflexivity.
  Qed.

  Definition sep_swap12 := sep_swap.

  Lemma sep_swap23:
    forall P Q R S, massert_eqv (P ** Q ** R ** S) (P ** R ** Q ** S).
  Proof.
    intros. rewrite (sep_swap Q). reflexivity.
  Qed.

  Lemma sep_swap34:
    forall P Q R S T, massert_eqv (P ** Q ** R ** S ** T) (P ** Q ** S ** R ** T).
  Proof.
    intros. rewrite (sep_swap R). reflexivity.
  Qed.

  Lemma sep_swap45:
    forall P Q R S T U, massert_eqv (P ** Q ** R ** S ** T ** U) (P ** Q ** R ** T ** S ** U).
  Proof.
    intros. rewrite (sep_swap S). reflexivity.
  Qed.

  Lemma sep_swap56:
    forall P Q R S T U V, massert_eqv (P ** Q ** R ** S ** T ** U ** V) (P ** Q ** R ** S ** U ** T ** V).
  Proof.
    intros. rewrite (sep_swap T). reflexivity.
  Qed.

  Lemma sep_swap67:
    forall P Q R S T U V W, massert_eqv (P ** Q ** R ** S ** T ** U ** V ** W) (P ** Q ** R ** S ** T ** V ** U ** W).
  Proof.
    intros. rewrite (sep_swap U). reflexivity.
  Qed.

  Lemma sep_swap78:
    forall P Q R S T U V W X, massert_eqv (P ** Q ** R ** S ** T ** U ** V ** W ** X) (P ** Q ** R ** S ** T ** U ** W ** V ** X).
  Proof.
    intros. rewrite (sep_swap V). reflexivity.
  Qed.

  Lemma sep_swap89:
    forall P Q R S T U V W X Y, massert_eqv (P ** Q ** R ** S ** T ** U ** V ** W ** X ** Y) (P ** Q ** R ** S ** T ** U ** V ** X ** W ** Y).
  Proof.
    intros. rewrite (sep_swap W). reflexivity.
  Qed.

  Definition sep_swap2 := sep_swap.

  Lemma sep_swap3:
    forall P Q R S, massert_eqv (P ** Q ** R ** S) (R ** Q ** P ** S).
  Proof.
    intros. rewrite sep_swap. rewrite (sep_swap P). rewrite sep_swap. reflexivity.
  Qed.

  Lemma sep_swap4:
    forall P Q R S T, massert_eqv (P ** Q ** R ** S ** T) (S ** Q ** R ** P ** T).
  Proof.
    intros. rewrite sep_swap. rewrite (sep_swap3 P). rewrite sep_swap. reflexivity.
  Qed.

  Lemma sep_swap5:
    forall P Q R S T U, massert_eqv (P ** Q ** R ** S ** T ** U) (T ** Q ** R ** S ** P ** U).
  Proof.
    intros. rewrite sep_swap. rewrite (sep_swap4 P). rewrite sep_swap. reflexivity.
  Qed.

  Lemma sep_swap6:
    forall P Q R S T U V, massert_eqv (P ** Q ** R ** S ** T ** U ** V) (U ** Q ** R ** S ** T ** P ** V).
  Proof.
    intros. rewrite sep_swap. rewrite (sep_swap5 P). rewrite sep_swap. reflexivity.
  Qed.

  Lemma sep_swap7:
    forall P Q R S T U V W, massert_eqv (P ** Q ** R ** S ** T ** U ** V ** W) (V ** Q ** R ** S ** T ** U ** P ** W).
  Proof.
    intros. rewrite sep_swap. rewrite (sep_swap6 P). rewrite sep_swap. reflexivity.
  Qed.

  Lemma sep_swap8:
    forall P Q R S T U V W X, massert_eqv (P ** Q ** R ** S ** T ** U ** V ** W ** X) (W ** Q ** R ** S ** T ** U ** V ** P ** X).
  Proof.
    intros. rewrite sep_swap. rewrite (sep_swap7 P). rewrite sep_swap. reflexivity.
  Qed.

  Lemma sep_swap9:
    forall P Q R S T U V W X Y, massert_eqv (P ** Q ** R ** S ** T ** U ** V ** W ** X ** Y) (X ** Q ** R ** S ** T ** U ** V ** W ** P ** Y).
  Proof.
    intros. rewrite sep_swap. rewrite (sep_swap8 P). rewrite sep_swap. reflexivity.
  Qed.


  Lemma sep_drop:
    forall P Q m, m |= P ** Q -> m |= Q.
  Proof.
    simpl; intros. tauto.
  Qed.

  Lemma sep_drop2:
    forall P Q R m, m |= P ** Q ** R -> m |= P ** R.
  Proof.
    intros. rewrite sep_swap in H. eapply sep_drop; eauto.
  Qed.

  Lemma sep_proj1:
    forall Q P m, m |= P ** Q -> m |= P.
  Proof.
    intros. destruct H; auto.
  Qed.

  Lemma sep_proj2:
    forall P Q m, m |= P ** Q -> m |= Q.
  Proof sep_drop.

  Definition sep_pick1 := sep_proj1.

  Lemma sep_pick2:
    forall P Q R m, m |= P ** Q ** R -> m |= Q.
  Proof.
    intros. eapply sep_proj1; eapply sep_proj2; eauto.
  Qed.

  Lemma sep_pick3:
    forall P Q R S m, m |= P ** Q ** R ** S -> m |= R.
  Proof.
    intros. eapply sep_pick2; eapply sep_proj2; eauto.
  Qed.

  Lemma sep_pick4:
    forall P Q R S T m, m |= P ** Q ** R ** S ** T -> m |= S.
  Proof.
    intros. eapply sep_pick3; eapply sep_proj2; eauto.
  Qed.

  Lemma sep_pick5:
    forall P Q R S T U m, m |= P ** Q ** R ** S ** T ** U -> m |= T.
  Proof.
    intros. eapply sep_pick4; eapply sep_proj2; eauto.
  Qed.

  Lemma sep_preserved:
    forall m m' P Q,
      m |= P ** Q ->
      (m |= P -> m' |= P) ->
      (m |= Q -> m' |= Q) ->
      m' |= P ** Q.
  Proof.
    simpl; intros. intuition auto.
  Qed.

  Lemma sep_preserved_disjoint : forall P Q P' Q' m m',
      m |= P ** Q ->
      (m |= P -> m' |= P') ->
      (m |= Q -> m' |= Q') ->
      disjoint_footprint P' Q' -> 
      m' |= P' ** Q'.
  Proof.           
    simpl; intros. intuition.
  Qed.

  Definition incl_footprint (P P' : massert) :=
    forall a, m_footprint P' a -> m_footprint P a. 

  Lemma incl_footprint_refl: forall P,
      incl_footprint P P.
  Proof.
    unfold incl_footprint. intros; intuition.
  Qed.

  Lemma incl_footprint_trans: forall P Q R,
      incl_footprint P Q ->
      incl_footprint Q R ->  
      incl_footprint P R.
  Proof.
    unfold incl_footprint. intros; intuition.
  Qed.

  Lemma sep_incl_footprint : forall P Q P' Q',
      incl_footprint P P' ->
      incl_footprint Q Q' ->
      incl_footprint (P**Q) (P'**Q'). 
  Proof.
    unfold incl_footprint. intros.
    unfold sepconj in *. simpl in *. 
    intuition.
  Qed.

  Lemma sep_preserved_footprint: forall m m' P Q P' Q',
      m |= P ** Q ->
      (m |= P -> m' |= P') ->
      (m |= Q -> m' |= Q') ->
      incl_footprint P P' ->
      incl_footprint Q Q' ->
      m' |= P' ** Q'. 
  Proof.
    simpl; intros. intuition.
    unfold disjoint_footprint, incl_footprint in *. 
    intros.
    apply H2 in H1.  apply H3 in H7.
    eapply H6; eauto.
  Qed.

  Ltac sepa := repeat rewrite -> sep_assoc. 

  Ltac sepa_in H := repeat rewrite -> sep_assoc in H.

  Ltac sep_swap_end := repeat rewrite <- sep_assoc; rewrite -> sep_comm; sepa. 

  Ltac sep_swap_end_in H := repeat rewrite <- sep_assoc in H; rewrite -> sep_comm in H; sepa_in H. 


Program Definition mconj (P Q: massert) : massert := {|
  m_pred := fun m => m_pred P m /\ m_pred Q m;
  m_footprint := fun a => m_footprint P a \/ m_footprint Q a
|}.
Next Obligation.
  split.
  - apply (m_invar P) with m; auto. eapply unchanged_on_implies; eauto. simpl; auto.
  - apply (m_invar Q) with m; auto. eapply unchanged_on_implies; eauto. simpl; auto.
Qed.
Next Obligation.
  destruct H0; [eapply (m_valid P) | eapply (m_valid Q)]; eauto.
Qed.

Lemma mconj_intro:
  forall P Q R m,
  m |= P ** R -> m |= Q ** R -> m |= mconj P Q ** R.
Proof.
  intros. destruct H as (A & B & C). destruct H0 as (D & E & F).
  split; [|split].
- simpl; auto.
- auto.
- red; simpl; intros. destruct H; [eelim C | eelim F]; eauto.
Qed.

Lemma mconj_proj1:
  forall P Q R m, m |= mconj P Q ** R -> m |= P ** R.
Proof.
  intros. destruct H as (A & B & C); simpl in A.
  simpl. intuition auto.
  red; intros; eapply C; eauto; simpl; auto.
Qed.

Lemma mconj_proj2:
  forall P Q R m, m |= mconj P Q ** R -> m |= Q ** R.
Proof.
  intros. destruct H as (A & B & C); simpl in A.
  simpl. intuition auto.
  red; intros; eapply C; eauto; simpl; auto.
Qed.

Lemma frame_mconj:
  forall P P' Q R m m',
  m |= mconj P Q ** R ->
  m' |= P' ** R ->
  m' |= Q ->
  m' |= mconj P' Q ** R.
Proof.
  intros. destruct H as (A & B & C); simpl in A.
  destruct H0 as (D & E & F).
  simpl. intuition auto.
  red; simpl; intros. destruct H2. eapply F; eauto. eapply C; simpl; eauto.
Qed.

Add Morphism mconj
  with signature massert_imp ==> massert_imp ==> massert_imp
  as mconj_morph_1.
Proof.
  intros P1 P2 [A B] Q1 Q2 [C D].
  red; simpl; intuition auto.
Qed.

Add Morphism mconj
  with signature massert_eqv ==> massert_eqv ==> massert_eqv
  as mconj_morph_2.
Proof.
  intros. destruct H, H0. split; apply mconj_morph_1; auto.
Qed.

  (** * Basic memory assertions. *)

  (** Pure logical assertion *)

  Program Definition pure (P: Prop) : massert := {|
    m_pred := fun m => P;
    m_footprint := fun a => False
  |}.
  (* not needed with Equations installed.
   Next Obligation.
    tauto.
  Qed.
 *)
  
  Lemma sep_pure:
    forall P Q m, m |= pure P ** Q <-> P /\ m |= Q.
  Proof.
    simpl; intros. intuition auto. red; simpl; tauto.
  Qed.


(** A range of addresses with unspecified contents. *)
(* Semi-open interval [lo,hi) *)
Program Definition range (lo hi: Z) : massert := {|
  m_pred := fun m =>
    (forall a, lo <= a < hi -> in_bounds a);
  m_footprint := fun a => lo <= a < hi 
|}.


Lemma range_empty:
  forall lo hi m,
    lo >= hi -> 
    m |= range lo hi. 
Proof.
  intros.
  simpl; intros. lia'. 
Qed. 


Lemma range_split:
  forall lo hi P mid m,
  lo <= mid <= hi ->
  m |= range lo hi ** P ->
  m |= range lo mid ** range mid hi ** P.
Proof.
  intros. rewrite <- sep_assoc. eapply sep_imp; eauto with sep.
  split; simpl; intros.
  - intuition auto.
    + apply H1; lia. 
    + apply H1; lia. 
    + red; simpl; intros; lia.  
  - intuition lia. 
Qed.

Lemma range_drop_left:
  forall lo hi P mid m,
  lo <= mid <= hi ->
  m |= range lo hi ** P ->
  m |= range mid hi ** P.
Proof.
  intros. apply sep_drop with (range lo mid). apply range_split; auto.
Qed.

Lemma range_drop_right:
  forall lo hi P mid m,
  lo <= mid <= hi ->
  m |= range lo hi ** P ->
  m |= range lo mid ** P.
Proof.
  intros. apply sep_drop2 with (range mid hi). apply range_split; auto.
Qed.

Lemma range_preserved:
  forall m m' lo hi,
  m |= range lo hi ->
  m' |= range lo hi.
Proof.
  auto.
Qed.

(** A range obeying a specified tag predicate. *)
(* Semi-open interval [lo,hi) *)
Program Definition trange (lo hi: Z) (tspec: Tag -> Prop) : massert := {|
  m_pred := fun m =>
    (forall a, lo <= a < hi -> in_bounds a /\ tspec (snd (m a)));
  m_footprint := fun a => lo <= a < hi 
|}.
Next Obligation.
  destruct (H a). 
  lia.
  split; auto.
  rewrite <- H0. auto. lia.
Qed.
Next Obligation.
  destruct (H a).
  lia.
  auto.
Qed.


Lemma trange_empty:
  forall lo hi tspec m,
    lo >= hi -> 
    m |= trange lo hi tspec. 
Proof.
  intros.
  simpl; split; lia'.
Qed. 


Lemma trange_split_imp:
  forall lo hi mid tspec,
  lo <= mid <= hi ->
  massert_imp (trange lo hi tspec)
    (trange lo mid tspec ** trange mid hi tspec).
Proof.  
  intros.
  split; simpl; intros.
  - intuition auto.
    + apply H0; lia. 
    + apply H0; lia. 
    + apply H0; lia. 
    + apply H0; lia. 
    + red; simpl; intros; lia.  
 - intuition lia. 
Qed.


 Lemma trange_join:  forall (n1 n2: nat) (pos:Z) m tspec P , 
      m |= trange pos (pos + n1) tspec ** P ->
      m |= trange (pos + n1) (pos + n1 + n2) tspec ** P ->
      m |= trange pos (pos + n1 + n2) tspec ** P.               
  Proof.
    induction n1; intros. 
    - replace (pos + 0%nat) with pos in H0 by lia'. 
      replace (pos + 0%nat) with pos by lia'. 
      auto.
    - replace (pos + S n1 + n2) with (pos + n1 + S n2) by lia'. 
      eapply IHn1. 
      + simpl in H|-*. destruct H as (A & B & C). split;[|split]; intros; auto.
        * eapply A. lia'.
        * unfold disjoint_footprint in C|-*. intros.
          eapply C; eauto.  simpl in H|-*. lia'.
      + simpl in H|-*. destruct H as (A & B & C). split;[|split]; intros; auto.
        * destruct (Z.eq_dec (pos+n1) a). 
          -- simpl in H. 
             eapply A. lia'. 
          -- eapply H0. lia'. 
        * unfold disjoint_footprint in C|-*. intros.
          destruct H0 as (A0 & B0 & C0). 
          simpl in H. 
          destruct (Z.eq_dec (pos+n1) a). 
          -- eapply C; eauto. simpl. lia'. 
          -- eapply C0; eauto.  simpl. lia'. 
  Qed.


 Lemma trange_join_imp':  forall (n1 n2: nat) (pos:Z) tspec,
     massert_imp (trange pos (pos + n1) tspec ** trange (pos + n1) (pos + n1 + n2) tspec)
           (trange pos (pos + n1 + n2) tspec).
  Proof.
    intros.
    unfold massert_imp; split; intros.
    - cut (True /\  m |= trange pos (pos + n1 + n2) tspec); [intuition|].
      rewrite <- sep_pure. rewrite sep_comm.
      eapply trange_join; rewrite sep_comm; rewrite -> sep_pure; split; auto.
      + apply sep_proj1 in H; auto.
      + apply sep_proj2 in H; auto.
    - simpl in *; lia'. 
  Qed.

Lemma trange_join_imp : forall (lo mid hi: Z) tspec, 
      lo <= mid <= hi -> 
      massert_imp (trange lo mid tspec ** trange mid hi tspec)
        (trange lo hi tspec). 
  Proof.
    unfold massert_imp. 
    intros; split; intros.
    - set (n1 := Z.to_nat(mid - lo)). 
      set (n2 := Z.to_nat(hi - mid)). 
      assert (mid = lo + n1) by lia'. 
      rewrite H1 in *. 
      assert (hi = lo + n1 + n2) by lia'. 
      rewrite H2 in *. 
      eapply trange_join_imp' ; eauto.
    - unfold m_footprint in *; simpl in *. lia'.
  Qed.    

  Lemma trange_eqv : forall (lo mid hi: Z) tspec, 
      lo <= mid <= hi -> 
      massert_eqv (trange lo mid tspec ** trange mid hi tspec)
        (trange lo hi tspec). 
  Proof.
    intros.
    unfold massert_eqv.
    split. 
    eapply trange_join_imp; eauto.
    eapply trange_split_imp; eauto.
  Qed.

  
  Lemma trange_tag : forall m lo hi tspec,
    m |= trange lo hi tspec ->
    forall a, lo <= a < hi -> tspec (snd (m a)).
  Proof.
    intros.
    unfold trange in H. simpl in H. destruct (H a H0).  auto.
  Qed.

Lemma writedown_unchanged_trange:
  forall (tspec: Tag -> Prop) m lo hi  priv dst_t b mv m',
    m |= trange lo hi tspec -> 
    writedown priv dst_t m b mv = Normal m' ->
    ((forall t', tspec t' -> ~ allowed priv t') \/ tspec dst_t) ->
    m' |= trange lo hi tspec. 
Proof.
  intros.
  unfold writedown in H0. 
  destruct (m b) as [v t] eqn:?. 
  machMonadInv1 H0.
  simpl. intros.
  apply andb_prop in Heqb0. destruct Heqb0. 
  apply in_bounds_access in H2. 
  apply allowed_access in H3. 
  destruct H1. 
  - rewrite mupdate_gso. eapply H; eauto. 
    intro. subst. eapply H1; eauto. 
    simpl in H. pose proof (H a H0). rewrite Heqp in H4. intuition.
  - destruct (Z.eq_dec a b). 
    + subst. rewrite mupdate_gss. intuition. 
    + rewrite mupdate_gso; try lia'. eapply H; eauto.       
Qed.


Lemma trange_lookup_failure_rule:
  forall lo hi tspec m t a , 
  m |= trange lo hi tspec -> 
  (forall t', tspec t' -> ~ allowed t t') ->
  lo <= a < hi -> 
  exists c: failure, lookup t m a = Failure c. 
Proof.
  simpl.  intros.
  unfold lookup. 
  eexists.
  destruct (H a H1) as [P Q]. 
  apply in_bounds_access in P. rewrite P.  simpl. 
  destruct (m a) as (mv,s); simpl in *. 
  apply H0 in Q. 
  destruct (access_allowed t s) eqn:?. 
  - exfalso.
    apply allowed_access in Heqb.
    apply Q; auto.
  - eauto.
Qed.    

(** A memory area that contains a value and tag satisfying given predicates *)

Program Definition contains (a : Z) (spec: mval -> Prop) (tspec: Tag -> Prop) : massert := {|
  m_pred := fun m =>
       in_bounds a              
       /\ spec (fst (m a))
       /\ tspec (snd (m a));
  m_footprint := fun a' => a = a'
|}.
Next Obligation.
  split; auto. 
  unfold unchanged_on in H0. 
  split; rewrite <- H0; auto. 
Qed.


Lemma contains_no_overflow:
  forall spec tspec m a, 
  m |= contains a spec tspec -> 
  0 <= a <= Int64.max_unsigned.
Proof.
  intros. simpl in H.
  apply in_bounds_WF. 
  tauto.
Qed.

Lemma lookup_rule:
  forall spec tspec m a t,
  m |= contains a spec tspec ->
  (forall t', tspec t' -> allowed t t') -> 
  exists mv, lookup t m a = Normal mv /\  spec mv. 
Proof.
  simpl. intros.
  unfold lookup.
  destruct (m a) as (mv,s); simpl in *. 
  exists mv. 
  destruct H as [P [Q R]].
  apply in_bounds_access in P. rewrite P. 
  apply H0 in R. 
  apply allowed_access in R. rewrite R. 
  auto.
Qed.

Lemma lookup_failure_rule:
  forall spec tspec m a t,
  m |= contains a spec tspec ->
  (forall t', tspec t' -> ~ allowed t t') ->
  exists c: failure, lookup t m a = Failure c.
Proof.
  simpl.  intros.
  unfold lookup. 
  destruct (m a) as (mv,s); simpl in *. 
  eexists.
  destruct H as [P [Q R]].
  apply in_bounds_access in P. rewrite P.  simpl. 
  apply H0 in R. 
  destruct (access_allowed t s) eqn:?. 
  - exfalso.
    apply allowed_access in Heqb.
    apply R; auto.
  -  eauto.
Qed.    

Lemma updm_rule:
  forall m a mv t (spec spec1: mval -> Prop) (tspec tspec1: Tag -> Prop) P,
    m |= contains a spec1 tspec1 ** P ->
  spec mv -> 
  tspec t ->  
  (updm t m a mv) |= contains a spec tspec ** P. 
Proof.
  intros.  destruct H as (A & B & C). destruct A as (D & E & F).  
  simpl; intuition.
  - rewrite mupdate_gss. auto.
  - rewrite mupdate_gss. auto.
  - apply (m_invar P) with m; auto.
    intros; red; intros. rewrite mupdate_gso; auto. intro; subst. eapply (C a0); simpl; auto.
Qed.

Lemma writedown_rule:
  forall (spec spec1: mval -> Prop) (tspec tspec1: Tag -> Prop) m a priv dst_t mv P,
    m |= contains a spec1 tspec1 ** P ->
    spec mv ->
    tspec dst_t -> 
    (forall t', tspec1 t' -> allowed priv t') -> 
    writedown priv dst_t m a mv = Normal (updm dst_t m a mv) /\
      updm dst_t m a mv  |= contains a spec tspec ** P.
Proof.
  intros.
  unfold writedown.
  exploit updm_rule; eauto. intro.  
  destruct H. 
  destruct H as (A & B & C). 
  destruct (m a) as [mv1 t1] . 
  split; eauto. 
  apply in_bounds_access in A.  rewrite A. 
  apply H2 in C. apply allowed_access in C. simpl in C. rewrite C. auto. 
Qed.

Lemma writedown_unchanged:
  forall (spec : mval -> Prop) (tspec: Tag -> Prop) m a priv dst_t b mv m',
    m |= contains a spec tspec -> 
    writedown priv dst_t m b mv = Normal m' ->
    (forall t', tspec t' -> ~ allowed priv t') ->
    m' |= contains a spec tspec.
Proof.
  intros.
  unfold writedown in H0. 
  destruct (m b) as [v t] eqn:?. 
  machMonadInv H0. 
  simpl. rewrite mupdate_gso; auto.
  intro. subst. simpl in H.  rewrite Heqp in H.  simpl in H.
  eapply (H1 t). intuition.
  apply andb_prop in Heqb0. destruct Heqb0. 
  apply allowed_access in H2. auto. 
Qed.


Lemma contains_imp:
  forall (spec1 spec2: mval -> Prop) (tspec1 tspec2: Tag -> Prop) a,
  (forall v, spec1 v -> spec2 v) ->
  (forall t, tspec1 t -> tspec2 t) -> 
  massert_imp (contains a spec1 tspec1) (contains a spec2 tspec2).
Proof.
  intros; split; simpl; intros.
- intuition auto. 
- auto.
Qed.

Lemma trange_imp:
  forall a n (tspec1 tspec2: Tag -> Prop),
  (forall t, tspec1 t -> tspec2 t) -> 
  massert_imp (trange a n tspec1) (trange a n tspec2).
Proof.  
  intros; split; simpl; intros; auto.
  destruct (H0 a0 H1). intuition.
Qed.


Lemma trange_contains_imp:
  forall a tspec,
    massert_imp (trange a (a+1) tspec)
         (contains a (fun v => True) tspec). 
Proof.
  intros. unfold massert_imp. split; intros.
  - destruct H with (a:= a); try lia'.
    simpl; intuition. 
  - unfold m_footprint in *. unfold contains, trange in *.  lia'. 
Qed.

Lemma contains_trange_imp:
  forall a spec tspec,
    massert_imp (contains a spec tspec)
      (trange a (a+1) tspec).
Proof.
  intros; unfold massert_imp; split; intros.
  - destruct H as (A & B & C). simpl in *. intros.
    assert (a = a0) by lia'.  subst; auto.
  - simpl in *. lia'.
Qed.



(** A memory area that contains a given value and tag *)
Definition hasvalue (a:Z) (mv: mval) (t: Tag) : massert :=
  contains a (fun mv' => mv' = mv) (fun t' => t' = t).

Lemma lookup_rule_v:
  forall m a mv t p,
  m |= hasvalue a mv t -> 
  allowed p t -> 
  lookup p m a = Normal mv.
Proof.
  intros.
  apply lookup_rule with (t := p) in H.
  - destruct H as [mv0 [P Q]]. subst. auto.
  - intros. subst.  auto.
Qed.

Lemma updm_rule_v:
  forall m a mv t (spec1: mval -> Prop) (tspec1: Tag -> Prop) P,
    m |= contains a spec1 tspec1 ** P ->
    (updm t m a mv) |= hasvalue a mv t ** P. 
Proof.
  intros.  eapply updm_rule; eauto. 
Qed.


Lemma writedown_rule_v:
  forall (spec1: mval -> Prop) (tspec1: Tag -> Prop) m a priv dst_t mv P,
    m |= contains a spec1 tspec1 ** P ->
    (forall t', tspec1 t' -> allowed priv t') -> 
    writedown priv dst_t m a mv = Normal (updm dst_t m a mv) /\
      updm dst_t m a mv  |= hasvalue a mv dst_t ** P.
Proof.
  intros.
  eapply writedown_rule; eauto.
Qed.


Lemma writedown_unchanged_v:
  forall (spec: mval -> Prop) (tspec: Tag -> Prop) m a priv dst_t b mv m', 
  m |= contains a spec tspec ->
  writedown priv dst_t m b mv = Normal m' ->
  (forall t', tspec t' -> ~ allowed priv t') ->
  m' |= contains a spec tspec. 
Proof.
  intros. 
  eapply writedown_unchanged; eauto.
Qed.



  Fixpoint hasvalues (pos:Z) (mvs: list mval) (t:Tag) : massert :=
    match mvs with
    | nil => pure True
    | mv :: mvs =>
        hasvalue pos mv t 
          ** hasvalues (pos + 1) mvs t
    end.

  Lemma hasvalue_hasvalues_imp: forall pos mv t,
      massert_imp (hasvalue pos mv t) (hasvalues pos (mv::nil) t). 
  Proof.
    intros.
    unfold hasvalues.
    unfold massert_imp; split.
    intros. rewrite sep_comm. rewrite sep_pure. split; auto.
    intros. unfold m_footprint in *.  unfold hasvalue in *. simpl in *.  intuition.
  Qed.


Lemma hasvalues_trange_imp: forall vs pos t,
    massert_imp (hasvalues pos vs t) (trange pos (pos + length vs) (fun t' => t' = t)). 
Proof.
  induction vs; intros. 
  - split; intros.
    + simpl in *.  intros; lia'. 
    + simpl in *. lia'. 
  - unfold length. fold (length vs).     
    replace (pos + S (length vs)) with ((pos + 1%nat) + length (vs)) by lia'. 
    split; intros.
    + unfold hasvalues in H. fold hasvalues in H.
      rewrite <- trange_eqv with (mid := pos + 1%nat); try lia'. 
      erewrite <- contains_trange_imp.  unfold hasvalue in H.
      rewrite (IHvs (pos+1) t) in H.  eauto.
    + unfold hasvalues. fold hasvalues. 
      pose proof (IHvs (pos+1) t).  unfold massert_imp in H0. 
      unfold m_footprint in *; simpl in *. unfold m_footprint in *; simpl in *. 
      destruct H0. 
      destruct (Z.eq_dec pos a0).
      * subst; left; auto.
      * right. eapply H1. lia'. 
Qed.


Lemma hasvalues_footprint : forall vs pos t a,
    pos <= a < pos + length vs <-> 
    m_footprint (hasvalues pos vs t) a.
Proof.
  unfold m_footprint. 
  induction vs; intros; split; simpl; intros. 
  - lia.
  - destruct H. 
  - destruct (Z.eq_dec pos a0). 
    + left; auto.
    + right. unfold m_footprint. erewrite <- (IHvs (pos + 1) t a0). lia'. 
  - destruct H. 
    + lia.
    + unfold m_footprint in H. 
      erewrite <- (IHvs (pos+1) t a0) in H.  lia'.
Qed.

Lemma lookup_rule_vs: forall mvs m pos t p,
  m |= hasvalues pos mvs t ->
  allowed p t -> 
  forall n mv, List.nth_error mvs n = Some mv -> 
  lookup p m (pos+n) = Normal mv.
Proof.  
  induction mvs.
  - intros.
    destruct n; inv H1. 
  - intros. 
    destruct n.
    +  inv H1.  replace (pos + 0%nat) with pos by lia'.
       apply sep_proj1 in H. 
       eapply lookup_rule_v; eauto.
    + inv H1. apply sep_proj2 in H. fold hasvalues in H. 
      replace (pos + S n) with ((pos+1) + n) by lia'. 
      eapply IHmvs; eauto.
Qed.

Lemma hasvalues_tag: forall mvs m pos t,
   m |= hasvalues pos mvs t ->
   forall (n:nat), (0 <= n < length mvs)%nat -> 
   snd (m (pos+n)) = t.                              
Proof.
  induction mvs. 
  - intros.
    inv H0. inv H2. 
  - intros.
    destruct n.
    + replace (pos + 0%nat) with pos by lia'. 
      apply sep_proj1 in H. 
      inv H. intuition.
    + replace (pos + S n) with ((pos + 1) + n) by lia'. 
      apply sep_proj2 in H.  fold hasvalues in H. 
      eapply IHmvs; eauto.  
      simpl in H0.  lia. 
Qed.

(* A slightly specialized rule *)

Definition replace {A} (xs: list A) (n:nat) (x:A) :=
  firstn n xs ++ x::tail(skipn n xs). 

Lemma writedown_rule_vs:
  forall mvs m pos priv t mv P,
    m |= hasvalues pos mvs t ** P -> 
    allowed priv t -> 
    forall (n:nat), (n < length mvs)%nat -> 
    writedown priv t m (pos+n) mv = Normal (updm t m (pos+n) mv) /\
    updm t m (pos+n) mv |= hasvalues pos (replace mvs n mv) t ** P.
Proof.
  induction mvs. 
  - intros.
    inv H1. 
  - intros.
    destruct n. 
    + replace (pos + 0%nat) with pos by lia'. 
      exploit writedown_rule_v. 
      unfold hasvalues in H.  fold hasvalues in H.  apply sep_assoc in H. 
      eapply H. 
      intros. simpl in H2.  subst t'. eauto.
      intros [Q R]. 
      split; eauto.
      unfold replace. simpl firstn. simpl skipn. simpl app. 
      unfold hasvalues; fold hasvalues. apply sep_assoc. 
      auto.
   + replace (replace (a :: mvs) (S n) mv) with (a:: replace mvs n mv) by auto.
     replace (pos + S n) with ((pos+1) + n) by lia'. 
     simpl in H1.  apply Nat.succ_lt_mono in H1. 
     exploit IHmvs. 
     unfold hasvalues in H.  fold hasvalues in H.  apply sep_assoc in H.
     apply sep_swap in H. 
     apply H. eauto.  eauto.
     intros [Q R].
     split; eauto.
     apply sep_swap in R. 
     unfold hasvalues; fold hasvalues. apply sep_assoc. apply R. 
Qed.


Lemma writedown_unchanged_vs:
  forall mvs m pos t priv dst_t b mv m', 
    m |= hasvalues pos mvs t -> 
    writedown priv dst_t m b mv = Normal m' ->
    ~ allowed priv t ->
    m' |= hasvalues pos mvs t.
Proof.
  induction mvs; intros. 
  - auto. 
  - unfold hasvalues; fold hasvalues.  unfold hasvalues in H; fold hasvalues in H.
    eapply sep_preserved; eauto. 
    intro. 
    eapply writedown_unchanged_v; eauto. 
    intros. subst. auto.
Qed.


End Separation.


