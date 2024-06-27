(* Concrete C *)

(* Shared definitions *)

Require Export Coqlib Zbits Integers Maps.
Import ListNotations.
Import Int64.
Set Implicit Arguments.

Definition val := int64.
Definition val_eq := Int64.eq.
Definition val_eq_dec := Int64.eq_dec.

Definition val_of_Z  : Z -> val := repr.
Global Coercion Z.of_nat  : nat  >-> Z.

Definition NULL : val := zero.

Local Open Scope Z_scope.

Definition def_val := NULL.
Inductive operation : Type :=
  | Oadd
  | Osub.
Definition eval_op (op: operation) (x y: val) : val := 
  match op with
  | Oadd => Int64.add x y
  | Osub => Int64.sub x y
  end.

(** ** Abstract sets/collections *)

(** Most of the abstract sets in this development are implemented as Coq
    [positive]s *)

Definition ident := positive.
Definition reg   := positive.
Definition reg_eq_dec := Pos.eq_dec.

(** [comparisons] (used for/in boolean operators/expressions) *)

Inductive comparison : Set :=  (** The standard set of comparisons *)
    Ceq : comparison           (** == equality                     *)
  | Cne : comparison           (** != inequality                   *)
  | Clt : comparison           (** <  less than                    *)
  | Cle : comparison           (** <= less than equals             *)
  | Cgt : comparison           (** >  greater than                 *)
  | Cge : comparison.          (** >= greater than equals          *)



(** ** Register banks via finite partial maps *)
(** Mappings from registers to some type. [PMap] is a finite partial maps
    (with default values for unmapped keys) library from the CompCert Maps
    module. *)

Module Regmap := PMap.
Module Regset := PTree.
Notation "a # b" := (Regmap.get b a) (at level 1).
Notation "a ## b" := (List.map (fun r => Regmap.get r a) b) (at level 1).
Notation "a # b <- c" := (Regmap.set b c a) (at level 1, b at next level).

(** Another notation *)
Notation "a ! b <- c" := (PTree.set b c a) (at level 1, b at next level).

(* XXXXX probably dead 
Class Inj A B : Type := {
  inject : A -> B
}.
Notation "$" := inject.
*)


Fixpoint assoc_lookup {A:Type} (x: ident) (al:  list (ident*A) ) : option A :=
  match al with
  | [] => None
  | (id,a)::rest => if Pos.eqb id x then Some a else assoc_lookup x rest
  end.


Close Scope Z.

Ltac lia' := (unfold val_of_Z, reg in *; lia).

Ltac maybeMonadInv H :=
  match type of H with
  | (match ?E with Some _ => _ | None => _ end) = Some _ => 
    destruct E eqn:?; try (maybeMonadInv H)
  | (match ?E with _ => _ end) = Some _ => 
    destruct E eqn:?; try (maybeMonadInv H)
  | ((if ?E then _ else _) = Some _) =>
    destruct E eqn:?; try (maybeMonadInv H)
  | Some _ = Some _ => inv H
  | Some _ = None => try discriminate 
  | None = Some _ => try discriminate
  end.

Ltac allInv :=
  repeat
    match goal with
    | H : _ |- _ => maybeMonadInv H
    end.
