Set Implicit Arguments.
Require Import DblibTactics.
Require Import DeBruijn.
Require Import Environments.

(* The syntax of types is independent of the syntax of terms, because terms
   do not refer to types (they are not annotated with types) and types do
   not refer to terms (there is no dependency). *)

(* ---------------------------------------------------------------------------- *)

(* The syntax of types. *)

Inductive ty :=

  (* [TyEpsilon] is the type of a memory range of length zero. *)

| TyEpsilon: ty

  (* [TyConsecutive] is a concatenation operator for types that describe
     memory ranges. *)

| TyConsecutive: ty -> ty -> ty

  (* [TyUnique T] is the type of a unique pointer to a memory block whose
     content is described by [T]. Only a base address (i.e., an address
     whose offset component is zero) can receive this type. *)

| TyUnique: ty -> ty

  (* [TyBorrowed l T] is the type of a borrowed pointer to a range of
     memory described by [T]. An arbitrary address (i.e., not just a
     base address) can receive this type. The parameter [l] is a lifetime
     variable. *)

| TyBorrowed: nat -> ty -> ty

  (* [TyLent l T] is the type of a memory area that has been lent out.
     The parameter [l] is a lifetime variable. *)

| TyLent: nat -> ty -> ty

.

(* ---------------------------------------------------------------------------- *)

(* The size of types. *)

Fixpoint sizeof_ty (T : ty) : nat :=
  match T with
  | TyEpsilon =>
      0
  | TyConsecutive T U =>
      sizeof_ty T + sizeof_ty U
  | TyUnique _ =>
      1
  | TyBorrowed _ _ =>
      1
  | TyLent _ T =>
      sizeof_ty T
  end.

(* ---------------------------------------------------------------------------- *)

(* Some types are duplicable; some types are not (i.e., they are linear). *)

Fixpoint duplicable (T : ty) : Prop :=
  match T with
  | TyEpsilon =>
      True
  | TyConsecutive T U =>
      duplicable T /\ duplicable U
  | TyUnique _ =>
      False
  | TyBorrowed _ _ =>
      True
  | TyLent _ T =>
      duplicable T
  end.

