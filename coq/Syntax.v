Set Implicit Arguments.
Require Import DblibTactics.
Require Import DeBruijn.
Require Import Environments.

(* ---------------------------------------------------------------------------- *)

(* Kinds. *)

Inductive kind :=
| ADDR       (* Addresses. A subset of values. *)
| VALUE      (* Values. Can be stored in the heap. *)
| STATEMENT  (* Expressions that produce no result. *)
| LVALUE     (* Expressions that produce an address. *)
| RVALUE.    (* Expressions that write a multi-word result to a destination. *)

(* ---------------------------------------------------------------------------- *)

(* Auxiliary syntactic elements. *)

(* A de Bruijn index. *)

Definition var :=
  nat.

(* A size (or an offset), expressed in words. *)

Definition size :=
  nat.

Definition offset :=
  size.

(* A base address is the base address of a memory block. *)

Definition base :=
  nat.

(* The combination of a base address and an offset forms an address that can
   be used to access memory (for reading or writing). We adopt this
   representation because we wish to allow address arithmetic within a block
   and disallow it across blocks. Thus, address arithmetic allows altering the
   offset component of an address, but does not allow altering its base
   component. *)

Definition address :=
  (base * offset)%type.

(* ---------------------------------------------------------------------------- *)

(* Syntax. *)

Inductive syntax :=

(* Variables. A priori, a variable can have an arbitrary kind, although, for
   the moment, we use only variables of kind [ADDR], i.e., variables that
   stand for addresses. *)

(* In this intermediate language, variables are immutable. When an address
   [SAddr a] is substituted for a variable [x], this means that this address
   is the *value* of the variable [x]. However, in order to avoid confusion,
   one must keep in mind how the source language (Rust) is translated down to
   this intermediate language. A stack allocation expression { var x : z; st }
   is translated (see [SStackAlloc] below) in such a way that the variable [x]
   becomes bound to the *address* of a new memory area of size [z]. In other
   words, the (immutable) variable that is known as [x] after the translation
   holds the *address* of the (possibly mutable) variable that is known as [x]
   before the translation. *)

| SVar: var -> syntax

(* Addresses have kind [ADDR]. *)

| SAddr: address -> syntax

(* Values have kind [VALUE]. A value is a thing that can be stored in a
   one-word cell in the heap. The values include the memory locations (above)
   as well as a special garbage value, which denotes uninitialized memory. *)

| SGarbage: syntax

(* Statements have kind [STATEMENT]. They can be thought of as expressions
   that produce no result. As a consequence, their evaluation does not require
   specifying a destination address. *)

| SSkip: syntax
| SSequence: syntax -> syntax -> syntax
| SAssignment: syntax -> syntax -> syntax
| SLetLValue: syntax -> syntax -> syntax
| SDelete: syntax -> syntax

(* LValues have kind [LVALUE]. They include the addresses (above) as well as
   the following constructs. They can be thought of as expressions whose
   evaluation produces a memory location (if it succeeds). They appear on the
   left-hand side of [SLetValue], and nowhere else. *)

| SFieldProj: syntax -> size -> syntax
| SDeref: syntax -> syntax
| SNew: size -> syntax

(* RValues have kind [RVALUE]. They can be thought of as expressions whose
   evaluation produces a multi-word result, which is written to a destination
   address. They appear either as the right-hand side of an assignment or
   nested within a composite rvalue (this is permitted by [SConsecutive]).
   They include the addresses (above) as well as the following constructs. *)

| SCopy: size -> syntax -> syntax
| SNothing: syntax
| SConsecutive: syntax -> syntax -> syntax

.

(* ---------------------------------------------------------------------------- *)

(* The binding structure of our syntax. *)

Instance Var_syntax : Var syntax := {
  var := SVar
}.

Fixpoint traverse_syntax (f : nat -> nat -> syntax) l t :=
  match t with
  | SVar x =>
      (* variable occurrence *)
      f l x
  | SAddr a =>
      SAddr a
  | SGarbage =>
      SGarbage
  | SSkip =>
      SSkip
  | SSequence st1 st2 =>
      SSequence (traverse_syntax f l st1) (traverse_syntax f l st2)
  | SAssignment lv rv =>
      SAssignment (traverse_syntax f l lv) (traverse_syntax f l rv)
  | SLetLValue lv st =>
      (* one more variable is bound in [st] *)
      SLetLValue (traverse_syntax f l lv) (traverse_syntax f (l + 1) st)
  | SDelete lv =>
      SDelete (traverse_syntax f l lv)
  | SFieldProj lv z =>
      SFieldProj (traverse_syntax f l lv) z
  | SDeref lv =>
      SDeref (traverse_syntax f l lv)
  | SNew z =>
      SNew z
  | SCopy z lv =>
      SCopy z (traverse_syntax f l lv)
  | SNothing =>
      SNothing
  | SConsecutive rv1 rv2 =>
      SConsecutive (traverse_syntax f l rv1) (traverse_syntax f l rv2)
  end.

Instance Traverse_syntax : Traverse syntax syntax := {
  traverse := traverse_syntax
}.

Instance TraverseVarInjective_syntax : @TraverseVarInjective syntax _ syntax _.
Proof.
  constructor. prove_traverse_var_injective.
Qed.

Instance TraverseFunctorial_syntax : @TraverseFunctorial syntax _ syntax _.
Proof.
  constructor. prove_traverse_functorial.
Qed.

Instance TraverseRelative_syntax : @TraverseRelative syntax syntax _.
Proof.
  constructor. prove_traverse_relative.
Qed.

Instance TraverseIdentifiesVar_syntax : @TraverseIdentifiesVar syntax _ _.
Proof.
  constructor. prove_traverse_identifies_var.
Qed.

Instance TraverseVarIsIdentity_syntax : @TraverseVarIsIdentity syntax _ syntax _.
Proof.
  constructor. prove_traverse_var_is_identity.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Stack allocation, { var x : z; st }, can be viewed as sugar for
   allocating a block of size [z] in the heap, binding [x] to the
   address of this block, executing [st], and de-allocating. This
   is written "let x = new z in (st; delete x)". *)

Notation SStackAlloc z st :=
  (SLetLValue (SNew z) (SSequence st (SDelete (SVar 0)))).

(* ---------------------------------------------------------------------------- *)

(* Tactics. *)

Ltac da (* destruct_addresses *) :=
  intros;
  repeat match goal with a: address |- _ =>
    let b := fresh "b" in
    let o := fresh "o" in
    destruct a as [ b o ]
  end.

