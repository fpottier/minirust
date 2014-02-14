Set Implicit Arguments.
Require Import MyTactics.
Require Import DeBruijn.
Require Import Environments.
Require Import Syntax.

(* ---------------------------------------------------------------------------- *)

(* Well-kindedness. *)

Inductive wk : env kind -> syntax -> kind -> Prop :=

(* The case of variables is special, as a variable can have an arbitrary kind. *)

(* Variable: [x]. *)

| WkVar:
    forall K x kappa,
    lookup x K = Some kappa ->
    wk K (SVar x) kappa

(* The following constructs have kind [ADDR]. *)

(* The value [SAddr a] represents the address [a] in the heap. *)

| WkAddr:
    forall K a,
    wk K (SAddr a) ADDR

(* The following constructs have kind [VALUE]. *)

(* An address is also a value. In other words, [ADDR] is a subkind of [VALUE]. *)

| WkAddrAsValue:
    forall K av,
    wk K av ADDR ->
    wk K av VALUE

(* The value [garbage] is used to fill newly-allocated, uninitialized
   areas of memory. *)

| WkGarbage:
    forall K,
    wk K SGarbage VALUE

(* The following constructs have kind [STATEMENT]. *)

(* [skip] is a no-op. *)

| WkSkip:
    forall K,
    wk K SSkip STATEMENT

(* Sequence: [st; st]. *)

| WkSequence:
    forall K st1 st2,
    wk K st1 STATEMENT ->
    wk K st2 STATEMENT ->
    wk K (SSequence st1 st2) STATEMENT

(* Assignment: [lv = rv]. *)

| WkAssignment:
    forall K lv rv,
    wk K lv ADDR ->
    wk K rv RVALUE ->
    wk K (SAssignment lv rv) STATEMENT

(* Local variable definition: [let x = lv in st]. The variable [x] is the de
   Bruijn index 0, so it does not explicitly appear. The lvalue [lv] is
   evaluated, yielding (if successful) a memory location [l]. The variable [x]
   is bound to this address. [x] may be used in the statement [st]. No memory
   allocation (on the stack or on the heap) takes place. *)

| WkLetLValue:
    forall K lv st,
    wk K lv LVALUE ->
    wk (insert 0 ADDR K) st STATEMENT ->
    wk K (SLetLValue lv st) STATEMENT

(* Memory de-allocation: [delete lv]. The size of the block that must be
   freed is known by the runtime system. *)

| WkDelete:
    forall K lv,
    wk K lv ADDR ->
    wk K (SDelete lv) STATEMENT

(* The following constructs have kind [LVALUE]. *)

(* We allow a syntactic element of kind [ADDR] to also have kind [LVALUE]. This
   allows variables (and memory locations) to appear as lvalues, i.e., it
   allows writing [let x = y in st], where [x] and [y] are temporaries of kind
   [ADDR]. This is useful as an intermediate step in the reduction of more
   elaborate expressions of the form [let x = lv in st]. *)

| WkAddrAsLValue:
    forall K lv,
    wk K lv ADDR ->
    wk K lv LVALUE

(* Field projection: [lv.f]. (Note that [z] must be nonnegative.) *)

| WkFieldProj:
    forall K lv z,
    wk K lv ADDR ->
    wk K (SFieldProj lv z) LVALUE

(* Dereferencing: [*lv]. *)

| WkDeref:
    forall K lv,
    wk K lv ADDR ->
    wk K (SDeref lv) LVALUE

(* Memory allocation: [new z]. The parameter [z] is a size. *)

| WkNew:
    forall K z,
    wk K (SNew z) LVALUE

(* The following constructs have kind [RVALUE]. *)

(* Copying: [z lv]. This means that an lvalue can be supplied where an rvalue
   is expected. We annotate with a size [z], so that we know how many words
   of memory must be copied. *)

| WkCopy:
    forall K z lv,
    wk K lv ADDR ->
    wk K (SCopy z lv) RVALUE

(* Every address also has kind [RVALUE]. It is a one-word rvalue. *)

| WkAddress:
    forall K lv,
    wk K lv ADDR ->
    wk K lv RVALUE

(* Nothing is an rvalue, which occupies zero words. *)

| WkNothing:
    forall K,
    wk K SNothing RVALUE

(* The concatenation of two rvalues forms an rvalue: [rv; rv]. This
   allows us to emulate struct constants, without relying on actual
   struct definitions. *)

| WkConsecutive:
    forall K rv1 rv2,
    wk K rv1 RVALUE ->
    wk K rv2 RVALUE ->
    wk K (SConsecutive rv1 rv2) RVALUE

.

