Set Implicit Arguments.
Require Import Relation_Operators.
Require Import MyTactics.
Require Import MyList.
Require Import AllocationMaps.
Require Import DeBruijn.
Require Import Environments.
Require Import Syntax.
Require Import WellKindedness.
Require Import Memory.

(* ---------------------------------------------------------------------------- *)

(* The size of every rvalue is statically known. This is made explicit by the
   following function, which maps an rvalue to its size (i.e., the number of
   words that it spans in memory). *)

Fixpoint sizeof (rv : syntax) : size :=
  match rv with
  | SCopy z lv =>
      (* When an lvalue is converted to an rvalue, its size is explicitly
         indicated, so we know how many words must be copied. *)
      z
  | SAddr lv =>
      (* A pointer occupies one word. *)
      1
  | SNothing =>
      (* The rvalue [nothing] occupies zero words. *)
      0
  | SConsecutive rv1 rv2 =>
      (* The concatenation of two rvalues occupies the sum of their sizes. *)
      sizeof rv1 + sizeof rv2
  | _ =>
      (* Dummy default. *)
      0
  end.

(* ---------------------------------------------------------------------------- *)

(* Reduction. *)

Inductive configuration :=
  Cf: heap -> syntax -> configuration.

Inductive red : configuration -> configuration -> Prop :=

(* Reduction of lvalues. *)

(* The field selection expression [a.z] evaluates to the address [a + z].
   No runtime test is involved here; well-kindedness guarantees that the
   left-hand argument of [SFieldProj] must be a variable or a memory
   location. Note that the address [a + z] could be out of bounds, but
   that is not a problem as long as it is not dereferenced. *)

| RedFieldProj:
    forall h a z,
    red
      (Cf h (SFieldProj (SAddr a) z))
      (Cf h (SAddr (address_add a z)))

(* The dereferencing expression [*a] looks up the heap at address [a], checks
   that the value found there is an address [a'] (as opposed to, say, garbage,
   or a primitive integer value), and reduces to [a']. Thus, a runtime test is
   involved (but a well-typed program should never fail). *)

| RedDeref:
    forall h a a',
    read h a (SAddr a') ->
    red
      (Cf h (SDeref (SAddr a)))
      (Cf h (SAddr a'))

(* The memory allocation expression [new z] allocates a new block of size [z],
   and returns its address. *)

| RedNew:
    forall h z h' a,
    malloc h z = (h', a) ->
    red
      (Cf h  (SNew z))
      (Cf h' (SAddr a))

(* Reduction of statements. *)

(* Reduction of a sequence whose left-hand side has finished. *)

| RedSeqSkip:
    forall h st,
    red
      (Cf h (SSequence SSkip st))
      (Cf h st)

(* Reduction of a sequence whose left-hand side has not finished. *)

| RedSeqContext:
    forall h h' st1 st1' st2,
    red
      (Cf h  st1)
      (Cf h' st1') ->
    red
      (Cf h  (SSequence st1  st2))
      (Cf h' (SSequence st1' st2))

(* Reduction of an assignment. There are as many rules as there are
   forms of rvalues. The left-hand side of the assignment is always
   assumed to be a memory location. *)

(* TEMPORARY should we first reduce an rvalue to a list of values,
   then perform a multi-write? should we enforce disjointness of
   source and destination at the level of an entire assignment?
   does this question even make sense? *)

| RedCopy:
    forall h dst z src h',
    copy h dst z src h' ->
    red
      (Cf h (SAssignment (SAddr dst) (SCopy z (SAddr src))))
      (Cf h' SSkip)

| RedAddress:
    forall h dst a h',
    write h dst (SAddr a) h' ->
    red
      (Cf h (SAssignment (SAddr dst) (SAddr a)))
      (Cf h' SSkip)
   
| RedNothing:
    forall h dst,
    red
      (Cf h (SAssignment (SAddr dst) SNothing))
      (Cf h SSkip)

| RedConsecutive:
    forall h dst rv1 rv2,
    red
      (Cf h (SAssignment (SAddr dst) (SConsecutive rv1 rv2)))
      (Cf h (SSequence
        (SAssignment (SAddr dst) rv1)
        (SAssignment (SAddr (address_add dst (sizeof rv1))) rv2)
      ))

(* Reduction of a local variable binding whose left-hand side has reached a
   result [l]. The memory location [l] is substituted for the variable [x] in
   the continuation [st]. *)

| RedLetLValue:
    forall h a st,
    red
      (Cf h (SLetLValue (SAddr a) st))
      (Cf h (subst (SAddr a) 0 st))

(* Reduction of a local variable binding whose left-hand side has not yet
   reached a result. Reduction (at kind [LVALUE]) takes place in the left-hand
   side. *)

| RedLetLValueContext:
    forall h lv h' lv' st,
    red
      (Cf h  lv)
      (Cf h' lv') ->
    red
      (Cf h  (SLetLValue lv  st))
      (Cf h' (SLetLValue lv' st))

(* Reduction of a [delete] expression. *)

| RedDelete:
    forall h a h',
    delete h a h' ->
    red
      (Cf h (SDelete (SAddr a)))
      (Cf h' SSkip)

.

Hint Constructors red : red.

(* TEMPORARY one could also let an rvalue [rv] reduce to a literal
   sequence of words, of length [sizeof rv], then perform a single
   multi-word assignment at the end. Multiple-word reads and writes
   would then be the primitive operations. A literal sequence of
   words would have to be a new form of rvalue; although we already
   have SConsecutive and SNothing, so it would suffice to add SWord,
   of kind VALUE -> RVALUE. Would that be preferable? *)

(* ---------------------------------------------------------------------------- *)

(* The reflexive-transitive closure of the reduction relation. *)

Notation redstar :=
  (clos_refl_trans_1n _ red).

Hint Constructors clos_refl_trans_1n : redstar.

(* ---------------------------------------------------------------------------- *)

(* We obtain the following derived reduction rule for [SStackAlloc]. *)

Lemma RedStackAlloc:
  forall h z st h' a,
  malloc h z = (h', a) ->
  redstar
    (Cf h (SStackAlloc z st))
    (Cf h' (SSequence
      (subst (SAddr a) 0 st)
      (SDelete (SAddr a)
    ))).
Proof.
  intros.
  (* One reduction step. *)
  econstructor; [ eauto with red | ].
  (* Another reduction step. *)
  econstructor; [ eauto with red | ].
  (* And we are there. *)
  simpl_subst_goal. econstructor.
Qed.

