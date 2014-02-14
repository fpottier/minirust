Set Implicit Arguments.
Require Export Coq.Program.Equality.
Require Export LibTactics.
Require Export DblibTactics.

(* It can be a nuisance that [1 + x] simplifies to [S x]. Prevent it. *)

Global Opaque plus.

(* Apparently the lemma [plus_n_O] is part of the default database [core].
   As a result, a goal of the form [e = ?x], where the right-hand side is
   a meta-variable, is resolved by [eauto] by instantiating [x] with [e + 0].
   This is ridiculous! We override this behavior by prodiving [reflexivity]
   as a hint. *)

Hint Extern 0 (_ = _ :> nat) => reflexivity : core.
Hint Extern 0 (_ + 0 = _ :> nat) => symmetry; apply plus_n_O : core.
Hint Extern 0 (_ = _ + 0 :> nat) => apply plus_n_O : core.

(* Make it possible to use [reflexivity] at the leaves of an [eauto] search. *)

Hint Extern 1 (_ = _) => reflexivity : reflexivity.

(* Hint for trying to find an arithmetic contradiction among the
   hypotheses. *)

Hint Extern 1 => solve [ false_goal; omega ] : falseomega.

(* These tactics are analogous to [dblib_inspect_cases] and
   [dblib_by_cases], but are concerned with [equiv_dec]. *)

Require Import EquivDec.

Ltac equiv_dec_inspect_cases :=
  match goal with
  | |- context [equiv_dec ?a1 ?a2] =>
      case (equiv_dec a1 a2); [
        unfold equiv; intro; try subst a1
      | unfold equiv, complement; intro ]
  | h: context [equiv_dec ?a1 ?a2] |- _ =>
      revert h;
      case (equiv_dec a1 a2); [
        unfold equiv; intro h; intro; try subst a1
      | unfold equiv, complement; intro h; intro ]
  end;
  try solve [ tauto ].

Ltac equiv_dec_by_cases :=
  try solve [ tauto ];
  repeat equiv_dec_inspect_cases.

(* This tactic unpacks all existentially quantified hypotheses and splits all
   conjunctive hypotheses. *)

Ltac unpack1 :=
  match goal with
  | h: ex _ |- _ => destruct h
  | h: (_ /\ _) |- _ => destruct h
  | h: exists2 x, _ & _ |- _ => destruct h
  end.

Tactic Notation "unpack" :=
  repeat progress unpack1.
Goal
  forall (P Q : nat -> Prop),
  (exists n, P n /\ Q n) ->
  (exists n, Q n /\ P n).
Proof.
  intros. unpack. eauto.
Qed.

(* This variant is analogous, but attacks only one hypothesis, whose name is
   specified. *)

Ltac named_unpack h :=
  revert h;
  match goal with
  | |- ex _ -> _ => intros [ ? h ]; named_unpack h
  | |- (_ /\ _) -> _ => intros [ ? h ]; named_unpack h
  | |- _ -> _ => intro h
  end.

Tactic Notation "unpack" hyp(h) := named_unpack h.

Goal
  forall (P Q : nat -> Prop),
  (exists n, P n /\ Q n) ->
  (exists n, Q n /\ P n).
Proof.
  intros ? ? h. unpack h. eauto.
Qed.

(* This variant is analogous, but attacks a term. *)

Ltac term_unpack t :=
  let h := fresh in
  generalize t; intro h; named_unpack h.

Tactic Notation "unpack" constr(t) := term_unpack t.

Goal
  forall (P Q : nat -> Prop) (x : nat),
  x = 0 ->
  (x = 0 -> exists n, P n /\ Q n) ->
  (exists n, Q n /\ P n).
Proof.
  intros ? ? ? z h. unpack (h z). unpack h. eauto.
Qed.

(* The tactic [xplit] deals with all existential quantifiers and
   conjunctions in the goal. *)

Ltac xplit :=
  repeat match goal with
  | |- exists x, _ => eexists
  | |- _ /\ _ => split
  end.

(* This tactic looks for a disjunctive hypothesis and destructs it. *)

Ltac by_cases :=
  repeat match goal with h: _ \/ _ |- _ => destruct h end.

(* Destructuring triples of propositions. *)

Lemma get1:
  forall A B, A /\ B -> A.
Proof. tauto. Qed.

Lemma get2:
  forall A B C, A /\ B /\ C -> B.
Proof. tauto. Qed.

Lemma get3:
  forall A B C D, A /\ B /\ C /\ D -> C.
Proof. tauto. Qed.

Lemma get4:
  forall A B C D E, A /\ B /\ C /\ D /\ E -> D.
Proof. tauto. Qed.

Lemma get5:
  forall A B C D E F, A /\ B /\ C /\ D /\ E /\ F -> E.
Proof. tauto. Qed.

Lemma last2:
  forall A B, A /\ B -> B.
Proof. tauto. Qed.

Lemma last3:
  forall A B C, A /\ B /\ C -> C.
Proof. tauto. Qed.

Lemma last4:
  forall A B C D, A /\ B /\ C /\ D -> D.
Proof. tauto. Qed.

Lemma last5:
  forall A B C D E, A /\ B /\ C /\ D /\ E -> E.
Proof. tauto. Qed.

Lemma last6:
  forall A B C D E F, A /\ B /\ C /\ D /\ E /\ F -> F.
Proof. tauto. Qed.

(* A convenient function. *)

Definition transpose A B (f : A -> A -> B) x y := f y x.

(* Turn some tactics into hints. *)

Hint Extern 1 => congruence : congruence.

(* ------------------------------------------------------------------------- *)

(* A generic judgement inversion tactic. *)

(* We require the user to provide a [select] tactic, which recognizes the
   judgements that the user potentially wishes to invert. The definition
   of [select] will typically look like this:

     Ltac select action :=
       match goal with
       | h: j _ _ _ |- _ =>
           action h
       end.

   The role of [select action] is to select a hypothesis [h] and pass it
   to [action]. It should fail if no hypothesis can be selected. It can
   also choose to succeed without invoking [action], in which case it
   should somehow make progress (otherwise the process will loop). For
   instance, it could set aside a hypothesis. *)

(* The hypotheses selected by [select] are inverted (destructed) if this
   yields exactly zero or one sub-goal; otherwise, they are set aside using
   [intro] and are re-introduced when the process is over. This is done in
   order to avoid examining a single hypothesis several times and in order to
   avoid divergence. *)

Ltac gji_handle h :=
  (* A hypothesis [h] has been selected for examination. *)
  first [
    (* invert this hypothesis if this yields only one sub-goal *)
    inversion h; [ clear h; try subst ]
  | (* invert this hypothesis if this solves the goal *)
    solve [ inversion h ]
  | (* otherwise, set this hypothesis aside *)
    revert h
  ].

Ltac gji select :=
  (* As long as there exists a suitable hypothesis, handle it. *)
  repeat select gji_handle;
  (* Re-introduce any hypothesis that was set aside. *)
  intros.
  (* maybe a bit violent; one could use marks to avoid introducing too many hypotheses *)

(* The user will typically use these tactics as follows:
     Ltac my_select action := ...
     Ltac my_inversion := gji my_select. *)

(* ------------------------------------------------------------------------- *)

(* The following tactics apply dependent destruction or inversion to the first
   hypothesis that appears in the goal. *)

Ltac dependent_destruction :=
  let h := fresh "hdd" in
  introv h; dependent destruction h.

Ltac dependent_induction :=
  let h := fresh "hdi" in
  introv h; dependent induction h.

(* ------------------------------------------------------------------------- *)

(* The tactic [injections] applies [injection] to the equality hypotheses that
   support it. *)

Ltac injections :=
  repeat match goal with
  | h: exist _ ?x _ = exist _ ?y _ |- _ =>
      assert (x = y); [ congruence | clear h ]
  | h: _ = _ |- _ =>
      first [
        (* Try to use [injection] on this hypothesis. *)
        injection h; clear h
        (* If this fails, set it aside. *)
      | revert h
      ]
  end;
  (* When done, re-introduce the hypotheses that were set aside. *)
  intros;
  (* Try substituting what can be substituted. *)
  try subst.

(* ------------------------------------------------------------------------- *)

(* The tactic [cleanup] simplifies the context by replacing a hypothesis of
   the form [P -> Q] with just [Q] when [P] is already known. It also looks
   for hypotheses of the form [x = y -> Q] and tries to use [eq_refl] as a
   proof of the equality. *)

Ltac cleanup :=
  repeat match goal with
  | ih: ?P -> ?Q, h: ?P |- _ =>
      generalize (ih h); clear ih; intro ih
  | ih: _ = _ -> _ |- _ =>
      generalize (ih eq_refl); clear ih; intro ih
  end.

(* ------------------------------------------------------------------------- *)

(* The tactic [analysis h] applies [dependent destruction] to the hypothesis
   [h], then tries to solve the sub-goals either by contradiction ([omega])
   or using [eauto]. *)

Ltac analysis h :=
  revert h; dependent_destruction; try solve [ omega | eauto ].

(* ------------------------------------------------------------------------- *)

(* The tactic [redundancy] removes one copy of a hypothesis that appears
   twice. *)

Ltac redundancy :=
  repeat match goal with h1: ?P, h2: ?P |- _ => clear h2 end.

