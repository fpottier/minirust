Set Implicit Arguments.
Require Export List.
Require Import MyTactics.

(* ---------------------------------------------------------------------------- *)

(* [repeat n a] is a list of [n] copies of the element [a]. *)

Fixpoint repeat A (n : nat) (a : A) : list A :=
  match n with 0 => nil | S n => a :: repeat n a end.

(* ---------------------------------------------------------------------------- *)

(* If every element satisfies [P], and if [P] implies [Q], then every element
   satisfies [Q]. *)

Lemma Forall_covariant:
  forall A (P Q : A -> Prop) xs,
  Forall P xs ->
  (forall x, P x -> Q x) ->
  Forall Q xs.
Proof.
  induction 1; econstructor; eauto.
Qed.

(* If every element of [xs] satisfies [P], and if [f] maps [P] to [Q],
   then every element of [map f xs] satisfies [Q]. *)

Lemma Forall_map:
  forall A B (f : A -> B) (P : A -> Prop) (Q : B -> Prop) xs,
  Forall P xs ->
  (forall x, P x -> Q (f x)) ->
  Forall Q (map f xs).
Proof.
  induction 1; simpl; eauto.
Qed.

Lemma Forall_map_reverse:
  forall A B (f : A -> B) (P : A -> Prop) (Q : B -> Prop) xs,
  Forall Q (map f xs) ->
  (forall x, Q (f x) -> P x) ->
  Forall P xs.
Proof.
  induction xs; simpl; inversion 1; eauto.
Qed.

(* If every element of [xs] satisfies [P] and every element of [ys]
   satisfies [P], then every element of [xs ++ ys] satisfies [P]. *)

Lemma Forall_app:
  forall A (P : A -> Prop) (xs ys : list A),
  Forall P xs ->
  Forall P ys ->
  Forall P (xs ++ ys).
Proof.
  induction 1; simpl; eauto.
Qed.

(* ---------------------------------------------------------------------------- *)

Lemma Forall2_length:
  forall A B (R : A -> B -> Prop) xs ys,
  Forall2 R xs ys ->
  length xs = length ys.
Proof.
  induction 1; simpl; eauto.
Qed.

Lemma Forall2_Forall_modus_ponens:
  forall A B : Type,
  forall P : A -> B -> Prop,
  forall Q : B -> Prop,
  (forall a b, P a b -> Q b) ->
  forall xs ys,
  Forall2 P xs ys ->
  Forall Q ys.
Proof.
  induction 2; econstructor; eauto.
Qed.

(* ---------------------------------------------------------------------------- *)

(* A definition of [nth] as a relation. *)

Inductive is_nth A : nat -> list A -> A -> Prop :=
| IsNthZero:
    forall x xs,
    is_nth 0 (x :: xs) x
| IsNthSucc:
    forall n y x xs,
    is_nth n xs y ->
    is_nth (S n) (x :: xs) y.

Hint Constructors is_nth : is_nth.

(* This tactic proves that [is_nth n xs x] implies that [xs] is non-empty. *)

Ltac is_nth_nonempty :=
  match goal with h: is_nth _ ?xs _ |- _ =>
    destruct xs; [ inversion h | ]
  end.

(* ---------------------------------------------------------------------------- *)

(* Lemmas about [is_nth]. *)

(* If every element satisfies [P], then the [n]-th element satisfies [P]. *)

Lemma is_nth_Forall:
  forall A P n xs (x : A),
  is_nth n xs x ->
  Forall P xs ->
  P x.
Proof.
  induction 1; inversion 1; subst; eauto.
Qed.

(* If [x] is the [n]-th element of [xs], then [f x] is the [n]-th element
   of [map f xs]. *)

Lemma is_nth_map:
  forall A B (f : A -> B) n xs x,
  is_nth n xs x ->
  is_nth n (map f xs) (f x).
Proof.
  induction 1; econstructor; eauto.
Qed.

Lemma is_nth_map_reverse:
  forall A B (f : A -> B) xs n y,
  is_nth n (map f xs) y ->
  exists x,
  is_nth n xs x /\ f x = y.
Proof.
  induction xs; simpl; dependent_destruction.
  repeat econstructor.
  forwards: IHxs. eauto. unpack.
  repeat econstructor; eauto.
Qed.

(* [is_nth] is injective. *)

Lemma is_nth_injective:
  forall A xs n (x1 x2 : A),
  is_nth n xs x1 ->
  is_nth n xs x2 ->
  x1 = x2.
Proof.
  induction 1; inversion 1; eauto.
Qed.

(* If [x] is the [n]-th element of [xs], then [xs] has length greater than [n]. *)

Lemma is_nth_length:
  forall A n (xs : list A) x,
  is_nth n xs x ->
  n < length xs.
Proof.
  induction 1; simpl; eauto with omega.
Qed.

(* Conversely, if has length greater than [n], then some [x] is the [n]-th
   element of [xs]. *)

Lemma length_is_nth:
  forall A (xs : list A) n,
  n < length xs ->
  exists x,
  is_nth n xs x.
Proof.
  induction xs; simpl; intros; [ false; omega | destruct n ].
  repeat econstructor.
  forwards: IHxs. instantiate (1 := n). omega. unpack. repeat econstructor; eauto.
Qed.

(* A combination of the above two lemmas. *)

Lemma is_nth_common_length:
  forall A n (xs : list A) x,
  is_nth n xs x ->
  forall B (ys : list B),
  length xs = length ys ->
  exists y,
  is_nth n ys y.
Proof.
  introv ? heq.
  eapply length_is_nth.
  rewrite <- heq.
  eauto using is_nth_length.
Qed.

(* Looking for the [n]-th element of [xs ++ ys]. *)

Lemma is_nth_app_near:
  forall A (xs ys : list A) n x,
  is_nth n xs x ->
  is_nth n (xs ++ ys) x.
Proof.
  induction 1; simpl; econstructor; eauto.
Qed.

Lemma is_nth_app_far:
  forall A (xs ys : list A) k n y,
  is_nth k ys y ->
  length xs + k = n ->
  is_nth n (xs ++ ys) y.
Proof.
  induction xs; simpl; intros.
  replace n with k by omega. assumption.
  destruct n; [ false; omega | ].
  econstructor. eauto.
Qed.

Lemma Forall2_is_nth:
  forall A B (R : A -> B -> Prop) xs ys,
  Forall2 R xs ys ->
  forall n x y,
  is_nth n xs x ->
  is_nth n ys y ->
  R x y.
Proof.
  induction 1; inversion 1; inversion 1; subst; eauto.
Qed.

Lemma Forall2_is_nth_left_to_right:
  forall A B (R : A -> B -> Prop) xs ys,
  Forall2 R xs ys ->
  forall n x,
  is_nth n xs x ->
  exists y,
  is_nth n ys y /\ R x y.
Proof.
  dependent_induction; dependent_destruction.
  repeat econstructor; eauto.
  forwards: IHhdi. eauto. unpack.
  repeat econstructor; eauto.
Qed.

Lemma Forall2_is_nth_right_to_left:
  forall A B (R : A -> B -> Prop) xs ys,
  Forall2 R xs ys ->
  forall n y,
  is_nth n ys y ->
  exists x,
  is_nth n xs x /\ R x y.
Proof.
  dependent_induction; dependent_destruction.
  repeat econstructor; eauto.
  forwards: IHhdi. eauto. unpack.
  repeat econstructor; eauto.
Qed.

Lemma is_nth_inversion:
  forall A (xs : list A) n x y,
  is_nth n (xs ++ x :: nil) y ->
  is_nth n xs y \/ x = y.
Proof.
  induction xs; simpl; dependent_destruction.
  right. eauto.
  inversion hdd.
  left. econstructor.
  forwards [ | ]: IHxs; [ eauto | left | right ].
    econstructor; eauto.
    eauto.
Qed.

(* ---------------------------------------------------------------------------- *)

(* A function that updates the [n]-th element of a list. *)

Fixpoint set_nth A (n : nat) (xs : list A) (y : A) : list A :=
  match n, xs with
  | 0, _ :: xs =>
      y :: xs
  | S n, x :: xs =>
      x :: set_nth n xs y
  | _, nil =>
      nil (* dummy; considered non-sensical *)
  end.

(* ---------------------------------------------------------------------------- *)

(* Lemmas about [set_nth]. *)

Lemma Forall_set_nth:
  forall A (P : A -> Prop) (n : nat) (xs : list A) (y : A),
  Forall P xs ->
  P y ->
  Forall P (set_nth n xs y).
Proof.
  induction n; inversion 1; simpl; intros; eauto.
Qed.

Lemma Forall2_set_nth:
  forall A B (R : A -> B -> Prop) xs ys x y,
  Forall2 R xs ys ->
  R x y ->
  forall n,
  Forall2 R (set_nth n xs x)(set_nth n ys y).
Proof.
  induction 1; destruct n; simpl; intros; econstructor; eauto.
Qed.

Lemma is_nth_set_nth_there:
  forall A n (xs : list A) x1 x2,
  is_nth n xs x1 ->
  is_nth n (set_nth n xs x2) x2.
Proof.
  induction 1; simpl; econstructor; eauto.
Qed.

Lemma is_nth_set_nth_elsewhere:
  forall A n (xs : list A) x1 x2,
  is_nth n xs x1 ->
  forall m,
  m <> n ->
  is_nth n (set_nth m xs x2) x1.
Proof.
  induction 1; simpl; intros; destruct m; solve [
    false; omega
  | econstructor; eauto
  ].
Qed.

Lemma set_nth_identity:
  forall A n (xs : list A) x,
  is_nth n xs x ->
  set_nth n xs x = xs.
Proof.
  induction 1; simpl; f_equal; eauto.
Qed.

Lemma length_set_nth:
  forall A (xs : list A) n y,
  length (set_nth n xs y) = length xs.
Proof.
  induction xs; destruct n; intros; simpl; eauto.
Qed.

Lemma is_nth_set_nth_inversion:
  forall A (xs : list A) m n x1 x2,
  is_nth n (set_nth m xs x1) x2 ->
  m <> n /\ is_nth n xs x2 \/
  m  = n /\ x1 = x2.
Proof.
  induction xs; destruct m; simpl; dependent_destruction. 
  right. eauto.
  left. eauto with is_nth.
  left. eauto with is_nth.
  forwards [ | ]: IHxs; [ eauto | left | right ]; unpack;
  eauto with omega is_nth.
Qed.

Lemma set_nth_app_left:
  forall A n (xs : list A) x1,
  is_nth n xs x1 ->
  forall ys x2,
  set_nth n (xs ++ ys) x2 = set_nth n xs x2 ++ ys.
Proof.
  induction 1; simpl; intros; eauto with f_equal.
Qed.
  
Lemma set_nth_set_nth:
  forall A (xs : list A) n1 a1,
  is_nth n1 xs a1 ->
  forall n2 a2,
  is_nth n2 xs a2 ->
  n1 <> n2 ->
  forall b1 b2,
  set_nth n2 (set_nth n1 xs b1) b2 = set_nth n1 (set_nth n2 xs b2) b1.
Proof.
  induction 1; inversion 1; intros; simpl; subst; eauto with falseomega f_equal omega.
Qed.

Lemma set_nth_overwrite:
  forall A n (xs : list A) y1 y2,
  set_nth n (set_nth n xs y1) y2 = set_nth n xs y2.
Proof.
  induction n; destruct xs; intros; simpl; eauto with f_equal.
Qed.

Lemma map_set_nth:
  forall A B (f : A -> B) n xs y,
  map f (set_nth n xs y) =
  set_nth n (map f xs) (f y).
Proof.
  induction n; destruct xs; intros; simpl; eauto with f_equal.
Qed.

(* ---------------------------------------------------------------------------- *)

(* A function that applies a transformation [f] to the [n]-th element of a list.
   This can be viewed as a generalization of [set_nth]. *)

Fixpoint apply_nth A (n : nat) (xs : list A) (f : A -> A) { struct xs } : list A :=
  match xs, n with
  | nil, _ =>
      nil (* dummy; considered non-sensical *)
  | x :: xs, 0 =>
      f x :: xs
  | x :: xs, S n =>
      x :: apply_nth n xs f
  end.

Lemma is_nth_set_nth_apply_nth:
  forall A (xs: list A) n a f,
  is_nth n xs a ->
  apply_nth n xs f = set_nth n xs (f a).
Proof.
  induction xs. 
  destruct n; simpl; eauto.
  destruct n; inversion 1; subst; simpl; [ eauto | f_equal; eauto ].
Qed.

Lemma length_apply_nth:
  forall A (xs : list A) n f,
  length (apply_nth n xs f) = length xs.
Proof.
  induction xs; destruct n; intros; simpl; eauto.
Qed.

Lemma Forall_apply_nth:
  forall A (P : A -> Prop) f,
  (forall x, P x -> P (f x)) ->
  forall n xs,
  Forall P xs ->
  Forall P (apply_nth n xs f).
Proof.
  induction n; inversion 1; simpl; intros; eauto.
Qed.

Lemma is_nth_apply_nth_there:
  forall A n xs f (x : A),
  is_nth n xs x ->
  is_nth n (apply_nth n xs f) (f x).
Proof.
  induction 1; simpl; econstructor; eauto.
Qed.

Lemma is_nth_apply_nth_elsewhere:
  forall A n xs f (x : A),
  is_nth n xs x ->
  forall m,
  m <> n ->
  is_nth n (apply_nth m xs f) x.
Proof.
  induction 1; simpl; intros; destruct m; solve [
    false; omega
  | econstructor; eauto
  ].
Qed.

Lemma is_nth_apply_nth_inversion:
  forall A (xs : list A) m n x2 f,
  is_nth n (apply_nth m xs f) x2 ->
  m <> n /\ is_nth n xs x2 \/
  m  = n /\ exists x1, is_nth n xs x1 /\ f x1 = x2.
Proof.
  induction xs; destruct m; simpl; dependent_destruction. 
  right. eauto with is_nth.
  left. eauto with is_nth.
  left. eauto with is_nth.
  forwards [ | ]: IHxs; [ eauto | left | right ]; unpack;
  eauto with omega is_nth.
Qed.

(* ---------------------------------------------------------------------------- *)

(* The combinator [zip] maps a function [f] over two lists [xs] and [ys]. *)

Fixpoint zip A B C (f : A -> B -> C) (xs : list A) (ys : list B) : list C :=
  match xs, ys with
  | nil, _
  | _, nil =>
      nil
  | x :: xs, y :: ys =>
      f x y :: zip f xs ys
  end.

(* ---------------------------------------------------------------------------- *)

(* If [x] and [y] are the [n]-th elements of [xs] and [ys], then [f x y] is
   the [n]-th element of [zip f xs ys]. *)

Lemma is_nth_zip:
  forall A B C (f : A -> B -> C) n xs x,
  is_nth n xs x ->
  forall ys y,
  is_nth n ys y ->
  is_nth n (zip f xs ys) (f x y).
Proof.
  induction 1; inversion 1; subst; simpl; econstructor; eauto.
Qed.

Lemma is_nth_zip_eq:
  forall A B C (f : A -> B -> C) n xs x,
  is_nth n xs x ->
  forall ys y,
  is_nth n ys y ->
  forall z,
  z = f x y ->
  is_nth n (zip f xs ys) z.
Proof.
  intros; subst; eauto using is_nth_zip.
Qed.

Lemma zip_set_nth:
  forall A B C (f : A -> B -> C) n xs ys x y,
  zip f (set_nth n xs x) (set_nth n ys y) =
  set_nth n (zip f xs ys) (f x y).
Proof.
  induction n; destruct xs; destruct ys; intros; simpl; eauto with f_equal.
Qed.

(* [zip] preserves the length of the lists when there is agreement. *)

Lemma zip_length_left:
  forall A B C (f : A -> B -> C) (xs : list A) (ys : list B),
  length xs = length ys ->
  length (zip f xs ys) = length xs.
Proof.
  induction xs; destruct ys; simpl; eauto.
Qed.

Lemma zip_length_right:
  forall A B C (f : A -> B -> C) (xs : list A) (ys : list B),
  length xs = length ys ->
  length (zip f xs ys) = length ys.
Proof.
  induction xs; destruct ys; simpl; eauto.
Qed.

(* If [f] is commutative, then [zip f] is commutative. *)

Lemma zip_commutative:
  forall A C (f : A -> A -> C),
  (forall x y, f x y = f y x) ->
  forall (xs ys : list A),
  zip f xs ys = zip f ys xs.
Proof.
  induction xs; destruct ys; simpl; eauto with f_equal.
Qed.

(* If [f] is associative, then [zip f] is associative. *)

Lemma zip_associative:
  forall A (f : A -> A -> A),
  (forall x y z, f x (f y z) = f (f x y) z) ->
  forall (xs ys zs : list A),
  zip f xs (zip f ys zs) = zip f (zip f xs ys) zs.
Proof.
  induction xs; destruct ys; destruct zs; simpl; eauto with f_equal.
Qed.

(* An ad hoc lemma about [zip] and [map]. *)

Lemma zip_map_right:
  forall A B (f : A -> B -> A) (g : A -> B),
  (forall x, f x (g x) = x) ->
  forall xs,
  zip f xs (map g xs) = xs.
Proof.
  induction xs; simpl; eauto with f_equal.
Qed.

(* [zip] and [++] commute. *)

Lemma zip_app:
  forall A B C (f : A -> B -> C) xs1 xs2 ys1 ys2,
  length xs1 = length xs2 ->
  length ys1 = length ys2 ->
  zip f (xs1 ++ ys1) (xs2 ++ ys2) =
  zip f xs1 xs2 ++ zip f ys1 ys2.
Proof.
  induction xs1; destruct xs2; simpl; intros;
  solve [ false; omega | eauto with f_equal].
Qed.

(* [zip] applied to [nil] is [nil]. *)

Lemma zip_nil_right:
  forall A B C (f : A -> B -> C) xs,
  zip f xs nil = nil.
Proof.
  destruct xs; reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)

(* The predicate [growth P Q xs ys] means that [xs] ``has grown'' into [ys].
   More precisely, the list [ys] is potentially longer than the list [xs].
   At indices that exist in both lists, the elements of [xs] and [ys] are
   related by [P]. At indices that exist only in the list [ys], the elements
   satisfy [Q]. *)

Inductive growth A B (P : A -> B -> Prop) (Q : B -> Prop) : list A -> list B -> Prop :=
| GrowthZero:
    forall ys,
    Forall Q ys ->
    growth P Q nil ys
| GrowthSucc:
    forall x xs y ys,
    P x y ->
    growth P Q xs ys ->
    growth P Q (x :: xs) (y :: ys).

(* ------------------------------------------------------------------------- *)

(* If [P] is reflexive, then [growth P Q] is reflexive. *)

Lemma growth_reflexive:
  forall A (P : A -> A -> Prop) (Q : A -> Prop),
  (forall x, P x x) ->
  forall xs,
  growth P Q xs xs.
Proof.
  induction xs; econstructor; eauto.
Qed.

(* If [xs] grows to [ys], and if [x] is the [n]-th element of [xs], then [ys]
   has an [n]-th element [y] which is related to [x] by [P]. *)

Lemma growth_is_nth:
  forall A B (P : A -> B -> Prop) (Q : B -> Prop) xs ys,
  growth P Q xs ys ->
  forall n x,
  is_nth n xs x ->
  exists y,
  is_nth n ys y /\ P x y.
Proof.
  induction 1; dependent_destruction; subst.
  repeat econstructor; eauto.
  forwards: IHgrowth; [ eauto | unpack ].
  repeat econstructor; eauto.
Qed.

Lemma growth_is_nth_reverse:
  forall A B (P : A -> B -> Prop) (Q : B -> Prop) xs ys,
  growth P Q xs ys ->
  forall n y,
  is_nth n ys y ->
  (exists x, is_nth n xs x /\ P x y) \/ Q y.
Proof.
  dependent_induction.
  right. eapply is_nth_Forall; eauto.
  dependent_destruction.
  left. repeat econstructor; eauto.
  forwards h: IHhdi. eauto. destruct h; unpack.
  left. repeat econstructor; eauto.
  right. eauto.
Qed.

Lemma growth_set_nth:
  forall A (P : A -> A -> Prop) (Q : A -> Prop) n xs x1 x2,
  (forall x, P x x) ->
  is_nth n xs x1 ->
  P x1 x2 ->
  growth P Q xs (set_nth n xs x2).
Proof.
  induction 2; simpl; econstructor; eauto using growth_reflexive.
Qed.

Lemma growth_set_nth_set_nth:
  forall A (P : A -> A -> Prop) (Q : A -> Prop) n xs d x y,
  is_nth n xs d ->
  forall ys,
  growth P Q xs ys ->
  P x y ->
  growth P Q (set_nth n xs x) (set_nth n ys y).
Proof.
  induction 1; inversion 1; intros; subst; simpl; econstructor; eauto.
  (* I don't even know what I am doing *)
Qed.

Lemma growth_apply_nth_apply_nth:
  forall A (P : A -> A -> Prop) (Q : A -> Prop) n xs d f,
  (forall x y, P x y -> P (f x) (f y)) ->
  is_nth n xs d ->
  forall ys,
  growth P Q xs ys ->
  growth P Q (apply_nth n xs f) (apply_nth n ys f).
Proof.
  induction 2; inversion 1; intros; subst; simpl; econstructor; eauto.
  (* I don't even know what I am doing, but I am really happy. *)
Qed.

(* If [P] is reflexive and if every element of [ys] satisfies [Q], then [xs]
   can grow to [xs ++ ys]. *)

Lemma growth_app:
  forall A (P : A -> A -> Prop) (Q : A -> Prop),
  (forall x, P x x) ->
  forall xs ys,
  Forall Q ys ->
  growth P Q xs (xs ++ ys).
Proof.
  induction xs; intros; simpl; econstructor; eauto.
Qed.

Lemma growth_length:
  forall A (P : A -> A -> Prop) (Q : A -> Prop) xs ys,
  growth P Q xs ys ->
  length xs <= length ys.
Proof.
  induction 1; simpl; eauto with omega.
Qed.

Lemma growth_map_map:
  forall (A B A' B' : Type) (P : A -> B -> Prop) (P' : A' -> B' -> Prop) Q Q' f g xs ys,
  (forall x y, P x y -> P' (f x) (g y)) ->
  (forall ys, Forall Q ys -> Forall Q' (map g ys)) ->
  growth P Q xs ys ->
  growth P' Q' (map f xs) (map g ys).
Proof.
  induction 3; simpl; econstructor; eauto.
Qed.

(* ---------------------------------------------------------------------------- *)

(* This handy tactic does a lot of useful work in the presence of lists. *)

Ltac my_list_cleanup :=
  injections;
  simpl in *;
  try discriminate;
  match goal with
    (* simplify cons-cons goal *)
  | |- _ :: _ = _ :: _ =>
      f_equal; my_list_cleanup
    (* simplify Forall-cons hypothesis *)
  | h: Forall _ (_ :: _) |- _ =>
      inversion h; clear h; my_list_cleanup
    (* simplify length-nil hypothesis *)
  | h: 0 = length ?xs |- _ =>
      destruct xs; [ clear h | false ]; my_list_cleanup
  | h: length ?xs = 0 |- _ =>
      destruct xs; [ clear h | false ]; my_list_cleanup
    (* simplify length-cons hypothesis *)
  | h: S _ = length ?xs |- _ =>
      destruct xs; [ false | ]; my_list_cleanup
  | h: length ?xs = S _ |- _ =>
      destruct xs; [ false | ]; my_list_cleanup
    (* simplify is-nth-nil hypothesis *)
  | h: is_nth _ nil _ |- _ =>
      inversion h; clear h; my_list_cleanup
    (* simplify is-nth-cons hypothesis *)
  | h: is_nth _ (_ :: _) _ |- _ =>
      inversion h; clear h; my_list_cleanup
    (* simplify nil-equal-zip or cons-equal-zip hypothesis *)
  | h: nil = zip _ ?xs ?ys |- _ =>
      destruct xs; destruct ys; simpl in h; try solve [ discriminate ]; my_list_cleanup
  | h: zip _ ?xs ?ys = nil |- _ =>
      destruct xs; destruct ys; simpl in h; try solve [ discriminate ]; my_list_cleanup
  | h: _ :: _ = zip _ ?xs ?ys |- _ =>
      destruct xs; destruct ys; simpl in h; try solve [ discriminate ]; my_list_cleanup
  | h: zip _ ?xs ?ys = _ :: _ |- _ =>
      destruct xs; destruct ys; simpl in h; try solve [ discriminate ]; my_list_cleanup
  | _ =>
      idtac
  end.

(* ---------------------------------------------------------------------------- *)

(* This tactic finds all lists in the hypotheses and performs induction on one
   of them and destruction on the others. *)

Ltac induction_lists :=
  repeat match goal with xs: list _ |- _ => generalize dependent xs end;
  intro xs; induction xs;
  repeat match goal with |- forall xs: list _, _ => intro ys; destruct ys end;
  intros; my_list_cleanup.

