Set Implicit Arguments.
Generalizable All Variables.
Require Import MyList.
Require Import MyTactics.

(* ------------------------------------------------------------------------- *)

(* An allocation map is a map of addresses to values, with support for dynamic
   allocation of fresh addresses. *)

(* An address is implemented as a natural integer. An allocation map is
   implemented as a finite list of values, which we interpret as a finite
   function of addresses to values. We refer to the length of this list
   as the ``allocation limit''. *)

(* Because the combination of two allocation maps is undefined when they
   disagree on the allocation limit, we also introduce an undefined map. *)

Inductive aMap A :=
| MapUndefined: aMap A
| Map: list A -> aMap A.

(* ------------------------------------------------------------------------- *)

(* The tactic [dam] -- for ``destruct allocation maps'' -- does the bulk of
   the preparatory work. *)

Ltac dam :=
  intros;
  repeat match goal with R: aMap _ |- _ => destruct R end;
  simpl in *;
  dblib_by_cases;
  simpl in *;
  injections;
  try solve [ congruence | tauto ];
  try subst;
  try match goal with |- Map _ = Map _ => f_equal end.

(* ------------------------------------------------------------------------- *)

(* These ad hoc tactics select certain hypotheses and perform induction or
   destruction on them. *)

Ltac select_Forall :=
  match goal with h: Forall _ _ |- _ => revert h end.

Ltac select_growth :=
  match goal with h: growth _ _ _ _ |- _ => revert h end.

Ltac destruction_Forall :=
  select_Forall; dependent_destruction.

Ltac induction_growth :=
  select_growth; dependent_induction.

(* ------------------------------------------------------------------------- *)

(* The empty allocation map. *)

Definition empty_map A :=
  Map (@nil A).

(* ------------------------------------------------------------------------- *)

(* A predicate over allocation maps: [everywhere]. *)

(* [everywhere P R] means that [R] is defined and maps every allocated address
   to a value that satisfies [P]. *)

Definition everywhere A (P : A -> Prop) (R : aMap A) : Prop :=
  match R with
  | MapUndefined => False
  | Map m        => Forall P m
  end.

Lemma everywhere_empty:
  forall A (P : A -> Prop),
  everywhere P (empty_map _).
Proof.
  econstructor.
Qed.

(* ------------------------------------------------------------------------- *)

(* A predicate over allocation maps: access. *)

(* The predicate [maps R r a] means that [R] is defined and maps the allocated
   address [r] to the value [a]. *)

Inductive maps A : aMap A -> nat -> A -> Prop :=
| Maps:
    forall m r a,
    is_nth r m a ->
    maps (Map m) r a.

Hint Constructors maps : maps.

Ltac maps_inversion :=
  match goal with h: maps _ _ _ |- _ =>
    inversion h; clear h; try subst
  end.

(* ------------------------------------------------------------------------- *)

(* The predicate [mapsp R l P] means that [R] maps [l] to some element
   that satisfies [P]. *)

Definition mapsp A R l (P : A -> Prop) :=
  exists a,
  maps R l a /\ P a.

Hint Unfold mapsp : mapsp.

Ltac mapsp_inversion :=
  match goal with h: mapsp _ _ _ |- _ =>
    destruct h as [ ? [ ? ? ]]
  end.

(* ------------------------------------------------------------------------- *)

(* A collection of lemmas that involve the above properties. *)

(* The empty map is empty. *)

Lemma maps_empty:
  forall A r a,
  maps (empty_map A) r a ->
  False.
Proof.
  unfold empty_map. dependent_destruction. my_list_cleanup.
Qed.

(* [maps] is injective. *)

Lemma maps_injective:
  forall A R r (a1 a2 : A),
  maps R r a1 ->
  maps R r a2 ->
  a1 = a2.
Proof.
  inversion 1; inversion 1; eauto using is_nth_injective.
Qed.

(* If [R] satisfies [P] everywhere, and if [maps R r a] holds, then [P a] must
   hold. *)

Lemma everywhere_maps:
  forall A (P : A -> Prop) R r a,
  everywhere P R ->
  maps R r a ->
  P a.
Proof.
  inversion 2; simpl; subst. eapply is_nth_Forall; eauto.
Qed.

(* [mapsp] is covariant. *)

Lemma mapsp_covariant:
  forall A R l (P Q : A -> Prop),
  mapsp R l P ->
  (forall a, P a -> Q a) ->
  mapsp R l Q.
Proof.
  unfold mapsp. intros. unpack. eauto.
Qed.

(* ------------------------------------------------------------------------- *)

(* An operation on allocation maps: allocation. *)

(* The allocation map [allocate R a] extends [R] with a newly allocated
   address, which is mapped to [a]. *)

Definition allocate A (R : aMap A) (a : A) :=
  match R with
  | MapUndefined =>
      @MapUndefined _
  | Map m =>
      Map (m ++ a :: nil)
  end.

(* Allocation preserves [everywhere P] if the new value satisfies [P]. *)

Lemma everywhere_allocate:
  forall A (P : A -> Prop) R a,
  everywhere P R ->
  P a ->
  everywhere P (allocate R a).
Proof.
  destruct R; simpl; eauto using Forall_app.
Qed.

(* If [r] points to [a], then this fact remains true after allocating
   a new address. *)

Lemma maps_allocate:
  forall A R r (a b : A),
  maps R r a ->
  maps (allocate R b) r a.
Proof.
  dependent_destruction; econstructor. eauto using is_nth_app_near.
Qed.

(* If, in the heap [allocate R a], [r] points to [b], then either this
   fact was true in [R] already, or [b] is [a]. *)

Lemma maps_allocate_inversion:
  forall A R r (a b : A),
  maps (allocate R a) r b ->
  maps R r b \/ a = b.
Proof.
  destruct R; dependent_destruction.
  forwards [ | ]: is_nth_inversion; eauto with maps.
Qed.

(* ------------------------------------------------------------------------- *)

(* An operation on allocation maps: the next available memory location. *)

(* For convenience, we make this a total function. *)

Definition limit A (R : aMap A) :=
  match R with
  | MapUndefined =>
      0
  | Map m =>
      length m
  end.

Lemma maps_allocate_elsewhere:
  forall A R l (a b : A),
  maps R l b ->
  maps (allocate R a) l b.
Proof.
  dependent_destruction. simpl. eauto using is_nth_app_near with maps.
Qed.

Lemma maps_limit:
  forall A R l (a : A),
  maps R l a ->
  l < limit R.
Proof.
  dependent_destruction. simpl. eauto using is_nth_length.
Qed.

(* [l] is a valid address (below the limit of [R]) if and only if
   [R] maps [l] to something. *)

Lemma limit_maps:
  forall A R l,
  l < limit R <->
  exists a : A,
  maps R l a.
Proof.
  dam; split; intros; unpack.
  false. omega.
  match goal with h: maps _ _ _ |- _ => inversion h end.
  forwards: length_is_nth. eauto. unpack. eauto with maps.
  match goal with h: maps _ _ _ |- _ => inversion h; clear h; subst end.
  eauto using is_nth_length.
Qed.

Lemma limit_mapsp:
  forall A R l,
  l < limit R <->
  mapsp R l (fun (_ : A) => True).
Proof.
  intros. rewrite limit_maps. unfold mapsp.
  split; intros; unpack; eauto.
Qed.

(* ------------------------------------------------------------------------- *)

(* An operation on allocation maps: update. *)

(* The allocation map [update R s a] coincides with [R], except at [s], which
   is now mapped to [a]. In principle, [s] should be an already-allocated
   address. *)

Definition update A (R : aMap A) (s : nat) (a : A) :=
  match R with
  | MapUndefined =>
      @MapUndefined _
  | Map m =>
      Map (set_nth s m a)
  end.

(* [update] does not affect [limit]. *)

Lemma limit_update:
  forall A R s (a : A),
  limit (update R s a) = limit R.
Proof.
  destruct R; simpl; eauto using length_set_nth.
Qed.

(* A characterization of [update] in terms of [maps]. *)

Lemma maps_update_there:
  forall A R R' r s (a1 a2 : A),
  maps R r a1 ->
  r = s ->
  R' = update R s a2 ->
  maps R' r a2.
Proof.
  dependent_destruction; intros; subst; econstructor.
  eauto using is_nth_set_nth_there.
Qed.

Lemma maps_update_elsewhere:
  forall A R r s (a1 a2 : A),
  maps R r a1 ->
  r <> s ->
  maps (update R s a2) r a1.
Proof.
  dependent_destruction; econstructor.
  eauto using is_nth_set_nth_elsewhere.
Qed.

Lemma maps_update_inversion:
  forall A R r s (a b : A),
  maps (update R r a) s b ->
  r <> s /\ maps R s b \/
  r  = s /\ a = b.
Proof.
  destruct R; dependent_destruction.
  forwards [ | ]: is_nth_set_nth_inversion; [ eauto | left | right ]; unpack;
  eauto with maps.
Qed.

(* When the new value is the previous value, [update] is the identity. *)

Lemma update_identity:
  forall A R s (a : A),
  maps R s a ->
  update R s a = R.
Proof.
  dependent_destruction. simpl. f_equal. eauto using set_nth_identity.
Qed.

(* Update commutes with allocation. *)

Lemma update_allocate:
  forall A R l (a1 : A),
  maps R l a1 ->
  forall b a2,
  update (allocate R b) l a2 = allocate (update R l a2) b.
Proof.
  dependent_destruction. dam.
  eauto using set_nth_app_left.
Qed.

(* Update preserves [everywhere P] if the new value satisfies [P]. *)

Lemma everywhere_update:
  forall A (P : A -> Prop) R l a,
  everywhere P R ->
  P a ->
  everywhere P (update R l a).
Proof.
  destruct R; simpl; eauto using Forall_set_nth.
Qed.

(* Update commutes with itself. *)

Lemma update_update:
  forall A R r1 a1 b1 r2 (a2 b2 : A),
  maps R r1 a1 ->
  maps R r2 a2 ->
  r1 <> r2 ->
  update (update R r1 b1) r2 b2 = update (update R r2 b2) r1 b1.
Proof.
  dependent_destruction. dependent_destruction. dam.
  eauto using set_nth_set_nth.
Qed.

Lemma update_overwrite:
  forall A R r (b1 b2 : A),
  update (update R r b1) r b2 = update R r b2.
Proof.
  dam. eauto using set_nth_overwrite.
Qed.

Lemma update_reverse:
  forall A R R' s (a b : A),
  maps R s a ->
  update R s b = R' ->
  R = update R' s a.
Proof.
  intros; subst. symmetry. 
  rewrite update_overwrite.
  eauto using update_identity.
Qed.

(* ------------------------------------------------------------------------- *)

(* [updatef] is a more general version of [update]. Instead of specifying a
   new value [a] to be written into the map at address [l], one specifies a
   function [f], which is applied to the value found at address [l]. *)

Definition updatef A (R : aMap A) (l : nat) (f : A -> A) :=
  match R with
  | MapUndefined =>
      @MapUndefined _
  | Map m =>
      Map (apply_nth l m f)
  end.

Lemma maps_updatef_there:
  forall A R R' r s (a b : A) f,
  maps R r a ->
  r = s ->
  R' = updatef R s f ->
  b = f a ->
  maps R' r b.
Proof.
  dependent_destruction; intros; subst; econstructor.
  eauto using is_nth_apply_nth_there.
Qed.

Lemma maps_updatef_elsewhere:
  forall A R r s (a : A) f,
  maps R r a ->
  r <> s ->
  maps (updatef R s f) r a.
Proof.
  dependent_destruction; intros; subst; econstructor.
  eauto using is_nth_apply_nth_elsewhere.
Qed.

Lemma maps_updatef_inversion:
  forall A R r s f (b : A),
  maps (updatef R r f) s b ->
  r <> s /\ maps  R s b \/
  r  = s /\ mapsp R s (fun a => f a = b).
Proof.
  destruct R; dependent_destruction.
  forwards [ | ]: is_nth_apply_nth_inversion; [ eauto | left | right ]; unpack;
  eauto 6 with maps mapsp.
Qed.

Lemma mapsp_updatef_there:
  forall A f (P Q : A -> Prop),
  (forall a, P a -> Q (f a)) ->
  forall R r s,
  mapsp R r P ->
  r = s ->
  mapsp (updatef R s f) r Q.
Proof.
  intros; subst. mapsp_inversion.
  eauto 6 using maps_updatef_there with mapsp.
Qed.

Lemma mapsp_updatef_elsewhere:
  forall A f (P : A -> Prop),
  forall R r s,
  mapsp R r P ->
  r <> s ->
  mapsp (updatef R s f) r P.
Proof.
  intros; subst. mapsp_inversion. eauto using maps_updatef_elsewhere with mapsp.
Qed.

Lemma mapsp_updatef_anywhere:
  forall A f (P : A -> Prop),
  (forall a, P a -> P (f a)) ->
  forall R r s,
  mapsp R r P ->
  mapsp (updatef R s f) r P.
Proof.
  intros; subst. mapsp_inversion.
  destruct (eq_nat_dec r s); [ subst | ];
  eauto 6 using maps_updatef_there, maps_updatef_elsewhere with mapsp.
Qed.

Lemma mapsp_updatef_inversion:
  forall A (P : A -> Prop) f,
  (forall a, P (f a) -> P a) ->
  forall R r s,
  mapsp (updatef R r f) s P ->
  mapsp R s P.
Proof.
  intros. mapsp_inversion.
  forwards [ | ]: maps_updatef_inversion; eauto; intros; unpack.
  eauto with mapsp.
  eapply mapsp_covariant. eauto. simpl. intros. subst. eauto.
Qed.

Lemma everywhere_updatef:
  forall A (P : A -> Prop) f,
  (forall x, P x -> P (f x)) ->
  forall R l,
  everywhere P R ->
  everywhere P (updatef R l f).
Proof.
  destruct R; simpl; eauto using Forall_apply_nth.
Qed.

Lemma maps_update_updatef:
  forall A R r (a b : A) f,
  maps R r a ->
  b = f a ->
  updatef R r f = update R r b.
Proof.
  destruct R; intros.
  eauto.
  maps_inversion. simpl. f_equal. eauto using is_nth_set_nth_apply_nth.
Qed.

Lemma compose_updatef_updatef:
  forall A f1 f2 g,
  (forall a : A, f2 (f1 a) = g a) ->
  forall R r,
  updatef (updatef R r f1) r f2 = updatef R r g.
Proof.
  dam.
  (* Prove this list lemma on the fly. *)
  generalize dependent r. induction_lists.
  eauto.
  destruct r; simpl; eauto with f_equal.
Qed.

Lemma updatef_identity:
  forall A R s P,
  mapsp R s P ->
  forall f,
  (forall a : A, P a -> f a = a) ->
  updatef R s f = R.
Proof.
  dam. mapsp_inversion. maps_inversion.
  (* Prove this list lemma on the fly. *)
  generalize dependent s. induction_lists; eauto.
Qed.

(* [updatef] commutes with itself. *)

Lemma updatef_updatef:
  forall A R r1 r2 (f : A -> A),
  updatef (updatef R r1 f) r2 f = updatef (updatef R r2 f) r1 f.
Proof.
  dam. generalize dependent r2. generalize dependent r1. induction_lists.
  eauto.
  destruct r1; destruct r2; simpl; eauto with f_equal.
Qed.

Lemma updatef_updatef_elsewhere:
  forall A R r1 r2 (f g : A -> A),
  r1 <> r2 ->
  updatef (updatef R r1 f) r2 g = updatef (updatef R r2 g) r1 f.
Proof.
  dam. generalize dependent r2. generalize dependent r1. induction_lists.
  eauto.
  destruct r1; destruct r2; simpl; eauto with f_equal omega.
Qed.

(* ------------------------------------------------------------------------- *)

(* An operation on allocation maps: transformation. This operation could be
   called [map], but that word is already overused. *)

Section Transform.

Variable A B : Type.

Variable f : A -> B.

Definition transform (R : aMap A) : aMap B :=
  match R with
  | MapUndefined =>
      @MapUndefined _
  | Map m =>
      Map (map f m)
  end.

Lemma everywhere_transform:
  forall (P : A -> Prop) (Q : B -> Prop) R,
  everywhere P R ->
  (forall a, P a -> Q (f a)) ->
  everywhere Q (transform R).
Proof.
  dam. eauto using Forall_map.
Qed.

Lemma maps_transform:
  forall R l a b,
  maps R l a ->
  f a = b ->
  maps (transform R) l b.
Proof.
  inversion 1; intros; subst. econstructor. eauto using is_nth_map.
Qed.

Lemma maps_transform_reverse:
  forall R l b,
  maps (transform R) l b ->
  exists a,
  maps R l a /\ f a = b.
Proof.
  destruct R; simpl; inversion 1; subst.
  forwards: is_nth_map_reverse; [ eauto | unpack ].
  eauto with maps.
Qed.

Lemma limit_transform:
  forall R,
  limit (transform R) = limit R.
Proof.
  dam; eauto using map_length.
Qed.

Lemma transform_allocate:
  forall R a,
  transform (allocate R a) = allocate (transform R) (f a).
Proof.
  dam. eapply map_app.
Qed.

End Transform.

Lemma transform_transform:
  forall A B C (f : A -> B) (g : B -> C) h R,
  (forall a, g (f a) = h a) ->
  transform g (transform f R) = transform h R.
Proof.
  dam. induction_lists; eauto with congruence.
Qed.

(* ------------------------------------------------------------------------- *)

(* An operation on allocation maps: combination. This operation could be
   called [zip], but that name is already used at the level of lists. *)

Definition mzip (A B C : Type) (f : A -> B -> C) R1 R2 :=
  match R1, R2 return _ with
  | MapUndefined, _
  | _, MapUndefined =>
      @MapUndefined _
  | Map m1, Map m2 =>
      if eq_nat_dec (length m1) (length m2) then
        Map (zip f m1 m2)
      else
        @MapUndefined _
  end.

(* [transform] and [mzip] commute as follows. *)

Lemma transform_mzip:
  forall (A B : Type) (f : A -> B) (g : A -> A -> A) (h : B -> B -> B) R1 R2,
  (forall a1 a2, f (g a1 a2) = h (f a1) (f a2)) ->
  transform f (mzip g R1 R2) = mzip h (transform f R1) (transform f R2).
Proof.
  dam; try solve [ repeat rewrite map_length in *; false ].
  induction_lists; eauto with congruence.
Qed.

(* The following lemma would correspond to [get_set], but unfortunately
   has side conditions. *)

Lemma transform_mzip_identity:
  forall (A B C : Type) (f : C -> A) (g : A -> B -> C) m1 m2,
  (forall a b, f (g a b) = a) ->
  m1 <> MapUndefined _ ->
  m2 <> MapUndefined _ ->
  limit m1 = limit m2 ->
  transform f (mzip g m1 m2) = m1.
Proof.
  dam. induction_lists; eauto with congruence.
Qed.

(* The following lemma corresponds to [set_get]. *)

Lemma mzip_transform_identity:
  forall (A B : Type) (f : A -> B) (g : B -> A -> A) m,
  (forall a, g (f a) a = a) ->
  mzip g (transform f m) m = m.
Proof.
  dam; try solve [ rewrite map_length in *; false ].
  induction_lists; eauto with congruence.
Qed.

(* The following lemma would correspond to [set_set], but unfortunately
   has side conditions. *)

Lemma mzip_mzip_idempotent:
  forall (A B : Type) (f : A -> B -> B) m1 m2 m,
  (forall a1 a2 b, f a2 (f a1 b) = f a2 b) ->
  m1 <> MapUndefined _ ->
  limit m1 = limit m ->
  mzip f m2 (mzip f m1 m) = mzip f m2 m.
Proof.
  dam; try solve [ rewrite zip_length_left in * by eauto; false ].
  induction_lists; eauto with congruence.
Qed.

(* ------------------------------------------------------------------------- *)

Section Agreement.

Context `{agrees : A -> B -> Prop}.

(* ------------------------------------------------------------------------- *)

(* Two maps agree if and only if they agree on the allocation limit and they
   agree pointwise at every allocated location. *)

Inductive aMap_agrees : aMap A -> aMap B -> Prop :=
| AMapAgrees:
    forall m1 m2,
    Forall2 agrees m1 m2 ->
    aMap_agrees (Map m1) (Map m2).

(* Some immediate consequences of the definition. *)

Lemma agrees_maps_left_to_right:
  forall R1 R2 l a,
  aMap_agrees R1 R2 ->
  maps R1 l a ->
  exists b,
  maps R2 l b /\
  agrees a b.
Proof.
  do 2 dependent_destruction.
  forwards: Forall2_is_nth_left_to_right; [ eauto | eauto | unpack ].
  xplit. econstructor; eauto. eauto.
Qed.

Lemma agrees_maps_right_to_left:
  forall R1 R2 l b,
  aMap_agrees R1 R2 ->
  maps R2 l b ->
  exists a,
  maps R1 l a /\
  agrees a b.
Proof.
  do 2 dependent_destruction.
  forwards: Forall2_is_nth_right_to_left; [ eauto | eauto | unpack ].
  xplit. econstructor; eauto. eauto.
Qed.

Lemma agrees_maps_maps:
  forall R1 R2 l a b,
  aMap_agrees R1 R2 ->
  maps R1 l a ->
  maps R2 l b ->
  agrees a b.
Proof.
  do 3 dependent_destruction. eapply Forall2_is_nth; eauto.
Qed.

(* Two empty maps agree. *)

Lemma agrees_empty:
  aMap_agrees (empty_map A) (empty_map B).
Proof.
  repeat econstructor.
Qed.

(* Agreement implies equality of limits. *)

Lemma agrees_limit:
  forall R1 R2,
  aMap_agrees R1 R2 ->
  limit R1 = limit R2.
Proof.
  dependent_destruction. simpl. eauto using Forall2_length.
Qed.

(* Allocation preserves agreement. *)

Lemma agrees_allocate:
  forall R1 R2 a b,
  aMap_agrees R1 R2 ->
  agrees a b ->
  aMap_agrees (allocate R1 a) (allocate R2 b).
Proof.
  dependent_destruction; intros; econstructor.
  eapply Forall2_app; eauto. (* part of the standard library! *)
Qed.

(* Update preserves agreement. *)

Lemma agrees_update:
  forall R1 R2 l a b,
  aMap_agrees R1 R2 ->
  agrees a b ->
  aMap_agrees (update R1 l a) (update R2 l b).
Proof.
  dependent_destruction; intros; econstructor.
  eauto using Forall2_set_nth.
Qed.

(* A combination of [agrees_update] and [update_identity]. *)

Lemma agrees_update_identity:
  forall R1 R2 l a b,
  aMap_agrees R1 R2 ->
  maps R1 l a ->
  agrees a b ->
  aMap_agrees R1 (update R2 l b).
Proof.
  intros. equates 2.
  eauto using @agrees_update.
  symmetry. eauto using @update_identity.
Qed.

End Agreement.

Implicit Arguments aMap_agrees [ A B ].

Hint Resolve @agrees_empty @agrees_allocate @agrees_update : agrees.

(* ------------------------------------------------------------------------- *)

(* This tactic helps use the lemma [maps_injective]. *)

Ltac maps_injective :=
  match goal with h1: maps ?R ?x _, h2: maps ?R ?x _ |- _ =>
    generalize (maps_injective h1 h2); intro; clear h2; try subst
  end.

(* ------------------------------------------------------------------------- *)

(* The notions defined in this module should be opaque. I hope. *)

Global Opaque empty_map allocate limit update.

