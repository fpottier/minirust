Set Implicit Arguments.
Require Import MyTactics.
Require Import MyList.
Require Import AllocationMaps.
Require Import DeBruijn.
Require Import Environments.
Require Import Syntax.
Require Import WellKindedness.

(* A simple memory model. *)

(* ---------------------------------------------------------------------------- *)

(* A block maps offsets to closed values of kind [VALUE]. We represent a block
   as an allocation map; the length of the block is encoded as the allocation
   limit of the map. In principle, the length of a block does not change with
   time. *)

Definition block :=
  aMap syntax.

(* ---------------------------------------------------------------------------- *)

(* A heap maps base addresses to blocks. *)

Definition heap :=
  aMap block.

(* ---------------------------------------------------------------------------- *)

(* Address arithmetic acts on the offset component only. *)

Definition address_add (a : address) (z : offset) : address :=
  let (b, o) := a in
  (b, o + z).

(* The successor of an address. *)

Definition address_succ (a : address) : address :=
  address_add a 1.

(* ---------------------------------------------------------------------------- *)

(* Validity of (a one-word range at) an address. *)

Definition valid_addr (h : heap) (a : address) : Prop :=
  let (b, o) := a in
  mapsp h b (fun bk => mapsp bk o (fun _ => True)).

(* Validity of an address range, defined by a start address and a size. *)

Fixpoint valid_range (h : heap) (a : address) (z : size) : Prop :=
  match z with
  | 0 =>
      True
  | S z =>
      valid_addr h a /\ valid_range h (address_succ a) z
  end.

(* ---------------------------------------------------------------------------- *)

(* A single-word read. *)

Definition read (h : heap) (src : address) (v : syntax) : Prop :=
  (* Extract the base and offset. *)
  let (b, o) := src in
  (* Looking up the base address in the heap should yield a block.
     Looking up the offset in the block should yield the value [v]. *)
  mapsp h b (fun bk => maps bk o v).

(* A multi-word read. *)

Fixpoint read_range (h : heap) (src : address) (z : size) (vs : list syntax) : Prop :=
  match z, vs with
  | 0, nil =>
      True
  | S z, v :: vs =>
      read h src v /\
      read_range h (address_succ src) z vs
  | _, _ =>
      False
  end.

(* ---------------------------------------------------------------------------- *)

(* A single-word write. *)

(* The functions [updatef] and [update] have no effect if the index is out of
   range. Thus, we must explicitly check that the address [dst] is valid. *)

Definition write (h : heap) (dst : address) (v : syntax) (h' : heap) : Prop :=
  valid_addr h dst /\
  (* Extract the base and offset. *)
  let (b, o) := dst in
  (* Update the heap at the base address. Update the block there at
     the desired offset. *)
  updatef h b (fun bk => update bk o v) = h'.

(* Multi-word write. *)

Fixpoint write_range (h : heap) (dst : address) (z : size) (vs : list syntax) (h' : heap) :=
  match z, vs with
  | 0, nil =>
      h = h'
  | S z, v :: vs =>
      exists h1,
      write h dst v h1 /\
      write_range h1 (address_succ dst) z vs h'
  | _, _ =>
      False
  end.

(* ---------------------------------------------------------------------------- *)

(* A definition of what it means for two memory ranges to be disjoint. *)

Definition disjoint_intervals (o1 : offset) (z1 : size) (o2 : offset) (z2 : size) : Prop :=
  o1 + z1 <= o2 \/ o2 + z2 <= o1.

Definition disjoint_ranges (a1 : address) (z1 : size) (a2 : address) (z2 : size) : Prop :=
  let (b1, o1) := a1 in
  let (b2, o2) := a2 in
  (* Either the base addresses are distinct, which means that these ranges
     lie within two distinct memory blocks; *)
  b1 <> b2 \/
  (* Or (if they lie within the same block) they represent disjoint intervals
     within that block. *)
  disjoint_intervals o1 z1 o2 z2.

(* ---------------------------------------------------------------------------- *)

(* Multi-word copy. *)

(* We explicitly disallow a copy whose source and destination ranges overlap.
   This guarantees that a simple-minded implementation of copying is correct. *)

(* TEMPORARY (in fact, we could prove that) *)

Definition copy (h : heap) (dst : address) (z : size) (src : address) (h' : heap) : Prop :=
  disjoint_ranges src z dst z /\
  exists vs,
  read_range h src z vs /\
  write_range h dst z vs h'.

(* ---------------------------------------------------------------------------- *)

(* Memory allocation. Newly allocated memory blocks are not initialized;
   that is, they are initialized with garbage. Memory allocation always
   succeeds (there is no point in modeling an out-of-memory failure, as
   we cannot statically prevent it). *)

Definition new_block (z : size) : block :=
  Map (repeat z SGarbage).

Definition malloc (h : heap) (z : size) : heap * address :=
  (* The heap is extended with a new block. *)
  let h' := allocate h (new_block z) in
  (* The address of this new block. *)
  let a  := (limit h, 0) in
  (* A pair of the new heap and the address. *)
  (h', a).

(* ---------------------------------------------------------------------------- *)

(* Memory de-allocation. *)

Definition delete (h : heap) (a : address) (h' : heap) : Prop :=
  (* De-allocation requires a base address. The offset component of [a]
     must be zero. *)
  let (b, o) := a in
  o = 0 /\
  (* We use [MapUndefined] to indicate that a block has been de-allocated.
     This will cause any future accesses to this block to fail. *)
  update h b (MapUndefined _) = h'.

(* ---------------------------------------------------------------------------- *)

(* Validity is equivalent to the success of a read. *)

Lemma valid_addr_implies_read:
  forall h a,
  valid_addr h a <-> exists v, read h a v.
Proof.
  unfold valid_addr, read, mapsp. da. split; intros; unpack; eauto.
Qed.

Lemma valid_range_implies_read_range:
  forall z h a,
  valid_range h a z <-> exists vs, read_range h a z vs.
Proof.
  induction z; simpl; split; intros; unpack.
  exists (@nil syntax). eauto.
  eauto.
  rewrite valid_addr_implies_read in *. rewrite IHz in *. unpack.
  match goal with v: syntax, vs: list syntax |- _ => exists (cons v vs) end. eauto.
  rewrite valid_addr_implies_read. rewrite IHz.
  match goal with vs: list syntax |- _ => destruct vs end; unpack. tauto. eauto.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Validity is equivalent to the success of a write. *)

Lemma valid_addr_implies_write:
  forall h a v,
  valid_addr h a ->
  exists h',
  write h a v h'.
Proof.
  unfold write. da. eauto.
Qed.

Lemma write_implies_valid_addr:
  forall h a v h',
  write h a v h' ->
  valid_addr h a.
Proof.
  unfold write. da. unpack. eauto.
Qed.

Lemma write_preserves_valid_addr:
  forall h a a' v h',
  valid_addr h a ->
  write h a' v h' ->
  valid_addr h' a.
Proof.
  unfold write, valid_addr. da. unpack. subst.
  eapply mapsp_updatef_anywhere; eauto.
  intro bk. do 2 rewrite <- limit_mapsp. rewrite limit_update. eauto.
Qed.

Lemma write_preserves_valid_addr_reverse:
  forall h a a' v h',
  valid_addr h' a ->
  write h a' v h' ->
  valid_addr h a.
Proof.
  unfold write, valid_addr. da. unpack. subst.
  eapply mapsp_updatef_inversion; eauto.
  intro bk. do 2 rewrite <- limit_mapsp. rewrite limit_update. eauto.
Qed.

Lemma write_preserves_valid_range:
  forall z h a a' v h',
  valid_range h a z ->
  write h a' v h' ->
  valid_range h' a z.
Proof.
  induction z; simpl; intros; unpack;
  eauto using write_preserves_valid_addr.
Qed.

Lemma write_preserves_valid_range_reverse:
  forall z h a a' v h',
  valid_range h'  a z ->
  write h a' v h' ->
  valid_range h a z.
Proof.
  induction z; simpl; intros; unpack;
  eauto using write_preserves_valid_addr_reverse.
Qed.

Lemma valid_range_implies_write_range:
  forall z h a vs,
  valid_range h a z ->
  length vs = z ->
  exists h', write_range h a z vs h'.
Proof.
  induction z; simpl; intros; unpack; my_list_cleanup.
  (* Base *)
  eauto.
  (* Step *)
  forwards: valid_addr_implies_write. eauto. unpack.
  forwards: IHz. eapply write_preserves_valid_range; eauto. eauto. unpack.
  eauto.
Qed.

Lemma write_range_implies_valid_range:
  forall z h a vs h',
  write_range h a z vs h' ->
  valid_range h a z.
Proof.
  induction z; destruct vs; simpl; intros; try tauto. unpack.
  eauto using write_implies_valid_addr, write_preserves_valid_range_reverse.
Qed.

Lemma write_range_implies_length_equality:
  forall z h a vs h',
  write_range h a z vs h' ->
  z = length vs.
Proof.
  induction z; destruct vs; simpl; intros; try tauto. unpack. eauto with f_equal.
Qed.

(* ---------------------------------------------------------------------------- *)

(* Disjointness is symmetric. *)

Lemma disjoint_intervals_symmetric:
  forall o1 z1 o2 z2,
  disjoint_intervals o1 z1 o2 z2 ->
  disjoint_intervals o2 z2 o1 z1.
Proof.
  unfold disjoint_intervals. intros. omega.
Qed.

Lemma disjoint_ranges_symmetric:
  forall a1 z1 a2 z2,
  disjoint_ranges a1 z1 a2 z2 ->
  disjoint_ranges a2 z2 a1 z1.
Proof.
  unfold disjoint_ranges. da. by_cases;
  eauto using disjoint_intervals_symmetric.
Qed.

