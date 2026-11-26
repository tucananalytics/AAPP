(** * Presburger-definable list morphisms

    Part of the development accompanying "Arithmetic Analysis of Polymorphic
    Programs and the Verification of Typed Agent Interfaces" (Section 4).

    A polymorphic function [List X ^ k -> List X] is represented, following the
    container representation theorem, by a pair

      - a shape map    [u : nat^k -> nat]          (output length from input lengths)
      - a position map [f : nat^k * nat -> nat]    (which input position feeds
                                                     output position [i])

    both given as piecewise-linear terms ([Plfun]).  Variable conventions:
    variables [0 .. k-1] denote the input lengths, and in the position map the
    extra variable [k] denotes the output position [i].

    Positions of the [k] inputs are numbered consecutively ("flat" encoding):
    positions [0..n_1-1] belong to the first input, [n_1..n_1+n_2-1] to the
    second, and so on.  This is the encoding used by the interpretation
    [interp] below and corresponds to the isomorphism
    [Fin n_1 + ... + Fin n_k ~ Fin (n_1 + ... + n_k)] of the paper. *)

From Coq Require Import Arith Lia List PeanoNat Compare_dec.
From AAPP Require Export Piecewise.
Import ListNotations.

Set Implicit Arguments.

(** ** Facts about lists

    A few facts about [length] are proved here rather than taken from the
    standard library, whose names for them changed between Coq 8.19 and 8.20;
    this keeps the development independent of the library version. *)

Lemma len_map : forall (A B : Type) (h : A -> B) (l : list A), length (map h l) = length l.
Proof. induction l; simpl; auto. Qed.

Lemma len_seq : forall n s, length (seq s n) = n.
Proof. induction n; intros; simpl; auto. Qed.

Lemma len_app : forall (A : Type) (l l' : list A), length (l ++ l') = length l + length l'.
Proof. induction l; intros; simpl; auto. Qed.

Lemma len_rev : forall (A : Type) (l : list A), length (rev l) = length l.
Proof. induction l; simpl; auto. rewrite len_app, IHl; simpl; lia. Qed.

Lemma len_firstn : forall (A : Type) n (l : list A), length (firstn n l) = Nat.min n (length l).
Proof. induction n; destruct l; simpl; auto. Qed.

Lemma len_skipn : forall (A : Type) n (l : list A), length (skipn n l) = length l - n.
Proof. induction n; destruct l; simpl; auto. Qed.

(** ** Environments *)

Lemma evl_ext : forall e rho rho', (forall j, rho j = rho' j) -> evl e rho = evl e rho'.
Proof. induction e; intros; simpl; auto. Qed.

Lemma pevl_ext : forall p rho rho', (forall j, rho j = rho' j) -> pevl p rho = pevl p rho'.
Proof.
  induction p; intros; simpl; [apply evl_ext; auto |].
  rewrite (IHp1 rho rho'), (IHp2 rho rho'), (IHp3 rho rho'); auto.
Qed.

(** [ext rho k i] binds variable [k] to [i]. *)
Definition ext (rho : nat -> nat) (k i : nat) : nat -> nat :=
  fun j => if Nat.eqb j k then i else rho j.

Lemma ext_eq : forall rho k i, ext rho k i k = i.
Proof. intros; unfold ext; rewrite Nat.eqb_refl; auto. Qed.

Lemma ext_neq : forall rho k i j, j <> k -> ext rho k i j = rho j.
Proof. intros; unfold ext; rewrite (proj2 (Nat.eqb_neq j k) H); auto. Qed.

(** [shield k p] is [p] with every variable [>= k] replaced by [0]; it is used
    in composition so that terms of arity [k] cannot observe the extra
    variables introduced by the composite. *)
Definition shield (k : nat) (p : Plfun) : Plfun :=
  psubst p (fun j => if j <? k then lp (vr j) else kon 0).

Lemma shield_ok : forall k p rho,
    pevl (shield k p) rho = pevl p (fun j => if j <? k then rho j else 0).
Proof.
  intros; unfold shield; rewrite psubst_ok; apply pevl_ext; intros j.
  destruct (j <? k); reflexivity.
Qed.

(** ** Morphisms *)

Definition PPCm : Set := (Plfun * Plfun)%type.
Definition shape (m : PPCm) : Plfun := fst m.
Definition pos   (m : PPCm) : Plfun := snd m.

(** ** Interpretation

    A list is represented, as in the extension of the list container, by its
    length together with a lookup function.  [d] is a default value returned
    for out-of-range positions; a well-typed morphism never produces one
    (Definition [in_range] below). *)

Definition Rep (X : Type) : Type := (nat * (nat -> X))%type.

Definition env (X : Type) (ins : list (Rep X)) : nat -> nat :=
  fun j => nth j (map (@fst nat (nat -> X)) ins) 0.

Lemma env_beyond : forall X (ins : list (Rep X)) j, length ins <= j -> env ins j = 0.
Proof.
  intros; unfold env; apply nth_overflow; rewrite len_map; auto.
Qed.

(** Flat lookup across the concatenation of the inputs. *)
Fixpoint flat (X : Type) (ins : list (Rep X)) (d : X) (j : nat) : X :=
  match ins with
  | [] => d
  | (n, g) :: rest => if j <? n then g j else flat rest d (j - n)
  end.

Definition interp (X : Type) (m : PPCm) (ins : list (Rep X)) (d : X) : Rep X :=
  (pevl (shape m) (env ins),
   fun i => flat ins d (pevl (pos m) (ext (env ins) (length ins) i))).

(** Translating between ordinary lists and representations. *)
Definition of_list (X : Type) (d : X) (l : list X) : Rep X :=
  (length l, fun i => nth i l d).

Definition to_list (X : Type) (r : Rep X) : list X :=
  map (snd r) (seq 0 (fst r)).

Lemma to_list_length : forall X (r : Rep X), length (to_list r) = fst r.
Proof. intros; unfold to_list; rewrite len_map, len_seq; auto. Qed.

Lemma to_list_nth : forall X (r : Rep X) i d, i < fst r -> nth i (to_list r) d = snd r i.
Proof.
  intros X [n g] i d H; unfold to_list; simpl in *.
  rewrite (nth_indep _ d (g 0)) by (rewrite len_map, len_seq; auto).
  rewrite map_nth, seq_nth by auto. reflexivity.
Qed.

Lemma to_of_list : forall X d (l : list X), to_list (of_list d l) = l.
Proof.
  intros. apply nth_ext with (d := d) (d' := d).
  - rewrite to_list_length; auto.
  - intros i Hi. rewrite to_list_length in Hi. rewrite to_list_nth; auto.
Qed.

(** ** Equality

    Two morphisms of arity [k] are equal when their shape maps agree on all
    environments and their position maps agree on all output positions that
    actually exist (i.e. [i < u rho]).  This is the quasi-container equality
    of Section 4.2 of the paper (equation (6.7) of the thesis).  It is a
    universal statement (universal prefix, quantifier-free matrix) of
    Presburger arithmetic, which is the fragment handled by [lia]. *)

Definition pcmEQ (k : nat) (l r : PPCm) : Prop :=
  forall rho,
    pevl (shape l) rho = pevl (shape r) rho /\
    forall i, i < pevl (shape l) rho ->
              pevl (pos l) (ext rho k i) = pevl (pos r) (ext rho k i).

(** Extensional equality of representations: same length, same elements. *)
Definition RepEq (X : Type) (a b : Rep X) : Prop :=
  fst a = fst b /\ forall i, i < fst a -> snd a i = snd b i.

(** Correctness: [pcmEQ] implies equality of the interpreted functions. *)
Theorem pcmEQ_ok : forall X k (l r : PPCm) (ins : list (Rep X)) d,
    length ins = k -> pcmEQ k l r -> RepEq (interp l ins d) (interp r ins d).
Proof.
  intros X k l r ins d Hk H. unfold interp, RepEq; simpl.
  destruct (H (env ins)) as [Hs Hp]. split; auto.
  intros i Hi. rewrite Hk. rewrite Hp; auto.
Qed.

(** ** Well-typedness: positions in range

    The dependent container representation guarantees [f_n i : Fin n]; in the
    non-dependent setting this is a side condition, again a universal
    Presburger statement. *)
Fixpoint sumvars (k : nat) : lfun :=
  match k with
  | 0 => cnst 0
  | S k' => adD (sumvars k') (vr k')
  end.

Definition in_range (k : nat) (m : PPCm) : Prop :=
  forall rho i, i < pevl (shape m) rho ->
                pevl (pos m) (ext rho k i) < evl (sumvars k) rho.

(** ** Lossless (cartesian) morphisms

    An arity-1 morphism is cartesian when every position map [f_n] is a
    bijection [Fin (u n) -> Fin n].  For finite sets this is equivalent to
    [u n = n] together with injectivity -- again a universal statement.  That
    [lossless] (with [in_range]) implies cartesianness of the corresponding
    container morphism is proved in [Containers.lossless_cartesian]. *)
Definition lossless (m : PPCm) : Prop :=
  forall rho,
    pevl (shape m) rho = rho 0 /\
    forall i j, i < rho 0 -> j < rho 0 ->
                pevl (pos m) (ext rho 1 i) = pevl (pos m) (ext rho 1 j) -> i = j.

(** ** Composition *)

(** [comp1 k l r]: post-compose the arity-1 morphism [l] with the arity-[k]
    morphism [r]; the composite has arity [k]. *)
Definition comp1 (k : nat) (l r : PPCm) : PPCm :=
  let ur := shield k (shape r) in
  (psubst (shape l) (fun j => if j =? 0 then ur else kon 0),
   psubst (pos r)
     (fun j => if j =? k
               then psubst (pos l) (fun j' => if j' =? 0 then ur
                                              else if j' =? 1 then lp (vr k)
                                              else kon 0)
               else lp (vr j))).

(** [comp2 k l r1 r2]: post-compose the arity-2 morphism [l] with two
    arity-[k] morphisms applied to the same [k] inputs.  With the flat
    encoding the composite position map is a case split on whether the
    intermediate position falls in the first or the second intermediate list.
    This is what is needed to express [app (take m xs) (drop m xs)] or
    [lastk (lastk xs ++ ys)]. *)
Definition comp2 (k : nat) (l r1 r2 : PPCm) : PPCm :=
  let u1 := shield k (shape r1) in
  let u2 := shield k (shape r2) in
  let sig := fun j => if j =? 0 then u1 else if j =? 1 then u2
                      else if j =? 2 then lp (vr k) else kon 0 in
  let jpos := psubst (pos l) sig in
  (psubst (shape l) sig,
   pf (psub u1 jpos)
      (psubst (pos r1) (fun j => if j =? k then jpos else lp (vr j)))
      (psubst (pos r2) (fun j => if j =? k then psub jpos u1 else lp (vr j)))).

(** The identity morphism (arity 1). *)
Definition idm : PPCm := (lp (vr 0), lp (vr 1)).

Lemma idm_ok : forall X (r : Rep X) d, RepEq (interp idm [r] d) r.
Proof.
  intros X [n g] d; unfold interp, RepEq; simpl; split; auto.
  intros i Hi. unfold ext; simpl. unfold env in Hi; simpl in Hi.
  destruct (Nat.ltb_spec i n); auto; lia.
Qed.

(** *** Correctness of composition *)

(** The environment of a single input of length [n], and of a pair. *)
Definition env1 (n : nat) : nat -> nat := fun j => if j =? 0 then n else 0.

Lemma env_single : forall X (n : nat) (g : nat -> X) j, env [(n, g)] j = env1 n j.
Proof. intros; unfold env, env1; destruct j; simpl; auto. destruct j; auto. Qed.

Lemma env_pair : forall X (n1 n2 : nat) (g1 g2 : nat -> X) j,
    env [(n1, g1); (n2, g2)] j = if j =? 0 then n1 else if j =? 1 then n2 else 0.
Proof. intros; unfold env; destruct j as [|[|j]]; simpl; auto. destruct j; auto. Qed.

Lemma shield_env : forall X (ins : list (Rep X)) p rho,
    (forall j, j < length ins -> rho j = env ins j) ->
    pevl (shield (length ins) p) rho = pevl p (env ins).
Proof.
  intros. rewrite shield_ok. apply pevl_ext. intros j.
  destruct (Nat.ltb_spec j (length ins)); auto.
  rewrite env_beyond; auto.
Qed.

Theorem comp1_ok : forall X k (l r : PPCm) (ins : list (Rep X)) d,
    length ins = k -> in_range 1 l ->
    RepEq (interp (comp1 k l r) ins d) (interp l [interp r ins d] d).
Proof.
  intros X k l r ins d Hk Hl. subst k.
  set (k := length ins).
  set (rho := env ins).
  set (n1 := pevl (shape r) rho).
  set (g1 := fun i => flat ins d (pevl (pos r) (ext rho k i))).
  set (sig := fun j' => if j' =? 0 then shield k (shape r)
                        else if j' =? 1 then lp (vr k) else kon 0).
  assert (Hsig : forall i j, pevl (sig j) (ext rho k i) = ext (env [(n1, g1)]) 1 i j).
  { intros i j. unfold sig, ext at 2. rewrite env_single; unfold env1.
    destruct (Nat.eqb_spec j 0); [subst; simpl; apply shield_env; intros; apply ext_neq; lia |].
    destruct (Nat.eqb_spec j 1); [subst; simpl; apply ext_eq | simpl; auto]. }
  assert (Hsig0 : forall j, pevl (if j =? 0 then shield k (shape r) else kon 0) rho = env [(n1, g1)] j).
  { intros j. rewrite env_single; unfold env1.
    destruct (Nat.eqb_spec j 0); [subst; simpl; apply shield_env; auto | simpl; auto]. }
  unfold interp, comp1, RepEq; simpl. fold k rho n1 g1 sig.
  assert (Hs : pevl (psubst (shape l) (fun j => if j =? 0 then shield k (shape r) else kon 0)) rho
               = pevl (shape l) (env [(n1, g1)])).
  { rewrite psubst_ok. apply pevl_ext; auto. }
  split; [exact Hs |].
  intros i Hi. rewrite Hs in Hi.
  set (p := pevl (pos l) (ext (env [(n1, g1)]) 1 i)).
  assert (Hp : pevl (psubst (pos l) sig) (ext rho k i) = p).
  { rewrite psubst_ok. apply pevl_ext; auto. }
  assert (Hrange : p < n1).
  { specialize (Hl (env [(n1, g1)]) i Hi). simpl in Hl.
    rewrite !env_single in Hl; unfold env1 in Hl. simpl in Hl. unfold p. lia. }
  simpl.
  match goal with
  | |- context [Nat.ltb ?a ?b] =>
      let E := fresh in assert (E : Nat.ltb a b = true) by (apply Nat.ltb_lt; exact Hrange);
      rewrite E; clear E
  end.
  f_equal. rewrite psubst_ok. apply pevl_ext; intros j.
  destruct (Nat.eqb_spec j k).
  + subst j. rewrite ext_eq. exact Hp.
  + simpl. rewrite !ext_neq; auto.
Qed.

Theorem comp2_ok : forall X k (l r1 r2 : PPCm) (ins : list (Rep X)) d,
    length ins = k -> in_range 2 l ->
    RepEq (interp (comp2 k l r1 r2) ins d)
          (interp l [interp r1 ins d; interp r2 ins d] d).
Proof.
  intros X k l r1 r2 ins d Hk Hl. subst k.
  set (k := length ins).
  set (rho := env ins).
  set (n1 := pevl (shape r1) rho).
  set (n2 := pevl (shape r2) rho).
  set (g1 := fun i => flat ins d (pevl (pos r1) (ext rho k i))).
  set (g2 := fun i => flat ins d (pevl (pos r2) (ext rho k i))).
  set (sig := fun j => if j =? 0 then shield k (shape r1) else if j =? 1 then shield k (shape r2)
                       else if j =? 2 then lp (vr k) else kon 0).
  (* evaluating [sig] in [ext rho k i] gives the environment of the intermediate list *)
  assert (Hsig : forall i j, pevl (sig j) (ext rho k i) = ext (env [(n1, g1); (n2, g2)]) 2 i j).
  { intros i j. unfold sig, ext at 2. rewrite env_pair.
    destruct (Nat.eqb_spec j 0); [subst; simpl; apply shield_env; intros; apply ext_neq; lia |].
    destruct (Nat.eqb_spec j 1); [subst; simpl; apply shield_env; intros; apply ext_neq; lia |].
    destruct (Nat.eqb_spec j 2); [subst; simpl; apply ext_eq | simpl; auto]. }
  assert (Hsig0 : forall j, pevl (sig j) rho = env [(n1, g1); (n2, g2)] j).
  { intros j. unfold sig. rewrite env_pair.
    destruct (Nat.eqb_spec j 0); [subst; simpl; apply shield_env; auto |].
    destruct (Nat.eqb_spec j 1); [subst; simpl; apply shield_env; auto |].
    destruct (Nat.eqb_spec j 2); [subst; simpl; apply env_beyond; auto | simpl; auto]. }
  unfold interp, comp2, RepEq; simpl. fold k rho n1 n2 g1 g2 sig.
  assert (Hs : pevl (psubst (shape l) sig) rho = pevl (shape l) (env [(n1, g1); (n2, g2)])).
  { rewrite psubst_ok. apply pevl_ext; auto. }
  split; [exact Hs |].
  intros i Hi. rewrite Hs in Hi.
  set (p := pevl (pos l) (ext (env [(n1, g1); (n2, g2)]) 2 i)).
  assert (Hp : pevl (psubst (pos l) sig) (ext rho k i) = p).
  { rewrite psubst_ok. apply pevl_ext; auto. }
  assert (Hrange : p < n1 + n2).
  { specialize (Hl (env [(n1, g1); (n2, g2)]) i Hi). simpl in Hl.
    rewrite !env_pair in Hl. simpl in Hl. unfold p. lia. }
  simpl.
  assert (Hc : pevl (psub (shield k (shape r1)) (psubst (pos l) sig)) (ext rho k i) = n1 - p).
  { rewrite psub_ok, Hp. f_equal. apply shield_env; intros; apply ext_neq; lia. }
  rewrite Hc.
  destruct (le_lt_dec (n1 - p) 0) as [Hge | Hlt].
  - (* p >= n1 : the position lies in the second intermediate list *)
    match goal with |- context [Nat.ltb ?a n1] =>
      replace (Nat.ltb a n1) with false by (symmetry; apply Nat.ltb_ge; change (n1 <= p); lia) end.
    match goal with |- context [Nat.ltb ?a n2] =>
      replace (Nat.ltb a n2) with true by (symmetry; apply Nat.ltb_lt; change (p - n1 < n2); lia) end.
    f_equal. rewrite psubst_ok. apply pevl_ext; intros j.
    destruct (Nat.eqb_spec j k).
    + subst j. rewrite ext_eq. rewrite psub_ok, Hp. f_equal. apply shield_env; intros; apply ext_neq; lia.
    + simpl. rewrite !ext_neq; auto.
  - (* p < n1 : the position lies in the first intermediate list *)
    match goal with |- context [Nat.ltb ?a n1] =>
      replace (Nat.ltb a n1) with true by (symmetry; apply Nat.ltb_lt; change (p < n1); lia) end.
    f_equal. rewrite psubst_ok. apply pevl_ext; intros j.
    destruct (Nat.eqb_spec j k).
    + subst j. rewrite ext_eq. exact Hp.
    + simpl. rewrite !ext_neq; auto.
Qed.

(** *** Evaluating composites

    An environment that arises from [k] inputs is zero beyond [k].  On such
    environments a composite evaluates as composition of container morphisms
    does: shapes compose forwards and positions backwards.  The four lemmas
    below are what links [comp1] and [comp2] to composition and pairing of
    container morphisms in [Containers]. *)

Definition env2 (n1 n2 : nat) : nat -> nat :=
  fun j => if j =? 0 then n1 else if j =? 1 then n2 else 0.

Definition vanishes (k : nat) (rho : nat -> nat) : Prop := forall j, k <= j -> rho j = 0.

Lemma vanishes_env1 : forall n, vanishes 1 (env1 n).
Proof. intros n [| j] H; [lia | reflexivity]. Qed.

Lemma vanishes_env2 : forall n1 n2, vanishes 2 (env2 n1 n2).
Proof. intros n1 n2 [| [| j]] H; [lia | lia | reflexivity]. Qed.

Lemma shield_vanish : forall k p rho, vanishes k rho -> pevl (shield k p) rho = pevl p rho.
Proof.
  intros k p rho Hv. rewrite shield_ok. apply pevl_ext; intros j.
  destruct (Nat.ltb_spec j k); [reflexivity | symmetry; apply Hv; assumption].
Qed.

Lemma shield_vanish_ext : forall k p rho i,
    vanishes k rho -> pevl (shield k p) (ext rho k i) = pevl p rho.
Proof.
  intros k p rho i Hv. rewrite shield_ok. apply pevl_ext; intros j.
  destruct (Nat.ltb_spec j k); [apply ext_neq; lia | symmetry; apply Hv; assumption].
Qed.

Lemma comp1_shape_gen : forall k (l r : PPCm) rho,
    vanishes k rho ->
    pevl (shape (comp1 k l r)) rho = pevl (shape l) (env1 (pevl (shape r) rho)).
Proof.
  intros k l r rho Hv. unfold comp1, shape; cbn [fst]. rewrite psubst_ok.
  apply pevl_ext; intros [| j]; [| reflexivity].
  cbn [Nat.eqb]. unfold env1; cbn [Nat.eqb]. apply shield_vanish; exact Hv.
Qed.

Lemma comp1_pos_gen : forall k (l r : PPCm) rho i,
    vanishes k rho ->
    pevl (pos (comp1 k l r)) (ext rho k i)
    = pevl (pos r) (ext rho k (pevl (pos l) (ext (env1 (pevl (shape r) rho)) 1 i))).
Proof.
  intros k l r rho i Hv. unfold comp1, pos, shape; cbn [fst snd]. rewrite psubst_ok.
  apply pevl_ext; intros j.
  destruct (Nat.eqb_spec j k) as [-> | Hj].
  - rewrite ext_eq, psubst_ok. apply pevl_ext; intros [| [| j']]; cbn [Nat.eqb].
    + unfold ext, env1; cbn [Nat.eqb]. apply (shield_vanish_ext (fst r) i Hv).
    + cbn [pevl evl]. rewrite ext_eq. reflexivity.
    + reflexivity.
  - cbn [pevl evl]. rewrite !ext_neq by assumption. reflexivity.
Qed.

Lemma comp2_shape_gen : forall k (l r1 r2 : PPCm) rho,
    vanishes k rho ->
    pevl (shape (comp2 k l r1 r2)) rho
    = pevl (shape l) (env2 (pevl (shape r1) rho) (pevl (shape r2) rho)).
Proof.
  intros k l r1 r2 rho Hv. unfold comp2, shape; cbn [fst]. rewrite psubst_ok.
  apply pevl_ext; intros [| [| [| j]]]; unfold env2; cbn [Nat.eqb].
  - apply shield_vanish; exact Hv.
  - apply shield_vanish; exact Hv.
  - cbn [pevl evl]. apply Hv; lia.
  - reflexivity.
Qed.

Lemma comp2_pos_gen : forall k (l r1 r2 : PPCm) rho i,
    vanishes k rho ->
    pevl (pos (comp2 k l r1 r2)) (ext rho k i)
    = if pevl (pos l) (ext (env2 (pevl (shape r1) rho) (pevl (shape r2) rho)) 2 i)
         <? pevl (shape r1) rho
      then pevl (pos r1)
                (ext rho k (pevl (pos l) (ext (env2 (pevl (shape r1) rho) (pevl (shape r2) rho)) 2 i)))
      else pevl (pos r2)
                (ext rho k (pevl (pos l) (ext (env2 (pevl (shape r1) rho) (pevl (shape r2) rho)) 2 i)
                            - pevl (shape r1) rho)).
Proof.
  intros k l r1 r2 rho i Hv. unfold comp2, pos, shape; cbn [fst snd].
  set (a := pevl (fst r1) rho). set (b := pevl (fst r2) rho).
  set (q := pevl (snd l) (ext (env2 a b) 2 i)).
  set (sig := fun j => if j =? 0 then shield k (fst r1) else if j =? 1 then shield k (fst r2)
                       else if j =? 2 then lp (vr k) else kon 0).
  assert (Hq : pevl (psubst (snd l) sig) (ext rho k i) = q).
  { rewrite psubst_ok. apply pevl_ext; intros [| [| [| j]]]; unfold sig, ext at 2, env2; cbn [Nat.eqb].
    - apply shield_vanish_ext; exact Hv.
    - apply shield_vanish_ext; exact Hv.
    - cbn [pevl evl]. apply ext_eq.
    - reflexivity. }
  assert (Ha : pevl (shield k (fst r1)) (ext rho k i) = a) by (apply shield_vanish_ext; exact Hv).
  cbn [pevl]. rewrite psub_ok, Ha, Hq.
  destruct (le_lt_dec (a - q) 0) as [Hle | Hlt]; destruct (Nat.ltb_spec q a) as [Hqa | Hqa];
    try (exfalso; lia).
  - rewrite psubst_ok. apply pevl_ext; intros j.
    destruct (Nat.eqb_spec j k) as [-> | Hj].
    + rewrite ext_eq, psub_ok, Hq, Ha. reflexivity.
    + cbn [pevl evl]. rewrite !ext_neq by assumption. reflexivity.
  - rewrite psubst_ok. apply pevl_ext; intros j.
    destruct (Nat.eqb_spec j k) as [-> | Hj].
    + rewrite ext_eq. exact Hq.
    + cbn [pevl evl]. rewrite !ext_neq by assumption. reflexivity.
Qed.

(** *** Closed terms

    A term is closed at [k] when it mentions no variable [>= k].  The value of
    a closed term depends only on the first [k] variables, so for closed
    morphisms it is enough to check [pcmEQ] on the environments that arise
    from [k] inputs. *)

Fixpoint lclosed (k : nat) (e : lfun) : bool :=
  match e with
  | cnst _ => true
  | vr j => j <? k
  | adD a b => lclosed k a && lclosed k b
  | suB a b => lclosed k a && lclosed k b
  end.

Fixpoint pclosed (k : nat) (p : Plfun) : bool :=
  match p with
  | lp a => lclosed k a
  | pf c l r => pclosed k c && pclosed k l && pclosed k r
  end.

(** A morphism of arity [k]: the shape map reads the [k] lengths, the
    position map in addition the output position (variable [k]). *)
Definition closed (k : nat) (m : PPCm) : bool :=
  pclosed k (shape m) && pclosed (S k) (pos m).

Lemma lclosed_ok : forall k e rho rho',
    lclosed k e = true -> (forall j, j < k -> rho j = rho' j) -> evl e rho = evl e rho'.
Proof.
  induction e; intros rho rho' Hc H; simpl in *.
  - reflexivity.
  - apply H. apply Nat.ltb_lt; exact Hc.
  - apply andb_prop in Hc. destruct Hc as [H1 H2]. rewrite (IHe1 rho rho'), (IHe2 rho rho'); auto.
  - apply andb_prop in Hc. destruct Hc as [H1 H2]. rewrite (IHe1 rho rho'), (IHe2 rho rho'); auto.
Qed.

Lemma pclosed_ok : forall k p rho rho',
    pclosed k p = true -> (forall j, j < k -> rho j = rho' j) -> pevl p rho = pevl p rho'.
Proof.
  induction p; intros rho rho' Hc H; simpl in *.
  - eapply lclosed_ok; eauto.
  - apply andb_prop in Hc. destruct Hc as [Hc H3]. apply andb_prop in Hc. destruct Hc as [H1 H2].
    rewrite (IHp1 rho rho'), (IHp2 rho rho'), (IHp3 rho rho'); auto.
Qed.

(** [pcmEQ] restricted to the environments of [k] inputs. *)
Definition pcmEQ_on (k : nat) (l r : PPCm) : Prop :=
  forall rho, vanishes k rho ->
    pevl (shape l) rho = pevl (shape r) rho /\
    forall i, i < pevl (shape l) rho ->
              pevl (pos l) (ext rho k i) = pevl (pos r) (ext rho k i).

Lemma pcmEQ_pcmEQ_on : forall k l r, pcmEQ k l r -> pcmEQ_on k l r.
Proof. intros k l r H rho _. apply H. Qed.

(** For closed morphisms the restriction loses nothing. *)
Theorem pcmEQ_on_pcmEQ : forall k l r,
    closed k l = true -> closed k r = true -> pcmEQ_on k l r -> pcmEQ k l r.
Proof.
  intros k l r Hl Hr H rho.
  apply andb_prop in Hl. destruct Hl as [Hls Hlp].
  apply andb_prop in Hr. destruct Hr as [Hrs Hrp].
  set (rho' := fun j => if j <? k then rho j else 0).
  assert (Hv : vanishes k rho').
  { intros j Hj. unfold rho'. destruct (Nat.ltb_spec j k); [lia | reflexivity]. }
  assert (Hag : forall j, j < k -> rho j = rho' j).
  { intros j Hj. unfold rho'. destruct (Nat.ltb_spec j k); [reflexivity | lia]. }
  assert (Hag' : forall i j, j < S k -> ext rho k i j = ext rho' k i j).
  { intros i j Hj. unfold ext. destruct (Nat.eqb_spec j k); [reflexivity | apply Hag; lia]. }
  destruct (H rho' Hv) as [Hs Hp].
  rewrite (pclosed_ok _ rho rho' Hls Hag), (pclosed_ok _ rho rho' Hrs Hag).
  split; [exact Hs |].
  intros i Hi.
  rewrite (pclosed_ok _ _ _ Hlp (Hag' i)), (pclosed_ok _ _ _ Hrp (Hag' i)). apply Hp. exact Hi.
Qed.

(** *** Composition at a single input

    For arity-1 morphisms evaluated at an input of length [n], the composite
    behaves as composition of container morphisms does: shapes compose
    forwards and positions backwards.  These two equations are what links
    [comp1] to composition of container morphisms in [Containers]. *)

Lemma comp1_shape1 : forall (l r : PPCm) n,
    pevl (shape (comp1 1 l r)) (env1 n)
    = pevl (shape l) (env1 (pevl (shape r) (env1 n))).
Proof.
  intros l r n. unfold comp1, shape; cbn [fst]. rewrite psubst_ok.
  apply pevl_ext; intros j. unfold env1 at 2.
  destruct (j =? 0); [| reflexivity].
  rewrite shield_ok. apply pevl_ext; intros [| j']; reflexivity.
Qed.

Lemma comp1_pos1 : forall (l r : PPCm) n i,
    pevl (pos (comp1 1 l r)) (ext (env1 n) 1 i)
    = pevl (pos r)
           (ext (env1 n) 1 (pevl (pos l) (ext (env1 (pevl (shape r) (env1 n))) 1 i))).
Proof.
  intros l r n i. unfold comp1, pos; cbn [snd]. rewrite psubst_ok.
  apply pevl_ext; intros j. unfold ext at 3.
  destruct (Nat.eqb_spec j 1) as [-> | Hj].
  - rewrite psubst_ok. apply pevl_ext; intros [| [| j']].
    + cbn [Nat.eqb]. rewrite shield_ok. apply pevl_ext; intros [| [| j'']]; reflexivity.
    + reflexivity.
    + reflexivity.
  - cbn [pevl evl]. unfold ext. rewrite (proj2 (Nat.eqb_neq j 1) Hj). reflexivity.
Qed.

(** ** The decision tactic

    [containers] unfolds the equality into its arithmetic content, eliminates
    the conditionals of the piecewise terms by case analysis, and hands the
    resulting linear-arithmetic goals to [lia].  Soundness is guaranteed by
    the kernel; the case analysis is exhaustive, so completeness of the tactic
    on [pcmEQ], [in_range] and [lossless] goals rests on that of [lia] for
    linear integer arithmetic. *)

Create HintDb morphisms.
#[export] Hint Unfold comp1 comp2 idm : morphisms.

Ltac simp_morph :=
  cbn [fst snd pevl evl Nat.eqb Nat.ltb Nat.leb sumvars] in *;
  repeat match goal with
    | [ |- context [pevl (psubst _ _) _] ] => rewrite psubst_ok
    | [ H : context [pevl (psubst _ _) _] |- _ ] => rewrite psubst_ok in H
    | [ |- context [pevl (shield _ _) _] ] => rewrite shield_ok
    | [ H : context [pevl (shield _ _) _] |- _ ] => rewrite shield_ok in H
    | [ |- context [pevl (padd _ _) _] ] => rewrite padd_ok
    | [ H : context [pevl (padd _ _) _] |- _ ] => rewrite padd_ok in H
    | [ |- context [pevl (psub _ _) _] ] => rewrite psub_ok
    | [ H : context [pevl (psub _ _) _] |- _ ] => rewrite psub_ok in H
    end;
  cbn [fst snd pevl evl Nat.eqb Nat.ltb Nat.leb sumvars] in *.

Ltac unfold_morphism :=
  autounfold with morphisms in *;
  unfold pcmEQ, in_range, lossless, shape, pos, ext, kon, lt_, x0, x1, x2 in *;
  intros; repeat split; intros; repeat simp_morph.

Ltac containers := unfold_morphism; arith.

(** ** Refutation by bounded search

    [lia] proves valid statements; it does not produce counterexamples to
    invalid ones.  For arity-1 morphisms the function [find_cex] searches the
    input lengths [0 .. bound] for a length at which the shape maps differ,
    or a position at which the position maps differ.  The search is exact:
    it returns nothing precisely when the two morphisms agree at every input
    length up to the bound ([find_cex_spec]), so a counterexample that is
    found is a proof that the equality fails ([find_cex_sound]), and a
    counterexample that exists is found once the bound reaches it. *)

(** Agreement of two arity-1 morphisms on inputs of length [n]. *)
Definition agree_at (l r : PPCm) (n : nat) : Prop :=
  pevl (shape l) (env1 n) = pevl (shape r) (env1 n) /\
  forall i, i < pevl (shape l) (env1 n) ->
            pevl (pos l) (ext (env1 n) 1 i) = pevl (pos r) (ext (env1 n) 1 i).

Lemma pcmEQ_agree_at : forall l r, pcmEQ 1 l r -> forall n, agree_at l r n.
Proof. intros l r H n. exact (H (env1 n)). Qed.

Inductive cex : Set :=
| ShapeCex : nat -> cex            (** the shapes differ at input length [n] *)
| PosCex   : nat -> nat -> cex.    (** the positions differ at length [n], position [i] *)

(** The least position [i < b] at which the position maps differ, if any. *)
Fixpoint pos_diff (l r : PPCm) (rho : nat -> nat) (b : nat) : option nat :=
  match b with
  | 0 => None
  | S b' =>
      match pos_diff l r rho b' with
      | Some i => Some i
      | None => if pevl (pos l) (ext rho 1 b') =? pevl (pos r) (ext rho 1 b')
                then None else Some b'
      end
  end.

Definition cex_at (l r : PPCm) (n : nat) : option cex :=
  if pevl (shape l) (env1 n) =? pevl (shape r) (env1 n)
  then match pos_diff l r (env1 n) (pevl (shape l) (env1 n)) with
       | Some i => Some (PosCex n i)
       | None => None
       end
  else Some (ShapeCex n).

Fixpoint find_cex (l r : PPCm) (bound : nat) : option cex :=
  match bound with
  | 0 => cex_at l r 0
  | S b => match find_cex l r b with
           | Some c => Some c
           | None => cex_at l r (S b)
           end
  end.

Lemma pos_diff_sound : forall l r rho b i,
    pos_diff l r rho b = Some i ->
    i < b /\ pevl (pos l) (ext rho 1 i) <> pevl (pos r) (ext rho 1 i).
Proof.
  induction b as [| b IH]; intros i H; simpl in H; [discriminate |].
  destruct (pos_diff l r rho b) as [j |] eqn:E.
  - inversion H; subst. destruct (IH i eq_refl); split; auto.
  - destruct (Nat.eqb_spec (pevl (pos l) (ext rho 1 b)) (pevl (pos r) (ext rho 1 b)));
      [discriminate | inversion H; subst; split; auto].
Qed.

Lemma pos_diff_none : forall l r rho b,
    pos_diff l r rho b = None ->
    forall i, i < b -> pevl (pos l) (ext rho 1 i) = pevl (pos r) (ext rho 1 i).
Proof.
  induction b as [| b IH]; intros H i Hi; simpl in H; [lia |].
  destruct (pos_diff l r rho b) as [j |] eqn:E; [discriminate |].
  destruct (Nat.eqb_spec (pevl (pos l) (ext rho 1 b)) (pevl (pos r) (ext rho 1 b))) as [Eb | Eb];
    [| discriminate].
  destruct (Nat.eq_dec i b) as [-> | Hne]; [exact Eb | apply IH; [reflexivity | lia]].
Qed.

Lemma cex_at_spec : forall l r n, cex_at l r n = None <-> agree_at l r n.
Proof.
  intros l r n. unfold cex_at, agree_at.
  destruct (Nat.eqb_spec (pevl (shape l) (env1 n)) (pevl (shape r) (env1 n))) as [Es | Es].
  - destruct (pos_diff l r (env1 n) (pevl (shape l) (env1 n))) as [i |] eqn:E.
    + split; [discriminate |]. intros [_ Hp].
      destruct (pos_diff_sound _ _ _ _ E) as [Hi Hne]. exfalso. apply Hne, Hp, Hi.
    + split; [| reflexivity]. intros _. split; [exact Es | apply pos_diff_none; exact E].
  - split; [discriminate | intros [Hs _]; contradiction].
Qed.

Theorem find_cex_spec : forall l r b,
    find_cex l r b = None <-> forall n, n <= b -> agree_at l r n.
Proof.
  intros l r. induction b as [| b IH]; simpl.
  - rewrite cex_at_spec. split.
    + intros H n Hn. replace n with 0 by lia. exact H.
    + intros H. apply H. lia.
  - destruct (find_cex l r b) as [c |] eqn:E.
    + split; [discriminate |]. intros H.
      exfalso. assert (Hb : Some c = None) by (apply IH; intros n Hn; apply H; lia). discriminate.
    + rewrite cex_at_spec. split.
      * intros H n Hn. destruct (Nat.eq_dec n (S b)) as [-> | Hne]; [exact H |].
        apply (proj1 IH eq_refl). lia.
      * intros H. apply H. lia.
Qed.

Lemma cex_at_sound : forall l r n c, cex_at l r n = Some c -> ~ pcmEQ 1 l r.
Proof.
  intros l r n c H Heq.
  assert (Hn : cex_at l r n = None) by (apply cex_at_spec, pcmEQ_agree_at, Heq).
  congruence.
Qed.

Theorem find_cex_sound : forall l r bound c, find_cex l r bound = Some c -> ~ pcmEQ 1 l r.
Proof.
  intros l r b c H Heq.
  assert (Hn : find_cex l r b = None)
    by (apply find_cex_spec; intros n _; apply pcmEQ_agree_at, Heq).
  congruence.
Qed.

(** [refute n] proves [~ pcmEQ 1 l r] by finding a counterexample among the
    input lengths [0 .. n]. *)
Ltac refute n := eapply find_cex_sound with (bound := n); vm_compute; reflexivity.
