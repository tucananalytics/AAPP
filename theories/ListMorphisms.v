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
    or a position at which the position maps differ, and [find_cex_sound]
    turns any counterexample found into a proof that the equality fails.
    (Presburger arithmetic has the small-model property, so a sufficiently
    large bound always exists; we do not need to compute it.) *)

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

Lemma cex_at_sound : forall l r n c, cex_at l r n = Some c -> ~ pcmEQ 1 l r.
Proof.
  unfold cex_at; intros l r n c H Heq. destruct (Heq (env1 n)) as [Hs Hp].
  destruct (Nat.eqb_spec (pevl (shape l) (env1 n)) (pevl (shape r) (env1 n))); [| contradiction].
  destruct (pos_diff l r (env1 n) (pevl (shape l) (env1 n))) as [i |] eqn:E; [| discriminate].
  destruct (pos_diff_sound _ _ _ _ E) as [Hi Hne]. apply Hne, Hp, Hi.
Qed.

Theorem find_cex_sound : forall l r bound c, find_cex l r bound = Some c -> ~ pcmEQ 1 l r.
Proof.
  induction bound as [| b IH]; intros c H; simpl in H.
  - eapply cex_at_sound; eauto.
  - destruct (find_cex l r b) as [c' |] eqn:E; [eapply IH; eauto | eapply cex_at_sound; eauto].
Qed.

(** [refute n] proves [~ pcmEQ 1 l r] by finding a counterexample among the
    input lengths [0 .. n]. *)
Ltac refute n := eapply find_cex_sound with (bound := n); vm_compute; reflexivity.
