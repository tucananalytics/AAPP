(** * Containers, container morphisms, and agent interfaces

    This file formalises the small amount of container theory used in the
    paper, and the reading of containers as typed agent interfaces
    (Section 3 of the paper):

      - a container [(S <| P)] is a type of shapes with a family of position
        types; read as an interface, [S] is the type of moves an agent may
        emit and [P s] the type of responses it accepts after emitting [s]
        (Niu and Spivak's polynomial  sum_{s:S} y^{P s});
      - a container morphism [(u, f)] is covariant on shapes and
        contravariant on positions -- as an interface map it is an *adapter*
        (a dependent lens): it translates moves forwards and responses
        backwards;
      - an agent with interface [I] and state [X] is a coalgebra
        [X -> Ext I X] (a readout and an update);
      - wrapping an agent by an adapter is post-composition with the
        extension of the adapter, and this is functorial.

    The list container [(n : nat <| Fin n)] is then connected to the
    non-dependent representation of [ListMorphisms]: a Presburger-definable
    morphism that is in range determines a genuine container morphism, and
    its extension agrees with [interp]. *)

From Coq Require Import Arith Lia List PeanoNat.
From AAPP Require Import ListMorphisms.
Import ListNotations.

Set Implicit Arguments.

(** ** Containers and their extensions *)

Record Container := mkCont {
  Shape : Type;
  Pos   : Shape -> Type
}.

(** The extension (semantics) of a container: a shape together with an
    assignment of data to its positions. *)
Definition Ext (C : Container) (X : Type) : Type := { s : Shape C & Pos C s -> X }.

Definition ext_map (C : Container) (X Y : Type) (h : X -> Y) : Ext C X -> Ext C Y :=
  fun e => existT (fun s => Pos C s -> Y) (projT1 e) (fun p => h (projT2 e p)).

(** ** Container morphisms (dependent lenses) *)

Record CMor (C D : Container) := mkMor {
  u : Shape C -> Shape D;                       (** forwards on shapes / moves *)
  f : forall s, Pos D (u s) -> Pos C s          (** backwards on positions / responses *)
}.

Arguments u {C D}.
Arguments f {C D}.

(** The polymorphic function (natural transformation) determined by a
    container morphism -- [mmap] in the paper. *)
Definition mmap (C D : Container) (m : CMor C D) (X : Type) : Ext C X -> Ext D X :=
  fun e => existT (fun s => Pos D s -> X) (u m (projT1 e)) (fun p => projT2 e (f m (projT1 e) p)).

(** Naturality of [mmap] in [X] holds by computation. *)
Lemma mmap_natural : forall C D (m : CMor C D) X Y (h : X -> Y) (e : Ext C X),
    mmap m (ext_map h e) = ext_map h (mmap m e).
Proof. reflexivity. Qed.

Definition cid (C : Container) : CMor C C := mkMor C C (fun s => s) (fun s p => p).

Definition ccomp (A B C : Container) (m2 : CMor B C) (m1 : CMor A B) : CMor A C :=
  mkMor A C (fun s => u m2 (u m1 s)) (fun s p => f m1 s (f m2 (u m1 s) p)).

Lemma mmap_id : forall C X (e : Ext C X), mmap (cid C) e = e.
Proof. intros C X [s g]; reflexivity. Qed.

(** Functoriality: the extension of a composite is the composite of the
    extensions.  This is what makes verification compositional: an equation
    between adapters transfers to every pipeline built from them. *)
Lemma mmap_comp : forall A B C (m2 : CMor B C) (m1 : CMor A B) X (e : Ext A X),
    mmap (ccomp m2 m1) e = mmap m2 (mmap m1 e).
Proof. intros A B C m2 m1 X [s g]; reflexivity. Qed.

(** A cartesian morphism: each [f s] is a bijection. *)
Definition cartesian (C D : Container) (m : CMor C D) : Prop :=
  forall s, exists g : Pos C s -> Pos D (u m s),
      (forall p, g (f m s p) = p) /\ (forall q, f m s (g q) = q).

(** ** Containers as agent interfaces *)

(** An agent with interface [I] and state [X]: from a state, a move together
    with a continuation for every admissible response.  Equivalently a
    coalgebra of the extension functor, or a lens  X y^X -> I. *)
Definition Agent (I : Container) (X : Type) : Type := X -> Ext I X.

Definition readout (I : Container) (X : Type) (a : Agent I X) (x : X) : Shape I :=
  projT1 (a x).

Definition update (I : Container) (X : Type) (a : Agent I X) (x : X)
  : Pos I (readout a x) -> X := projT2 (a x).

(** Wrapping an agent by an adapter [m : I => J] yields an agent with
    interface [J]: the agent's moves are translated forwards and the
    environment's responses backwards. *)
Definition wrap (I J : Container) (X : Type) (m : CMor I J) (a : Agent I X) : Agent J X :=
  fun x => mmap m (a x).

Lemma wrap_id : forall I X (a : Agent I X) x, wrap (cid I) a x = a x.
Proof. intros; apply mmap_id. Qed.

Lemma wrap_comp : forall I J K X (m2 : CMor J K) (m1 : CMor I J) (a : Agent I X) x,
    wrap (ccomp m2 m1) a x = wrap m2 (wrap m1 a) x.
Proof. intros; apply mmap_comp. Qed.

(** Running an agent against an environment strategy for [n] rounds.  An
    environment for interface [I] chooses, for every move, a response. *)
Definition Env (I : Container) : Type := forall s, Pos I s.

Fixpoint run (I : Container) (X : Type) (a : Agent I X) (e : Env I) (x : X) (n : nat)
  : list (Shape I) :=
  match n with
  | 0 => []
  | S n' => readout a x :: run a e (update a x (e (readout a x))) n'
  end.

(** Behavioural consequence of adapter equality: adapters with the same
    extension (for every data type) induce the same wrapped behaviour. *)
Lemma wrap_ext_eq : forall I J X (m m' : CMor I J) (a : Agent I X),
    (forall x, mmap m (a x) = mmap m' (a x)) ->
    forall e x n, run (wrap m a) e x n = run (wrap m' a) e x n.
Proof.
  intros I J X m m' a Hm e x n. revert x.
  induction n as [| n IH]; intros x; simpl; auto.
  unfold readout, update, wrap. rewrite Hm. f_equal. apply IH.
Qed.

(** ** The list container and the link to the arithmetic representation *)

Definition Fin (n : nat) : Type := { i : nat | i < n }.

Definition ListC : Container := mkCont (fun n => Fin n).

(** From a Presburger-definable morphism of arity 1 that is in range, build a
    container morphism [ListC => ListC]. *)
Definition env1 (n : nat) : nat -> nat := fun j => if j =? 0 then n else 0.

Definition to_cmor (m : PPCm) (H : in_range 1 m) : CMor ListC ListC.
Proof.
  refine (mkMor ListC ListC
            (fun n => pevl (shape m) (env1 n))
            (fun n i => exist _ (pevl (pos m) (ext (env1 n) 1 (proj1_sig i))) _)).
  destruct i as [i Hi]; simpl.
  specialize (H (env1 n) i Hi). simpl in H. unfold env1 in H at 2. simpl in H. lia.
Defined.

(** Representations of lists as elements of the extension of [ListC]. *)
Definition rep_to_ext (X : Type) (r : Rep X) : Ext ListC X :=
  existT (fun n => Fin n -> X) (fst r) (fun i : Fin (fst r) => snd r (proj1_sig i)).

Definition ext_to_rep (X : Type) (d : X) (e : Ext ListC X) : Rep X :=
  (projT1 e, fun i => match le_lt_dec (projT1 e) i with
                      | left _ => d
                      | right Hi => projT2 e (exist _ i Hi)
                      end).

(** The extension of [to_cmor m] agrees with the arithmetic interpretation:
    for every element [e] of the extension of the list container, wrapping
    by [to_cmor m] and then reading off the list is the same as reading off
    the list and then applying [interp m]. *)
Theorem to_cmor_interp : forall (m : PPCm) (H : in_range 1 m) X (d : X) (e : Ext ListC X),
    RepEq (ext_to_rep d (mmap (to_cmor H) e)) (interp m [ext_to_rep d e] d).
Proof.
  intros m H X d [n g]. unfold RepEq, ext_to_rep, interp; simpl.
  assert (He : forall j, env [(n, fun i => match le_lt_dec n i with
                                           | left _ => d
                                           | right Hi => g (exist _ i Hi) end)] j = env1 n j).
  { intros j. unfold env, env1; destruct j; simpl; auto. destruct j; auto. }
  assert (Hs : pevl (shape m) (env1 n) = pevl (shape m) (env [(n, fun i => match le_lt_dec n i with
                                           | left _ => d
                                           | right Hi => g (exist _ i Hi) end)])).
  { apply pevl_ext; auto. }
  split; [exact Hs |].
  intros i Hi.
  assert (Hr : pevl (pos m) (ext (env1 n) 1 i) < n).
  { specialize (H (env1 n) i Hi). simpl in H. unfold env1 in H at 2; simpl in H. lia. }
  assert (Hg : forall p p' (H1 : p < n) (H2 : p' < n), p = p' ->
                 g (exist _ p H1) = g (exist _ p' H2)).
  { intros p p' H1 H2 Hpp; subst p'. f_equal. f_equal. apply le_unique. }
  destruct (le_lt_dec (pevl (shape m) (env1 n)) i); [lia |].
  simpl.
  match goal with |- context [Nat.ltb ?a n] =>
    assert (Hp : pevl (pos m) (ext (env1 n) 1 i) = a)
      by (apply pevl_ext; intros j; unfold ext; destruct (j =? 1); auto);
    revert Hp; generalize a
  end.
  intros p' Hp. rewrite <- Hp.
  destruct (Nat.ltb_spec (pevl (pos m) (ext (env1 n) 1 i)) n); [| exfalso; lia].
  destruct (le_lt_dec n (pevl (pos m) (ext (env1 n) 1 i))); [exfalso; lia |].
  apply Hg. reflexivity.
Qed.

(** Hence an arithmetic equality between well-typed morphisms yields equal
    container morphisms in the sense that matters for agents: their
    extensions agree, so any agent wrapped by either behaves identically. *)
Corollary pcmEQ_wrap : forall (l r : PPCm) (Hl : in_range 1 l) (Hr : in_range 1 r),
    pcmEQ 1 l r ->
    forall X (d : X) (a : Agent ListC X) x,
      RepEq (ext_to_rep d (wrap (to_cmor Hl) a x)) (ext_to_rep d (wrap (to_cmor Hr) a x)).
Proof.
  intros l r Hl Hr Heq X d a x. unfold wrap.
  destruct (to_cmor_interp Hl d (a x)) as [H1 H2].
  destruct (to_cmor_interp Hr d (a x)) as [H3 H4].
  destruct (pcmEQ_ok (k := 1) [ext_to_rep d (a x)] d eq_refl Heq) as [H5 H6].
  split; [congruence |].
  intros i Hi. rewrite H2 by auto. rewrite H6 by congruence. rewrite <- H4 by congruence. auto.
Qed.
