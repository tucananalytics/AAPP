(** * Containers, container morphisms, and agent interfaces

    Part of the development accompanying "Arithmetic Analysis of Polymorphic
    Programs and the Verification of Typed Agent Interfaces" (Sections 2, 3
    and 5.1-5.2).

    This file formalises the small amount of container theory used in the
    paper, and the reading of containers as typed agent interfaces:

      - a container [(S <| P)] is a type of shapes with a family of position
        types; read as an interface, [S] is the type of moves an agent may
        emit and [P s] the type of responses it accepts after emitting [s]
        (Niu and Spivak's polynomial  sum_{s:S} y^{P s});
      - a container morphism [(u, f)] is covariant on shapes and
        contravariant on positions -- as an interface map it is an *adapter*
        (a dependent lens): it translates moves forwards and responses
        backwards;
      - containers compose, and a morphism lifts along composition
        ([whisker]), which is how an adapter on bare lists acts on lists of
        typed items;
      - an agent with interface [I] and state [X] is a coalgebra
        [X -> Ext I X] (a readout and an update), an environment answers
        moves, and a run is the sequence of moves of an agent against an
        environment;
      - wrapping an agent by an adapter is post-composition with the
        extension of the adapter, and this is functorial.

    The list container [(n : nat <| Fin n)] is then connected to the
    non-dependent representation of [ListMorphisms], for morphisms out of
    one list and out of two.  A Presburger-definable morphism that is in
    range determines a genuine container morphism ([to_cmor], [to_cmor2]);
    its extension agrees with [interp]; composites of representations
    represent composites and pairings of container morphisms; arithmetic
    equality implies equality of container morphisms ([represents_cmorEq]),
    and conversely for closed terms ([pcmEQ_iff_cmorEq]); equal morphisms
    give every wrapped agent the same runs ([cmorEq_run]), and conversely
    ([runs_cmorEq]); and the arithmetic losslessness condition implies
    cartesianness ([lossless_cartesian]).  The last section treats binary
    trees and the flattening morphism. *)

From Coq Require Import Arith Lia List PeanoNat Compare_dec Peano_dec FinFun.
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

(** ** Container morphisms (dependent lenses)

    The projections are named [u] and [f] to match the notation [(u, f)] of
    the paper. *)

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

Lemma cartesian_id : forall C, cartesian (cid C).
Proof. intros C s; exists (fun p => p); split; reflexivity. Qed.

(** Cartesian morphisms compose: a pipeline of lossless adapters is lossless. *)
Lemma cartesian_comp : forall A B C (m2 : CMor B C) (m1 : CMor A B),
    cartesian m1 -> cartesian m2 -> cartesian (ccomp m2 m1).
Proof.
  intros A B C m2 m1 H1 H2 s.
  destruct (H1 s) as [g1 [H1a H1b]]. destruct (H2 (u m1 s)) as [g2 [H2a H2b]].
  exists (fun q => g2 (g1 q)); simpl; split.
  - intros p. rewrite H1a. apply H2a.
  - intros q. rewrite H2b. apply H1b.
Qed.

(** ** Composition of containers and lifting of morphisms

    The composite [cComp C D] has as shapes the [C]-structures of [D]-shapes
    and as positions a [C]-position together with a [D]-position at the shape
    found there.  Read as interfaces: emit a [C]-move whose slots carry
    [D]-moves; a response picks a slot and answers the move in it.  With
    [C := ListC] (below) this is the interface of batches of [D]-items.

    A morphism [m : C => C'] lifts to [whisker m D : cComp C D => cComp C' D],
    which rearranges the slots as [m] does and leaves their contents alone
    ("applying a container morphism", Definition 3.8 of the thesis). *)

Definition cComp (C D : Container) : Container :=
  mkCont (fun e : Ext C (Shape D) => { p : Pos C (projT1 e) & Pos D (projT2 e p) }).

Definition whisker (C C' : Container) (m : CMor C C') (D : Container)
  : CMor (cComp C D) (cComp C' D) :=
  mkMor (cComp C D) (cComp C' D)
        (fun e => mmap m e)
        (fun e q => existT (fun p => Pos D (projT2 e p))
                           (f m (projT1 e) (projT1 q)) (projT2 q)).

(** Lifting is functorial (the equation holds by computation). *)
Lemma whisker_comp : forall C C' C'' (m2 : CMor C' C'') (m1 : CMor C C') D,
    whisker (ccomp m2 m1) D = ccomp (whisker m2 D) (whisker m1 D).
Proof. reflexivity. Qed.

(** The extension of a composite is the composite of the extensions, in one
    direction of the isomorphism  Ext (cComp C D) X ~ Ext C (Ext D X). *)
Definition assoc (C D : Container) (X : Type) (e : Ext (cComp C D) X) : Ext C (Ext D X) :=
  existT (fun s => Pos C s -> Ext D X)
         (projT1 (projT1 e))
         (fun p => existT (fun t => Pos D t -> X)
                          (projT2 (projT1 e) p)
                          (fun q => projT2 e (existT (fun p => Pos D (projT2 (projT1 e) p)) p q))).

(** Under that isomorphism the lifted morphism is the original morphism at
    the data type [Ext D X]: lifting changes the items a morphism acts on,
    not what it does to them.  Consequently every equation between the
    polymorphic functions denoted by two morphisms holds of their liftings. *)
Lemma whisker_assoc : forall C C' (m : CMor C C') D X (e : Ext (cComp C D) X),
    assoc (mmap (whisker m D) e) = mmap m (assoc e).
Proof. reflexivity. Qed.

Lemma whisker_ext_eq : forall C C' (m m' : CMor C C') D,
    (forall Y (e : Ext C Y), mmap m e = mmap m' e) ->
    forall X (e : Ext (cComp C D) X),
      assoc (mmap (whisker m D) e) = assoc (mmap (whisker m' D) e).
Proof. intros C C' m m' D H X e. rewrite !whisker_assoc. apply H. Qed.

(** *** Structures of items answered all at once

    In [cComp C D] a response answers one item.  The interface in which a
    response answers *every* item has the same shapes and, as positions, a
    [D]-response for each [C]-position.  A morphism [m : C => C'] lifts to it
    only when no position is dropped: what is needed is a section [g] of the
    position maps of [m], which sends each position of the source to a
    position of the target that is fetched from it. *)
Definition cAll (C D : Container) : Container :=
  mkCont (fun e : Ext C (Shape D) => forall p : Pos C (projT1 e), Pos D (projT2 e p)).

Definition lift_all (C C' : Container) (m : CMor C C')
           (g : forall s, Pos C s -> Pos C' (u m s))
           (Hg : forall s p, f m s (g s p) = p) (D : Container)
  : CMor (cAll C D) (cAll C' D) :=
  mkMor (cAll C D) (cAll C' D)
        (fun e => mmap m e)
        (fun e rho p =>
           eq_rect (f m (projT1 e) (g (projT1 e) p))
                   (fun p0 => Pos D (projT2 e p0))
                   (rho (g (projT1 e) p)) p (Hg (projT1 e) p)).

(** ** Products and pairing

    The product of two containers has a pair of shapes and, as positions,
    the positions of either component; its extension is the product of the
    two extensions, so a value is a pair of structures.  Read as interfaces:
    emit a move of each, and accept a response to one of the two.  Pairing
    two morphisms out of the same container gives a morphism into the
    product; it is how a function of one argument that uses its argument
    twice ([take m b ++ drop m b]) is expressed. *)

Definition cProd (C D : Container) : Container :=
  mkCont (fun s : Shape C * Shape D => (Pos C (fst s) + Pos D (snd s))%type).

Definition cfst (C D : Container) : CMor (cProd C D) C :=
  mkMor (cProd C D) C (fun s => fst s) (fun s p => inl p).

Definition csnd (C D : Container) : CMor (cProd C D) D :=
  mkMor (cProd C D) D (fun s => snd s) (fun s p => inr p).

Definition cpair (C D1 D2 : Container) (m1 : CMor C D1) (m2 : CMor C D2)
  : CMor C (cProd D1 D2) :=
  mkMor C (cProd D1 D2)
        (fun s => (u m1 s, u m2 s))
        (fun s p => match p with
                    | inl p1 => f m1 s p1
                    | inr p2 => f m2 s p2
                    end).

Lemma cfst_cpair : forall C D1 D2 (m1 : CMor C D1) (m2 : CMor C D2),
    ccomp (cfst D1 D2) (cpair m1 m2) = m1.
Proof. intros C D1 D2 [u1 f1] m2. reflexivity. Qed.

Lemma csnd_cpair : forall C D1 D2 (m1 : CMor C D1) (m2 : CMor C D2),
    ccomp (csnd D1 D2) (cpair m1 m2) = m2.
Proof. intros C D1 D2 m1 [u2 f2]. reflexivity. Qed.

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

(** Running an agent against an environment for at most [n] rounds.  An
    environment for interface [I] has a state of its own (a memory of the
    interaction so far, say); in each state it chooses, for every move, a
    response and a next state, or declines.  It must decline when the move
    admits no response (for example the empty batch of the list interface),
    and the run then ends.  The observable behaviour is the sequence of
    moves. *)
Definition Env (I : Container) (E : Type) : Type :=
  E -> forall s, option (Pos I s * E).

Fixpoint run (I : Container) (X E : Type) (a : Agent I X) (e : Env I E)
         (x : X) (w : E) (n : nat) : list (Shape I) :=
  match n with
  | 0 => []
  | S n' =>
      readout a x ::
        match e w (readout a x) with
        | Some (p, w') => run a e (update a x p) w' n'
        | None => []
        end
  end.

(** Agents that agree at every state have the same runs ... *)
Lemma run_ext : forall I X E (a b : Agent I X),
    (forall x, a x = b x) -> forall (e : Env I E) x w n, run a e x w n = run b e x w n.
Proof.
  intros I X E a b H e x w n. revert x w.
  induction n as [| n IH]; intros x w; simpl; auto.
  unfold readout, update. rewrite (H x). f_equal.
  destruct (e w (projT1 (b x))) as [[p w'] |]; auto.
Qed.

(** ... so adapters with the same extension on the one-step behaviour of an
    agent induce the same wrapped behaviour. *)
Lemma wrap_ext_eq : forall I J X E (m m' : CMor I J) (a : Agent I X),
    (forall x, mmap m (a x) = mmap m' (a x)) ->
    forall (e : Env J E) x w n, run (wrap m a) e x w n = run (wrap m' a) e x w n.
Proof. intros I J X E m m' a Hm. apply run_ext. exact Hm. Qed.

(** The first one and two moves of a run. *)
Lemma run_one : forall I X E (a : Agent I X) (e : Env I E) x w,
    run a e x w 1 = [readout a x].
Proof. intros. cbn [run]. destruct (e w (readout a x)) as [[p w'] |]; reflexivity. Qed.

Lemma run_two : forall I X E (a : Agent I X) (e : Env I E) x w,
    run a e x w 2 = readout a x :: match e w (readout a x) with
                                    | Some (p, _) => [readout a (update a x p)]
                                    | None => []
                                    end.
Proof.
  intros.
  change (run a e x w 2)
    with (readout a x :: match e w (readout a x) with
                         | Some (p, w') => run a e (update a x p) w' 1
                         | None => []
                         end).
  destruct (e w (readout a x)) as [[p w'] |]; [rewrite run_one |]; reflexivity.
Qed.

(** An adapter also transports environments, in the opposite direction: an
    environment that serves interface [J] serves interface [I] through the
    adapter.  Wrapping the agent and adapting the environment are two
    descriptions of the same interaction; the observed moves differ only by
    the translation [u]. *)
Definition pull (I J : Container) (E : Type) (m : CMor I J) (e : Env J E) : Env I E :=
  fun w s => match e w (u m s) with
             | Some (p, w') => Some (f m s p, w')
             | None => None
             end.

Lemma run_wrap_pull : forall I J X E (m : CMor I J) (a : Agent I X) (e : Env J E) x w n,
    run (wrap m a) e x w n = map (u m) (run a (pull m e) x w n).
Proof.
  intros I J X E m a e x w n. revert x w.
  induction n as [| n IH]; intros x w; [reflexivity |].
  cbn [run map]. unfold readout, update, wrap, pull.
  destruct (a x) as [s g]. cbn [mmap projT1 projT2].
  destruct (e w (u m s)) as [[p w'] |]; cbn [map]; [rewrite IH |]; reflexivity.
Qed.

(** ** The list container and the link to the arithmetic representation *)

Definition Fin (n : nat) : Type := { i : nat | i < n }.

Lemma Fin_eq : forall n (a b : Fin n), proj1_sig a = proj1_sig b -> a = b.
Proof.
  intros n [i Hi] [j Hj] H; simpl in H; subst j. f_equal. apply le_unique.
Qed.

Definition ListC : Container := mkCont (fun n => Fin n).

(** ** Equality of morphisms into the list container

    Two container morphisms are equal when their shape maps agree and their
    position maps agree up to the resulting identification of position sets
    (Definition 2.10 of the paper, where this is expressed with heterogeneous
    equality).  For morphisms into [ListC] the positions of the codomain are
    numbers below a bound, so the condition can be stated with ordinary
    equality, with no axioms. *)
Definition cmorEq (C : Container) (m m' : CMor C ListC) : Prop :=
  forall s, u m s = u m' s /\
            forall (p : Fin (u m s)) (q : Fin (u m' s)),
              proj1_sig p = proj1_sig q -> f m s p = f m' s q.

Lemma cmorEq_refl : forall C (m : CMor C ListC), cmorEq m m.
Proof.
  intros C m s; split; [reflexivity |].
  intros p q Hpq. rewrite (Fin_eq p q Hpq). reflexivity.
Qed.

Lemma cmorEq_sym : forall C (m m' : CMor C ListC), cmorEq m m' -> cmorEq m' m.
Proof.
  intros C m m' H s. destruct (H s) as [Hu Hf]. split; [auto |].
  intros p q Hpq. symmetry. apply Hf. auto.
Qed.

Lemma cmorEq_trans : forall C (m1 m2 m3 : CMor C ListC),
    cmorEq m1 m2 -> cmorEq m2 m3 -> cmorEq m1 m3.
Proof.
  intros C m1 m2 m3 H12 H23 s.
  destruct (H12 s) as [Hu Hf]; destruct (H23 s) as [Hu' Hf']. split; [congruence |].
  intros p q Hpq.
  assert (Hlt : proj1_sig p < u m2 s) by (rewrite <- Hu; exact (proj2_sig p)).
  rewrite (Hf p (exist _ (proj1_sig p) Hlt) eq_refl). apply Hf'. exact Hpq.
Qed.

(** It is a congruence for composition on either side. *)
Lemma cmorEq_pre : forall C D (m m' : CMor C ListC) (k : CMor D C),
    cmorEq m m' -> cmorEq (ccomp m k) (ccomp m' k).
Proof.
  intros C D m m' k H s. destruct (H (u k s)) as [Hu Hf]. split; [exact Hu |].
  intros p q Hpq. simpl. f_equal. apply Hf. exact Hpq.
Qed.

Lemma cmorEq_post : forall C (m m' : CMor C ListC) (k : CMor ListC ListC),
    cmorEq m m' -> cmorEq (ccomp k m) (ccomp k m').
Proof.
  intros C m m' k H s. destruct (H s) as [Hu Hf].
  assert (Hk : forall a b, a = b -> forall (p : Fin (u k a)) (q : Fin (u k b)),
               proj1_sig p = proj1_sig q -> proj1_sig (f k a p) = proj1_sig (f k b q)).
  { intros a b E; subst b. intros p q Hpq. rewrite (Fin_eq p q Hpq). reflexivity. }
  split.
  - simpl. rewrite Hu. reflexivity.
  - intros p q Hpq. simpl. apply Hf. apply (Hk _ _ Hu). exact Hpq.
Qed.

(** Under function extensionality [cmorEq] is equality of container
    morphisms, so every construction whatsoever respects it.  The results
    below that concern the list interface itself are proved without this
    assumption; it is used only for [cmorEq_run_lifted]. *)
Definition FunExt : Prop :=
  forall (A : Type) (B : A -> Type) (g h : forall a, B a), (forall a, g a = h a) -> g = h.

Lemma cmorEq_eq : FunExt -> forall C (m m' : CMor C ListC), cmorEq m m' -> m = m'.
Proof.
  intros FE C [u1 f1] [u2 f2] H.
  assert (Hu : u1 = u2) by (apply FE; intros s; apply (proj1 (H s))).
  subst u2. f_equal. apply FE; intros s. apply FE; intros p.
  apply (proj2 (H s) p p eq_refl).
Qed.

(** From a Presburger-definable morphism of arity 1 that is in range, build a
    container morphism [ListC => ListC]. *)
Lemma to_cmor_bound : forall (m : PPCm) (H : in_range 1 m) n
                             (i : Fin (pevl (shape m) (env1 n))),
    pevl (pos m) (ext (env1 n) 1 (proj1_sig i)) < n.
Proof.
  intros m H n [i Hi]; simpl.
  specialize (H (env1 n) i Hi). simpl in H. unfold env1 in H at 2. simpl in H. lia.
Qed.

Definition to_cmor (m : PPCm) (H : in_range 1 m) : CMor ListC ListC :=
  mkMor ListC ListC
        (fun n => pevl (shape m) (env1 n))
        (fun n i => exist _ (pevl (pos m) (ext (env1 n) 1 (proj1_sig i)))
                          (to_cmor_bound H n i)).

Lemma to_cmor_u : forall (m : PPCm) (H : in_range 1 m) n,
    u (to_cmor H) n = pevl (shape m) (env1 n).
Proof. reflexivity. Qed.

Lemma to_cmor_f : forall (m : PPCm) (H : in_range 1 m) n (i : Fin (u (to_cmor H) n)),
    proj1_sig (f (to_cmor H) n i) = pevl (pos m) (ext (env1 n) 1 (proj1_sig i)).
Proof. reflexivity. Qed.

(** Representations of lists as elements of the extension of [ListC]. *)
Definition rep_to_ext (X : Type) (r : Rep X) : Ext ListC X :=
  existT (fun n => Fin n -> X) (fst r) (fun i : Fin (fst r) => snd r (proj1_sig i)).

Definition ext_to_rep (X : Type) (d : X) (e : Ext ListC X) : Rep X :=
  (projT1 e, fun i => match le_lt_dec (projT1 e) i with
                      | left _ => d
                      | right Hi => projT2 e (exist _ i Hi)
                      end).

(** The extension of [to_cmor m] agrees with the arithmetic interpretation:
    for every element [e] of the extension of the list container, applying
    [to_cmor m] and then reading off the list is the same as reading off
    the list and then applying [interp m]. *)
Theorem to_cmor_interp : forall (m : PPCm) (H : in_range 1 m) X (d : X) (e : Ext ListC X),
    RepEq (ext_to_rep d (mmap (to_cmor H) e)) (interp m [ext_to_rep d e] d).
Proof.
  intros m H X d [n g]. unfold RepEq, ext_to_rep, interp; simpl.
  assert (He : forall j, env [(n, fun i => match le_lt_dec n i with
                                           | left _ => d
                                           | right Hi => g (exist _ i Hi) end)] j = env1 n j).
  { intros j. apply env_single. }
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

(** *** Equal morphisms have equal extensions and induce equal behaviour *)

Lemma cmorEq_mmap : forall C (m m' : CMor C ListC),
    cmorEq m m' ->
    forall X (d : X) (e : Ext C X),
      RepEq (ext_to_rep d (mmap m e)) (ext_to_rep d (mmap m' e)).
Proof.
  intros C m m' H X d [s g]. destruct (H s) as [Hu Hf].
  unfold RepEq, ext_to_rep, mmap; simpl. split; [exact Hu |].
  intros i Hi.
  destruct (le_lt_dec (u m s) i) as [Hle | Hlt]; [exfalso; lia |].
  destruct (le_lt_dec (u m' s) i) as [Hle' | Hlt']; [exfalso; lia |].
  f_equal. apply Hf. reflexivity.
Qed.

(** An environment's responses to two equal moves have the same index and
    lead to the same state. *)
Lemma env_resp : forall E (e : forall s, option (Fin s * E)) (a b : nat),
    a = b ->
    match e a, e b with
    | Some (p, w), Some (q, w') => proj1_sig p = proj1_sig q /\ w = w'
    | None, None => True
    | _, _ => False
    end.
Proof. intros E e a b H; subst b. destruct (e a) as [[p w] |]; auto. Qed.

(** Equal adapters make every agent produce the same run, against every
    environment, for every number of rounds. *)
Theorem cmorEq_run : forall C (m m' : CMor C ListC),
    cmorEq m m' ->
    forall X E (a : Agent C X) (e : Env ListC E) x w n,
      run (wrap m a) e x w n = run (wrap m' a) e x w n.
Proof.
  intros C m m' H X E a e x w n. revert x w.
  induction n as [| n IH]; intros x w; [reflexivity |].
  cbn [run]. unfold readout, update, wrap.
  destruct (a x) as [s g]. cbn [mmap projT1 projT2].
  destruct (H s) as [Hu Hf].
  generalize (env_resp (e w) Hu).
  destruct (e w (u m s)) as [[p w1] |]; destruct (e w (u m' s)) as [[q w2] |];
    intros Hpq; try contradiction.
  - destruct Hpq as [Hpq Hw]. subst w2.
    f_equal; [exact Hu |]. rewrite (Hf p q Hpq). apply IH.
  - f_equal. exact Hu.
Qed.

(** The same holds one step at a time for the liftings of the two adapters
    to batches of items of any interface [K]: they send every batch to the
    same list of items, each with its continuation ... *)
Lemma cmorEq_whisker : forall C (m m' : CMor C ListC),
    cmorEq m m' ->
    forall (K : Container) X (d : Ext K X) (e : Ext (cComp C K) X),
      RepEq (ext_to_rep d (assoc (mmap (whisker m K) e)))
            (ext_to_rep d (assoc (mmap (whisker m' K) e))).
Proof. intros C m m' H K X d e. rewrite !whisker_assoc. apply cmorEq_mmap; assumption. Qed.

(** ... and, given function extensionality, for whole runs. *)
Theorem cmorEq_run_lifted : FunExt -> forall C (m m' : CMor C ListC),
    cmorEq m m' ->
    forall (K : Container) X E (a : Agent (cComp C K) X) (e : Env (cComp ListC K) E) x w n,
      run (wrap (whisker m K) a) e x w n = run (wrap (whisker m' K) a) e x w n.
Proof. intros FE C m m' H K X E a e x w n. rewrite (cmorEq_eq FE H). reflexivity. Qed.

(** *** Observational completeness

    The converse of [cmorEq_run]: adapters that no agent and no environment
    can tell apart are equal.  It holds for every source container whose
    positions have decidable equality and which has a shape with no
    positions (the empty batch): if the position maps differ somewhere, an
    agent that emits the empty shape when it receives one of the two answers,
    and a non-empty one otherwise, produces different runs.  Stateless
    environments already suffice. *)

Theorem runs_cmorEq : forall C (m m' : CMor C ListC),
    (forall s (p q : Pos C s), {p = q} + {p <> q}) ->
    forall s0 : Shape C, (Pos C s0 -> False) ->
    (forall X (a : Agent C X) (e : Env ListC unit) x n,
        run (wrap m a) e x tt n = run (wrap m' a) e x tt n) ->
    cmorEq m m'.
Proof.
  intros C m m' dec s0 Hs0 Hrun s.
  assert (Hu : u m s = u m' s).
  { pose proof (Hrun unit (fun _ => existT (fun s' => Pos C s' -> unit) s (fun _ => tt))
                     (fun _ _ => None) tt 1) as H1.
    rewrite !run_one in H1. exact (f_equal (fun l => nth 0 l 0) H1). }
  split; [exact Hu |].
  intros p q Hpq.
  destruct (dec s (f m s p) (f m' s q)) as [E | NE]; [exact E | exfalso].
  set (a := fun x : option (Pos C s) =>
              match x with
              | None => existT (fun s' => Pos C s' -> option (Pos C s)) s (fun r => Some r)
              | Some r => existT (fun s' => Pos C s' -> option (Pos C s))
                                 (if dec s r (f m s p) then s0 else s) (fun _ => Some r)
              end).
  set (e := fun (_ : unit) (k : nat) =>
              match lt_dec (proj1_sig p) k with
              | left H => Some (exist (fun i => i < k) (proj1_sig p) H, tt)
              | right _ => None
              end).
  assert (Hstep : forall (mm : CMor C ListC) (pp : Fin (u mm s)),
             proj1_sig pp = proj1_sig p ->
             run (wrap mm a) e None tt 2
             = [u mm s; u mm (if dec s (f mm s pp) (f m s p) then s0 else s)]).
  { intros mm pp Hpp. rewrite run_two.
    change (readout (wrap mm a) None) with (u mm s).
    unfold e at 1. destruct (lt_dec (proj1_sig p) (u mm s)) as [H | H].
    - replace (exist (fun i => i < u mm s) (proj1_sig p) H) with pp
        by (apply Fin_eq; simpl; exact Hpp).
      reflexivity.
    - exfalso. apply H. rewrite <- Hpp. exact (proj2_sig pp). }
  pose proof (Hrun (option (Pos C s)) a e None 2) as Hr.
  rewrite (Hstep m p eq_refl), (Hstep m' q (eq_sym Hpq)) in Hr.
  destruct (dec s (f m s p) (f m s p)) as [_ | Hn]; [| apply Hn; reflexivity].
  destruct (dec s (f m' s q) (f m s p)) as [Hy | _]; [apply NE; symmetry; exact Hy |].
  assert (H2 : u m s0 = u m' s) by exact (f_equal (fun l => nth 1 l 0) Hr).
  assert (Hpos : 0 < u m s0).
  { pose proof (proj2_sig p) as Hp. simpl in Hp. rewrite H2, <- Hu. lia. }
  apply Hs0. exact (f m s0 (exist _ 0 Hpos)).
Qed.

Lemma Fin_dec : forall n (p q : Fin n), {p = q} + {p <> q}.
Proof.
  intros n p q. destruct (Nat.eq_dec (proj1_sig p) (proj1_sig q)) as [E | NE].
  - left. apply Fin_eq. exact E.
  - right. intros H. apply NE. rewrite H. reflexivity.
Qed.

Lemma Fin0_empty : Fin 0 -> False.
Proof. intros [i Hi]. lia. Qed.

(** For adapters on the list interface, equality of container morphisms *is*
    observational equivalence. *)
Theorem list_adapters_iff_runs : forall m m' : CMor ListC ListC,
    cmorEq m m' <->
    (forall X E (a : Agent ListC X) (e : Env ListC E) x w n,
        run (wrap m a) e x w n = run (wrap m' a) e x w n).
Proof.
  intros m m'. split.
  - intros H X E a e x w n. apply cmorEq_run. exact H.
  - intros H. apply (@runs_cmorEq ListC m m' Fin_dec 0 Fin0_empty).
    intros X a e x n. apply H.
Qed.

(** *** From arithmetic to container morphisms

    The arithmetic representation applies to morphisms from [k] lists to a
    list.  A *source* packages what the representation needs to know about
    the domain: the container, the arity [k], the environment that a shape
    determines (the [k] lengths), and the flat numbering of its positions. *)

Record Src := mkSrc {
  SC : Container;
  ar : nat;
  en : Shape SC -> nat -> nat;
  fl : forall s, Pos SC s -> nat;
  en_vanishes : forall s, vanishes ar (en s);
  en_onto : forall rho, vanishes ar rho -> exists s, forall j, en s j = rho j;
  fl_inj : forall s (p q : Pos SC s), fl s p = fl s q -> p = q
}.

Arguments en S s j : rename.
Arguments fl S s p : rename.

(** One list. *)
Lemma src1_onto : forall rho, vanishes 1 rho -> exists n : nat, forall j, env1 n j = rho j.
Proof.
  intros rho Hv. exists (rho 0). intros [| j]; [reflexivity | symmetry; apply Hv; lia].
Qed.

Definition src1 : Src :=
  @mkSrc ListC 1 env1 (fun n (p : Fin n) => proj1_sig p)
         vanishes_env1 src1_onto (fun n p q H => Fin_eq p q H).

(** Two lists: the product of the list container with itself.  Positions are
    numbered consecutively, those of the first list first. *)
Definition List2C : Container := cProd ListC ListC.

Definition flat_idx (s : nat * nat) (p : Pos List2C s) : nat :=
  match p with
  | inl i => proj1_sig i
  | inr j => fst s + proj1_sig j
  end.

Arguments flat_idx s p : clear implicits.

Lemma flat_idx_inj : forall s (p q : Pos List2C s), flat_idx s p = flat_idx s q -> p = q.
Proof.
  intros [n1 n2] [[i Hi] | [i Hi]] [[j Hj] | [j Hj]] H; simpl in *.
  - f_equal. apply Fin_eq. exact H.
  - exfalso. lia.
  - exfalso. lia.
  - f_equal. apply Fin_eq. simpl. lia.
Qed.

Lemma src2_onto : forall rho, vanishes 2 rho ->
    exists s : nat * nat, forall j, env2 (fst s) (snd s) j = rho j.
Proof.
  intros rho Hv. exists (rho 0, rho 1).
  intros [| [| j]]; [reflexivity | reflexivity | symmetry; apply Hv; lia].
Qed.

Definition src2 : Src :=
  @mkSrc List2C 2 (fun s => env2 (fst s) (snd s)) flat_idx
         (fun s => vanishes_env2 (fst s) (snd s)) src2_onto flat_idx_inj.

(** A pair of piecewise-linear terms [t] *represents* a container morphism
    [m] out of a source when it computes the shape map of [m] and the flat
    index of every value of its position maps. *)
Definition represents (S : Src) (t : PPCm) (m : CMor (SC S) ListC) : Prop :=
  forall s, u m s = pevl (shape t) (en S s) /\
            forall p : Fin (u m s),
              fl S s (f m s p) = pevl (pos t) (ext (en S s) (ar S) (proj1_sig p)).

Lemma to_cmor_represents : forall (t : PPCm) (H : in_range 1 t), represents src1 t (to_cmor H).
Proof. intros t H n; split; [reflexivity | intros p; reflexivity]. Qed.

Lemma cid_represents : represents src1 idm (cid ListC).
Proof. intros n; split; [reflexivity | intros p; reflexivity]. Qed.

(** A representation of arity 2 that is in range determines a container
    morphism from two lists to a list. *)
Lemma to_cmor2_bound : forall (m : PPCm) (H : in_range 2 m) (s : nat * nat)
                              (i : Fin (pevl (shape m) (env2 (fst s) (snd s)))),
    pevl (pos m) (ext (env2 (fst s) (snd s)) 2 (proj1_sig i)) < fst s + snd s.
Proof.
  intros m H [n1 n2] [i Hi]; simpl in *.
  exact (H (env2 n1 n2) i Hi).
Qed.

Lemma split_pos_r : forall n1 n2 p, p < n1 + n2 -> ~ p < n1 -> p - n1 < n2.
Proof. intros; lia. Qed.

Definition split_pos (n1 n2 p : nat) (H : p < n1 + n2) : (Fin n1 + Fin n2)%type :=
  match lt_dec p n1 with
  | left H1 => inl (exist _ p H1)
  | right H1 => inr (exist _ (p - n1) (@split_pos_r n1 n2 p H H1))
  end.

Arguments split_pos n1 n2 p H : clear implicits.

Lemma flat_split : forall n1 n2 p (H : p < n1 + n2),
    flat_idx (n1, n2) (split_pos n1 n2 p H) = p.
Proof.
  intros n1 n2 p H. unfold split_pos. destruct (lt_dec p n1); simpl; lia.
Qed.

Definition to_cmor2 (m : PPCm) (H : in_range 2 m) : CMor List2C ListC :=
  mkMor List2C ListC
        (fun s => pevl (shape m) (env2 (fst s) (snd s)))
        (fun s i => split_pos (fst s) (snd s) _ (@to_cmor2_bound m H s i)).

Lemma to_cmor2_represents : forall (t : PPCm) (H : in_range 2 t), represents src2 t (to_cmor2 H).
Proof. intros t H [n1 n2]; split; [reflexivity | intros p; apply flat_split]. Qed.

(** Observational completeness holds for adapters out of a pair of lists as
    well. *)
Lemma List2_dec : forall s (p q : Pos List2C s), {p = q} + {p <> q}.
Proof.
  intros s p q. destruct (Nat.eq_dec (flat_idx s p) (flat_idx s q)) as [E | NE].
  - left. apply flat_idx_inj. exact E.
  - right. intros H. apply NE. rewrite H. reflexivity.
Qed.

Lemma List2_empty : Pos List2C (0, 0) -> False.
Proof. intros [p | p]; exact (Fin0_empty p). Qed.

Theorem list2_adapters_iff_runs : forall m m' : CMor List2C ListC,
    cmorEq m m' <->
    (forall X E (a : Agent List2C X) (e : Env ListC E) x w n,
        run (wrap m a) e x w n = run (wrap m' a) e x w n).
Proof.
  intros m m'. split.
  - intros H X E a e x w n. apply cmorEq_run. exact H.
  - intros H. apply (@runs_cmorEq List2C m m' List2_dec (0, 0) List2_empty).
    intros X a e x n. apply H.
Qed.

(** Its extension agrees with the arithmetic interpretation on the two lists
    obtained from a pair by the projections. *)
Theorem to_cmor2_interp : forall (m : PPCm) (H : in_range 2 m) X (d : X) (e : Ext List2C X),
    RepEq (ext_to_rep d (mmap (to_cmor2 H) e))
          (interp m [ext_to_rep d (mmap (cfst ListC ListC) e);
                     ext_to_rep d (mmap (csnd ListC ListC) e)] d).
Proof.
  intros m H X d [[n1 n2] g].
  set (e := existT (fun s => Pos List2C s -> X) (n1, n2) g).
  set (r1 := ext_to_rep d (mmap (cfst ListC ListC) e)).
  set (r2 := ext_to_rep d (mmap (csnd ListC ListC) e)).
  assert (He : forall j, env [r1; r2] j = env2 n1 n2 j) by (intros j; apply env_pair).
  assert (Hs : pevl (shape m) (env [r1; r2]) = pevl (shape m) (env2 n1 n2))
    by (apply pevl_ext; exact He).
  assert (Hp : forall i, pevl (pos m) (ext (env [r1; r2]) 2 i)
                         = pevl (pos m) (ext (env2 n1 n2) 2 i)).
  { intros i. apply pevl_ext; intros j. unfold ext. destruct (j =? 2); auto. }
  (* the value stored at a flat position of the pair *)
  assert (Hg : forall p (Hlt : p < n1 + n2),
             g (split_pos n1 n2 p Hlt) = flat [r1; r2] d p).
  { intros p Hlt. unfold split_pos. cbn [flat r1 r2 ext_to_rep mmap e cfst csnd u f projT1 projT2 fst snd].
    destruct (lt_dec p n1) as [H1 | H1].
    - destruct (Nat.ltb_spec p n1); [| exfalso; lia].
      destruct (le_lt_dec n1 p) as [Hle | Hlt']; [exfalso; lia |].
      rewrite (le_unique _ _ H1 Hlt'). reflexivity.
    - destruct (Nat.ltb_spec p n1); [exfalso; lia |].
      destruct (Nat.ltb_spec (p - n1) n2); [| exfalso; lia].
      destruct (le_lt_dec n2 (p - n1)) as [Hle | Hlt']; [exfalso; lia |].
      rewrite (le_unique _ _ (@split_pos_r n1 n2 p Hlt H1) Hlt'). reflexivity. }
  split.
  - symmetry. exact Hs.
  - intros i Hi.
    change (snd (interp m [r1; r2] d) i) with (flat [r1; r2] d (pevl (pos m) (ext (env [r1; r2]) 2 i))).
    rewrite Hp.
    change (fst (ext_to_rep d (mmap (to_cmor2 H) e))) with (pevl (shape m) (env2 n1 n2)) in Hi.
    cbn [ext_to_rep snd mmap e projT1 projT2].
    destruct (le_lt_dec (u (to_cmor2 H) (n1, n2)) i) as [Hle | Hlt].
    + exfalso. change (u (to_cmor2 H) (n1, n2)) with (pevl (shape m) (env2 n1 n2)) in Hle. lia.
    + apply Hg.
Qed.

(** The arithmetic composite represents the composite of container
    morphisms ... *)
Lemma comp1_represents : forall (S : Src) (l r : PPCm)
                                (m : CMor ListC ListC) (m' : CMor (SC S) ListC),
    represents src1 l m -> represents S r m' ->
    represents S (comp1 (ar S) l r) (ccomp m m').
Proof.
  intros S l r m m' Hm Hm' s.
  destruct (Hm' s) as [Hu' Hf']. destruct (Hm (u m' s)) as [Hu Hf].
  split.
  - change (u m (u m' s) = pevl (shape (comp1 (ar S) l r)) (en S s)).
    rewrite comp1_shape_gen by apply en_vanishes. rewrite <- Hu'. exact Hu.
  - intros p.
    change (fl S s (f m' s (f m (u m' s) p))
            = pevl (pos (comp1 (ar S) l r)) (ext (en S s) (ar S) (proj1_sig p))).
    rewrite comp1_pos_gen by apply en_vanishes. rewrite Hf', <- Hu'.
    f_equal. f_equal. exact (Hf p).
Qed.

(** ... and the composite of an arity-2 term with two terms over the same
    inputs represents composition with the pairing of the two morphisms. *)
Lemma comp2_represents : forall (S : Src) (l r1 r2 : PPCm)
                                (m : CMor List2C ListC) (m1 m2 : CMor (SC S) ListC),
    represents src2 l m -> represents S r1 m1 -> represents S r2 m2 ->
    represents S (comp2 (ar S) l r1 r2) (ccomp m (cpair m1 m2)).
Proof.
  intros S l r1 r2 m m1 m2 Hm H1 H2 s.
  destruct (H1 s) as [Hu1 Hf1]. destruct (H2 s) as [Hu2 Hf2].
  destruct (Hm (u m1 s, u m2 s)) as [Hu Hf].
  split.
  - change (u m (u m1 s, u m2 s) = pevl (shape (comp2 (ar S) l r1 r2)) (en S s)).
    rewrite comp2_shape_gen by apply en_vanishes. rewrite <- Hu1, <- Hu2. exact Hu.
  - intros p.
    change (fl S s (f (cpair m1 m2) s (f m (u m1 s, u m2 s) p))
            = pevl (pos (comp2 (ar S) l r1 r2)) (ext (en S s) (ar S) (proj1_sig p))).
    rewrite comp2_pos_gen by apply en_vanishes. rewrite <- Hu1, <- Hu2.
    pose proof (Hf p) as Hq.
    change (flat_idx (u m1 s, u m2 s) (f m (u m1 s, u m2 s) p)
            = pevl (pos l) (ext (env2 (u m1 s) (u m2 s)) 2 (proj1_sig p))) in Hq.
    rewrite <- Hq.
    destruct (f m (u m1 s, u m2 s) p) as [p1 | p2]; cbn [flat_idx fst snd cpair f].
    + pose proof (proj2_sig p1) as Hlt. cbn [fst] in Hlt.
      match goal with |- context [?a <? ?b] => destruct (Nat.ltb_spec a b) end;
        [apply Hf1 | exfalso; lia].
    + match goal with |- context [?a <? ?b] => destruct (Nat.ltb_spec a b) end;
        [exfalso; lia |].
      match goal with |- context [u m1 s + ?x - u m1 s] =>
        replace (u m1 s + x - u m1 s) with x by lia end.
      apply Hf2.
Qed.

(** Soundness: if the representing terms are equal in the arithmetic sense
    (on the environments of the source), the container morphisms are equal. *)
Theorem represents_cmorEq : forall (S : Src) (t t' : PPCm) (m m' : CMor (SC S) ListC),
    represents S t m -> represents S t' m' -> pcmEQ_on (ar S) t t' -> cmorEq m m'.
Proof.
  intros S t t' m m' Hm Hm' Heq s.
  destruct (Hm s) as [Hu Hf]; destruct (Hm' s) as [Hu' Hf'].
  destruct (Heq (en S s) (en_vanishes S s)) as [Hs Hp].
  split; [congruence |].
  intros p q Hpq. apply (fl_inj S). rewrite Hf, Hf', <- Hpq. apply Hp.
  rewrite <- Hu. exact (proj2_sig p).
Qed.

(** Exactness: conversely, equal container morphisms have representing terms
    that are equal on the environments of the source ... *)
Theorem cmorEq_pcmEQ_on : forall (S : Src) (t t' : PPCm) (m m' : CMor (SC S) ListC),
    represents S t m -> represents S t' m' -> cmorEq m m' -> pcmEQ_on (ar S) t t'.
Proof.
  intros S t t' m m' Hm Hm' Heq rho Hv.
  destruct (en_onto S Hv) as [s Hs].
  assert (E1 : forall p, pevl p rho = pevl p (en S s))
    by (intros p; apply pevl_ext; intros j; symmetry; apply Hs).
  assert (E2 : forall p i, pevl p (ext rho (ar S) i) = pevl p (ext (en S s) (ar S) i)).
  { intros p i. apply pevl_ext; intros j. unfold ext. destruct (j =? ar S); auto. }
  destruct (Hm s) as [Hu Hf]; destruct (Hm' s) as [Hu' Hf']; destruct (Heq s) as [Huu Hff].
  rewrite !E1. split; [congruence |].
  intros i Hi. rewrite !E2.
  assert (Hi1 : i < u m s) by (rewrite Hu; exact Hi).
  assert (Hi2 : i < u m' s) by (rewrite <- Huu; exact Hi1).
  pose proof (Hf (exist _ i Hi1)) as A. pose proof (Hf' (exist _ i Hi2)) as B.
  simpl in A, B. rewrite <- A, <- B. f_equal. apply Hff. reflexivity.
Qed.

(** ... so for closed terms the arithmetic statement [pcmEQ] is *equivalent*
    to equality of the container morphisms. *)
Theorem pcmEQ_iff_cmorEq : forall (S : Src) (t t' : PPCm) (m m' : CMor (SC S) ListC),
    represents S t m -> represents S t' m' ->
    closed (ar S) t = true -> closed (ar S) t' = true ->
    (pcmEQ (ar S) t t' <-> cmorEq m m').
Proof.
  intros S t t' m m' Hm Hm' Hc Hc'. split.
  - intros H. apply (represents_cmorEq Hm Hm'). apply pcmEQ_pcmEQ_on. exact H.
  - intros H. apply pcmEQ_on_pcmEQ; auto. apply (cmorEq_pcmEQ_on Hm Hm' H).
Qed.

(** A counterexample found by the bounded search is a genuine inequality of
    container morphisms. *)
Theorem find_cex_cmor : forall (l r : PPCm) (m m' : CMor ListC ListC) b c,
    represents src1 l m -> represents src1 r m' ->
    find_cex l r b = Some c -> ~ cmorEq m m'.
Proof.
  intros l r m m' b c Hm Hm' Hc Heq.
  assert (Hn : find_cex l r b = None).
  { apply find_cex_spec. intros n _.
    exact (cmorEq_pcmEQ_on Hm Hm' Heq (vanishes_env1 n)). }
  congruence.
Qed.

Corollary pcmEQ_cmorEq : forall (l r : PPCm) (Hl : in_range 1 l) (Hr : in_range 1 r),
    pcmEQ 1 l r -> cmorEq (to_cmor Hl) (to_cmor Hr).
Proof.
  intros l r Hl Hr Heq.
  exact (represents_cmorEq (to_cmor_represents Hl) (to_cmor_represents Hr)
                           (pcmEQ_pcmEQ_on Heq)).
Qed.

(** Taken together: for closed, well-typed representations of arity 1 the
    statement proved by the tactic [containers] is equivalent to the
    observational equivalence of the two adapters. *)
Theorem pcmEQ_iff_runs : forall (l r : PPCm) (Hl : in_range 1 l) (Hr : in_range 1 r),
    closed 1 l = true -> closed 1 r = true ->
    (pcmEQ 1 l r <->
     forall X E (a : Agent ListC X) (e : Env ListC E) x w n,
       run (wrap (to_cmor Hl) a) e x w n = run (wrap (to_cmor Hr) a) e x w n).
Proof.
  intros l r Hl Hr Hc Hc'.
  rewrite (pcmEQ_iff_cmorEq (S := src1) (to_cmor_represents Hl) (to_cmor_represents Hr) Hc Hc').
  apply list_adapters_iff_runs.
Qed.

(** Hence an arithmetic equality between well-typed morphisms yields equal
    extensions, at every data type ... *)
Theorem pcmEQ_mmap : forall (l r : PPCm) (Hl : in_range 1 l) (Hr : in_range 1 r),
    pcmEQ 1 l r ->
    forall X (d : X) (e : Ext ListC X),
      RepEq (ext_to_rep d (mmap (to_cmor Hl) e)) (ext_to_rep d (mmap (to_cmor Hr) e)).
Proof. intros l r Hl Hr Heq. apply cmorEq_mmap, pcmEQ_cmorEq, Heq. Qed.

(** ... in particular on the one-step behaviour of any agent ... *)
Corollary pcmEQ_wrap : forall (l r : PPCm) (Hl : in_range 1 l) (Hr : in_range 1 r),
    pcmEQ 1 l r ->
    forall X (d : X) (a : Agent ListC X) x,
      RepEq (ext_to_rep d (wrap (to_cmor Hl) a x)) (ext_to_rep d (wrap (to_cmor Hr) a x)).
Proof. intros l r Hl Hr Heq X d a x. unfold wrap. apply pcmEQ_mmap; assumption. Qed.

(** ... on the liftings of the two morphisms to batches of items ... *)
Corollary pcmEQ_whisker : forall (l r : PPCm) (Hl : in_range 1 l) (Hr : in_range 1 r),
    pcmEQ 1 l r ->
    forall (K : Container) X (d : Ext K X) (e : Ext (cComp ListC K) X),
      RepEq (ext_to_rep d (assoc (mmap (whisker (to_cmor Hl) K) e)))
            (ext_to_rep d (assoc (mmap (whisker (to_cmor Hr) K) e))).
Proof. intros l r Hl Hr Heq. apply cmorEq_whisker, pcmEQ_cmorEq, Heq. Qed.

(** ... and on whole runs: adapters that are equal in the arithmetic sense
    make every agent on the list interface produce the same run. *)
Theorem pcmEQ_run : forall (l r : PPCm) (Hl : in_range 1 l) (Hr : in_range 1 r),
    pcmEQ 1 l r ->
    forall X E (a : Agent ListC X) (e : Env ListC E) x w n,
      run (wrap (to_cmor Hl) a) e x w n = run (wrap (to_cmor Hr) a) e x w n.
Proof. intros l r Hl Hr Heq. apply cmorEq_run, pcmEQ_cmorEq, Heq. Qed.

(** Losslessness.  The arithmetic condition [lossless] (injectivity of the
    position map together with [u n = n]) implies that the container morphism
    is cartesian; the inverse is obtained from the pigeonhole principle for
    bounded functions ([FinFun]). *)
Theorem lossless_cartesian : forall (m : PPCm) (H : in_range 1 m),
    lossless m -> cartesian (to_cmor H).
Proof.
  intros m H Hloss n.
  destruct (Hloss (env1 n)) as [Hs Hinj]. unfold env1 in Hs at 2, Hinj; simpl in Hs, Hinj.
  set (f0 := fun i => pevl (pos m) (ext (env1 n) 1 i)).
  assert (HbF : bFun n f0).
  { intros i Hi. unfold f0. specialize (H (env1 n) i). simpl in H.
    unfold env1 in H at 3; simpl in H. rewrite Hs in H. specialize (H Hi). lia. }
  assert (HbI : bInjective n f0) by (intros i j Hi Hj; apply Hinj; assumption).
  destruct (bSurjective_bBijective HbF (proj1 (bInjective_bSurjective HbF) HbI))
    as [g0 [HbG Hinv]].
  assert (Hlt : forall q : Fin n, g0 (proj1_sig q) < pevl (shape m) (env1 n)).
  { intros [j Hj]; simpl. rewrite Hs. apply HbG; assumption. }
  exists (fun q => exist _ (g0 (proj1_sig q)) (Hlt q)). split.
  - intros [i Hi]. apply Fin_eq; simpl. apply Hinv. rewrite <- Hs; assumption.
  - intros [j Hj]. apply Fin_eq; simpl. apply Hinv; assumption.
Qed.

(** A lossless morphism moreover has a computable section: the position of
    the output that is fetched from a given position of the input is found by
    bounded search.  Hence every lossless adapter lifts to batches that are
    answered all at once. *)
Fixpoint bfind (h : nat -> nat) (i n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => if h n' =? i then n' else bfind h i n'
  end.

Lemma bfind_ok : forall h i n,
    (exists j, j < n /\ h j = i) -> bfind h i n < n /\ h (bfind h i n) = i.
Proof.
  intros h i n. induction n as [| n IH]; intros [j [Hj Hh]]; [lia |].
  simpl. destruct (Nat.eqb_spec (h n) i) as [E | E]; [split; [lia | exact E] |].
  assert (Hj' : j < n).
  { destruct (Nat.eq_dec j n) as [E' | E']; [subst j; contradiction | lia]. }
  destruct (IH (ex_intro _ j (conj Hj' Hh))) as [H1 H2]. split; [lia | exact H2].
Qed.

Lemma lossless_section : forall (m : PPCm), in_range 1 m -> lossless m ->
    forall n i, i < n ->
      bfind (fun j => pevl (pos m) (ext (env1 n) 1 j)) i n < pevl (shape m) (env1 n)
      /\ pevl (pos m) (ext (env1 n) 1
                       (bfind (fun j => pevl (pos m) (ext (env1 n) 1 j)) i n)) = i.
Proof.
  intros m H Hloss n i Hi.
  destruct (Hloss (env1 n)) as [Hs Hinj]. unfold env1 in Hs at 2, Hinj; simpl in Hs, Hinj.
  set (f0 := fun j => pevl (pos m) (ext (env1 n) 1 j)).
  assert (HbF : bFun n f0).
  { intros j Hj. unfold f0. specialize (H (env1 n) j). simpl in H.
    unfold env1 in H at 3; simpl in H. rewrite Hs in H. specialize (H Hj). lia. }
  assert (HbI : bInjective n f0) by (intros j j' Hj Hj'; apply Hinj; assumption).
  destruct (bfind_ok f0 (proj1 (bInjective_bSurjective HbF) HbI i Hi)) as [H1 H2].
  rewrite Hs. split; assumption.
Qed.

Definition lossless_inv (m : PPCm) (H : in_range 1 m) (L : lossless m)
           (n : nat) (p : Fin n) : Fin (u (to_cmor H) n) :=
  exist _ (bfind (fun j => pevl (pos m) (ext (env1 n) 1 j)) (proj1_sig p) n)
        (proj1 (lossless_section H L (proj2_sig p))).

Arguments lossless_inv {m} H L n p.

Lemma lossless_inv_ok : forall (m : PPCm) (H : in_range 1 m) (L : lossless m) n p,
    f (to_cmor H) n (lossless_inv H L n p) = p.
Proof.
  intros m H L n p. apply Fin_eq. rewrite to_cmor_f.
  exact (proj2 (lossless_section H L (proj2_sig p))).
Qed.

Definition lossless_all (m : PPCm) (H : in_range 1 m) (L : lossless m) (K : Container)
  : CMor (cAll ListC K) (cAll ListC K) :=
  lift_all (to_cmor H) (lossless_inv H L) (lossless_inv_ok H L) K.

(** ** Tree-shaped interfaces and flattening

    A planner emits a hierarchical plan -- a binary tree whose leaves are the
    atomic sub-tasks -- and accepts a result for each leaf.  Its interface is
    the container of (leaf-labelled) binary trees: shapes are tree skeletons
    and positions are leaves, which may occur at any depth.  The function
    that flattens a tree into a list (Listing 21 of the thesis) is a container
    morphism from the tree interface to the list interface whose position maps
    are bijections, i.e. a *cartesian*, lossless adapter: an environment that
    only understands flat batches can serve a hierarchical planner, and every
    result is routed back to exactly one leaf.  Its shape map is not
    injective (different plans flatten to batches of the same size), which is
    harmless: cartesianness constrains positions, not shapes. *)

Inductive TreeS : Set :=
| leaf : TreeS
| node : TreeS -> TreeS -> TreeS.

(** Positions of a skeleton: its leaves, addressed by left/right choices. *)
Fixpoint TreeP (s : TreeS) : Type :=
  match s with
  | leaf => unit
  | node l r => (TreeP l + TreeP r)%type
  end.

Definition TreeC : Container := mkCont TreeP.

(** The number of leaves. *)
Fixpoint Sum (s : TreeS) : nat :=
  match s with
  | leaf => 1
  | node l r => Sum l + Sum r
  end.

Lemma sub_lt_r : forall i (l r : TreeS), i < Sum (node l r) -> ~ i < Sum l -> i - Sum l < Sum r.
Proof. intros; simpl in *; lia. Qed.

(** Position map of flattening: output position [i] of the list is sent to
    the [i]-th leaf in left-to-right order. *)
Fixpoint flat_pos (s : TreeS) : Fin (Sum s) -> TreeP s :=
  match s return Fin (Sum s) -> TreeP s with
  | leaf => fun _ => tt
  | node l r => fun i =>
      match lt_dec (proj1_sig i) (Sum l) with
      | left H => inl (flat_pos l (exist _ (proj1_sig i) H))
      | right H => inr (flat_pos r (exist _ (proj1_sig i - Sum l)
                                            (sub_lt_r l r (proj2_sig i) H)))
      end
  end.

(** The inverse: the index of a leaf in left-to-right order. *)
Fixpoint leaf_index (s : TreeS) : TreeP s -> nat :=
  match s return TreeP s -> nat with
  | leaf => fun _ => 0
  | node l r => fun p =>
      match p with
      | inl pl => leaf_index l pl
      | inr pr => Sum l + leaf_index r pr
      end
  end.

Lemma leaf_index_lt : forall s (p : TreeP s), leaf_index s p < Sum s.
Proof.
  induction s as [| l IHl r IHr]; intros p; simpl.
  - lia.
  - destruct p as [pl | pr]; [specialize (IHl pl) | specialize (IHr pr)]; lia.
Qed.

Definition unflat_pos (s : TreeS) (p : TreeP s) : Fin (Sum s) :=
  exist _ (leaf_index s p) (leaf_index_lt s p).

(** [flatten : TreeC => ListC], the container morphism of Listing 21. *)
Definition flatten : CMor TreeC ListC := mkMor TreeC ListC Sum flat_pos.

Lemma flat_pos_index : forall s (i : Fin (Sum s)), leaf_index s (flat_pos s i) = proj1_sig i.
Proof.
  induction s as [| l IHl r IHr]; intros [i Hi]; simpl in *.
  - lia.
  - destruct (lt_dec i (Sum l)) as [H | H]; simpl.
    + rewrite IHl; reflexivity.
    + rewrite IHr; simpl; lia.
Qed.

Lemma flat_pos_ext : forall s (a b : Fin (Sum s)),
    proj1_sig a = proj1_sig b -> flat_pos s a = flat_pos s b.
Proof. intros s a b H. rewrite (Fin_eq a b H). reflexivity. Qed.

Lemma index_flat_pos : forall s (p : TreeP s), flat_pos s (unflat_pos s p) = p.
Proof.
  induction s as [| l IHl r IHr]; intros p; simpl in *.
  - destruct p; reflexivity.
  - destruct p as [pl | pr]; unfold unflat_pos in *; simpl.
    + destruct (lt_dec (leaf_index l pl) (Sum l)) as [H | H].
      * f_equal. etransitivity; [apply flat_pos_ext with (b := unflat_pos l pl); reflexivity | apply IHl].
      * exfalso; apply H; apply leaf_index_lt.
    + destruct (lt_dec (Sum l + leaf_index r pr) (Sum l)) as [H | H]; [lia |].
      f_equal. etransitivity; [apply flat_pos_ext with (b := unflat_pos r pr); simpl; lia | apply IHr].
Qed.

(** Flattening is a lossless (cartesian) adapter. *)
Theorem flatten_cartesian : cartesian flatten.
Proof.
  intros s. exists (unflat_pos s). split.
  - intros i. apply Fin_eq. simpl. apply flat_pos_index.
  - intros p. apply index_flat_pos.
Qed.

(** ... although its shape map is not injective: two different plans may
    flatten to batches of the same size. *)
Example Sum_not_injective :
  Sum (node leaf (node leaf leaf)) = Sum (node (node leaf leaf) leaf)
  /\ node leaf (node leaf leaf) <> node (node leaf leaf) leaf.
Proof. split; [reflexivity | discriminate]. Qed.

(** Wrapping a planner by [flatten] presents it to the environment as an
    agent on the list interface, to which the results above apply. *)
Definition flat_planner (X : Type) (a : Agent TreeC X) : Agent ListC X := wrap flatten a.

(** In particular, list adapters that are equal in the arithmetic sense give
    the planner the same runs when it is served through [flatten]. *)
Corollary pcmEQ_run_planner : forall (l r : PPCm) (Hl : in_range 1 l) (Hr : in_range 1 r),
    pcmEQ 1 l r ->
    forall X E (a : Agent TreeC X) (e : Env ListC E) x w n,
      run (wrap (ccomp (to_cmor Hl) flatten) a) e x w n
      = run (wrap (ccomp (to_cmor Hr) flatten) a) e x w n.
Proof. intros l r Hl Hr Heq. apply cmorEq_run, cmorEq_pre, pcmEQ_cmorEq, Heq. Qed.

(** A lossless list adapter after flattening is a lossless adapter out of the
    tree interface. *)
Corollary lossless_after_flatten : forall (m : PPCm) (H : in_range 1 m),
    lossless m -> cartesian (ccomp (to_cmor H) flatten).
Proof.
  intros m H Hl. apply cartesian_comp; [apply flatten_cartesian | apply lossless_cartesian; assumption].
Qed.

(** Flattening has a section (the index of a leaf), so it also lifts to plans
    and batches whose results are returned all at once: given a result for
    every slot of the batch, every leaf of the plan receives its result. *)
Definition flatten_all (K : Container) : CMor (cAll TreeC K) (cAll ListC K) :=
  lift_all flatten unflat_pos index_flat_pos K.

(** ** Observational completeness needs an empty shape

    The two adapters that present a plan as a batch of one item -- its
    leftmost leaf, respectively its rightmost leaf -- are different container
    morphisms, yet no agent and no environment can tell them apart by the
    moves that cross the interface: every run through either of them is a
    sequence of ones.  The tree container has no shape without positions, so
    the hypothesis of [runs_cmorEq] fails for it, and so does its conclusion. *)

Fixpoint leftmost (s : TreeS) : TreeP s :=
  match s return TreeP s with
  | leaf => tt
  | node l r => inl (leftmost l)
  end.

Fixpoint rightmost (s : TreeS) : TreeP s :=
  match s return TreeP s with
  | leaf => tt
  | node l r => inr (rightmost r)
  end.

Definition pick_left : CMor TreeC ListC :=
  mkMor TreeC ListC (fun _ => 1) (fun s _ => leftmost s).

Definition pick_right : CMor TreeC ListC :=
  mkMor TreeC ListC (fun _ => 1) (fun s _ => rightmost s).

Lemma pick_runs : forall X E (a : Agent TreeC X) (e : Env ListC E) n x x' w,
    run (wrap pick_left a) e x w n = run (wrap pick_right a) e x' w n.
Proof.
  intros X E a e. induction n as [| n IH]; intros x x' w; [reflexivity |].
  cbn [run].
  change (readout (wrap pick_left a) x) with 1.
  change (readout (wrap pick_right a) x') with 1.
  destruct (e w 1) as [[p w'] |]; [f_equal; apply IH | reflexivity].
Qed.

Theorem pick_same_runs : forall X E (a : Agent TreeC X) (e : Env ListC E) x w n,
    run (wrap pick_left a) e x w n = run (wrap pick_right a) e x w n.
Proof. intros. apply pick_runs. Qed.

Theorem pick_differ : ~ cmorEq pick_left pick_right.
Proof.
  intros H. destruct (H (node leaf leaf)) as [_ Hf].
  assert (H1 : 0 < 1) by lia.
  specialize (Hf (exist _ 0 H1) (exist _ 0 H1) eq_refl). discriminate Hf.
Qed.
