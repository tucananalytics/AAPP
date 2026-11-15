(** * Worked examples: verified adapters for agents

    Part of the development accompanying "Arithmetic Analysis of Polymorphic
    Programs and the Verification of Typed Agent Interfaces" (Section 5).

    The adapters of the paper are turned into container morphisms on the list
    interface, and the arithmetic facts of [Examples] are transported, by the
    theorems of [Containers], to statements about container morphisms and
    about the behaviour of agents wrapped by them.  Every law below is proved
    by citing a [pcmEQ] fact that was itself discharged by the tactic
    [containers]; no proof in this file inspects a list or a tree.

    The file ends with concrete agents and environments whose runs are
    computed by the kernel, which shows that the behavioural statements are
    not vacuous and that adapters with different position maps are told
    apart by the behaviour they induce. *)

From Coq Require Import Arith Lia List PeanoNat.
From AAPP Require Import Examples Containers.
Import ListNotations.

(** ** The adapters as container morphisms *)

Definition window (k : nat) : CMor ListC ListC := to_cmor (Lastk_range k).
Definition firstk (k : nat) : CMor ListC ListC := to_cmor (Take_range k).
Definition dropk (k : nat) : CMor ListC ListC := to_cmor (Drop_range k).
Definition reverse : CMor ListC ListC := to_cmor Rev_range.
Definition rotate : CMor ListC ListC := to_cmor Rot_range.
Definition unrotate : CMor ListC ListC := to_cmor Unrot_range.

(** [adapter_law H] proves an equation between composites of such morphisms
    from the arithmetic fact [H] about the representing terms. *)
Ltac adapter_law H :=
  eapply represents_cmorEq;
  [ repeat first [ apply ccomp_represents | apply to_cmor_represents | apply cid_represents ]
  | repeat first [ apply ccomp_represents | apply to_cmor_represents | apply cid_represents ]
  | apply H ].

(** ** Laws, as equations between container morphisms *)

(** Truncating a history to its last [k] items is idempotent. *)
Theorem window_idem : forall k, cmorEq (ccomp (window k) (window k)) (window k).
Proof. intros k. adapter_law (lastk_idem k). Qed.

(** A [k]-window of a [(k+1)]-window is a [k]-window. *)
Theorem window_window : forall k, cmorEq (ccomp (window k) (window (S k))) (window k).
Proof. intros k. adapter_law (lastk_lastk k). Qed.

(** Reversal is an involution; rotation and unrotation are mutually inverse. *)
Theorem reverse_involutive : cmorEq (ccomp reverse reverse) (cid ListC).
Proof. adapter_law rev_rev. Qed.

Theorem rotate_unrotate : cmorEq (ccomp rotate unrotate) (cid ListC).
Proof. adapter_law rot_unrot. Qed.

Theorem unrotate_rotate : cmorEq (ccomp unrotate rotate) (cid ListC).
Proof. adapter_law unrot_rot. Qed.

(** Skipping composes additively. *)
Theorem dropk_dropk : forall n m, cmorEq (ccomp (dropk n) (dropk m)) (dropk (n + m)).
Proof. intros n m. adapter_law (drop_drop n m). Qed.

(** ** The same laws, as statements about behaviour *)

(** Wrapping twice by the window is observationally the same as wrapping
    once: the two agents produce the same run against every environment. *)
Corollary window_idem_run : forall k X E (a : Agent ListC X) (e : Env ListC E) x w n,
    run (wrap (window k) (wrap (window k) a)) e x w n = run (wrap (window k) a) e x w n.
Proof.
  intros k X E a e x w n.
  rewrite <- (run_ext (wrap (ccomp (window k) (window k)) a)
                      (wrap (window k) (wrap (window k) a))
                      (wrap_comp (window k) (window k) a)).
  apply cmorEq_run, window_idem.
Qed.

(** Reversing the batch twice leaves the behaviour of every agent unchanged. *)
Corollary reverse_involutive_run : forall X E (a : Agent ListC X) (e : Env ListC E) x w n,
    run (wrap reverse (wrap reverse a)) e x w n = run a e x w n.
Proof.
  intros X E a e x w n.
  rewrite <- (run_ext (wrap (ccomp reverse reverse) a) (wrap reverse (wrap reverse a))
                      (wrap_comp reverse reverse a)).
  rewrite (cmorEq_run reverse_involutive a e x w n).
  apply run_ext. intros y. apply wrap_id.
Qed.

(** The first law for a planner served through [flatten]: it is the same
    statement, instantiated at the flattened planner. *)
Corollary planner_window_idem : forall k X E (a : Agent TreeC X) (e : Env ListC E) x w n,
    run (wrap (window k) (wrap (window k) (flat_planner a))) e x w n
    = run (wrap (window k) (flat_planner a)) e x w n.
Proof. intros. apply window_idem_run. Qed.

(** ** Losslessness *)

(** The permutations are cartesian container morphisms ... *)
Theorem reverse_cartesian : cartesian reverse.
Proof. apply lossless_cartesian, Rev_lossless. Qed.

Theorem rotate_cartesian : cartesian rotate.
Proof. apply lossless_cartesian, Rot_lossless. Qed.

Theorem unrotate_cartesian : cartesian unrotate.
Proof. apply lossless_cartesian, Unrot_lossless. Qed.

(** ... and so is any pipeline assembled from them, including one that
    starts from a hierarchical plan: every result that the environment
    returns is routed to exactly one leaf of the plan, and every leaf
    receives one. *)
Theorem pipeline_cartesian : cartesian (ccomp rotate (ccomp reverse flatten)).
Proof.
  apply cartesian_comp; [apply cartesian_comp |].
  - apply flatten_cartesian.
  - apply reverse_cartesian.
  - apply rotate_cartesian.
Qed.

(** ** Ill-typed adapters are rejected before any law is considered

    The off-by-one window [BadLastk] sends the last slot of a full window
    outside the history, so it is not a container morphism at all. *)
Example badlastk_ill_typed : ~ in_range 1 (BadLastk 2).
Proof.
  intros H. specialize (H (fun _ => 2) 1). unfold_morphism.
  assert (Hlt : 1 < 2) by lia. specialize (H Hlt). lia.
Qed.

(** ** Computed runs

    A countdown agent: in state [x] it emits a batch of [x] items, and when
    the item at index [i] is answered it moves to state [i].  The environment
    (which needs no memory) always answers the last item of the batch it is
    shown, and declines the empty batch. *)
Definition countdown : Agent ListC nat :=
  fun x => existT (fun n => Fin n -> nat) x (fun p => proj1_sig p).

Definition last_slot : Env ListC unit :=
  fun _ n => match n with
             | 0 => None
             | S n' => Some (exist (fun i => i < S n') n' (Nat.lt_succ_diag_r n'), tt)
             end.

Example run_plain : run countdown last_slot 5 tt 10 = [5; 4; 3; 2; 1; 0].
Proof. reflexivity. Qed.

(** Through a window of size 3 the environment sees at most three items, and
    its answer to the last visible item is routed to the last item of the
    agent's batch ... *)
Example run_window : run (wrap (window 3) countdown) last_slot 5 tt 10 = [3; 3; 3; 2; 1; 0].
Proof. reflexivity. Qed.

(** ... whereas the adapter that keeps the *first* three items has the same
    shape map but routes the answer elsewhere, and the agent behaves
    differently.  Shape maps alone do not determine behaviour. *)
Example run_firstk : run (wrap (firstk 3) countdown) last_slot 5 tt 10 = [3; 2; 1; 0].
Proof. reflexivity. Qed.

Example run_reverse : run (wrap reverse countdown) last_slot 5 tt 10 = [5; 0].
Proof. reflexivity. Qed.

Example run_reverse_twice :
  run (wrap reverse (wrap reverse countdown)) last_slot 5 tt 10 = run countdown last_slot 5 tt 10.
Proof. reflexivity. Qed.

(** A planner on the tree interface: its state and its move are the current
    plan, and when the result for a leaf arrives it refines that leaf into
    two sub-tasks. *)
Fixpoint refine (s : TreeS) : TreeP s -> TreeS :=
  match s return TreeP s -> TreeS with
  | leaf => fun _ => node leaf leaf
  | node l r => fun p =>
      match p with
      | inl pl => node (refine l pl) r
      | inr pr => node l (refine r pr)
      end
  end.

Definition refiner : Agent TreeC TreeS :=
  fun s => existT (fun s => TreeP s -> TreeS) s (refine s).

(** Served through [flatten], the planner presents batches of 1, 2, 3, ...
    sub-tasks to an environment that knows nothing about trees; behind a
    window the environment never sees more than two. *)
Example run_refiner : run (flat_planner refiner) last_slot leaf tt 5 = [1; 2; 3; 4; 5].
Proof. reflexivity. Qed.

Example run_refiner_window :
  run (wrap (window 2) (flat_planner refiner)) last_slot leaf tt 5 = [1; 2; 2; 2; 2].
Proof. reflexivity. Qed.

(** The plan of the figure in the paper, ((x1, x2), x3), flattens to a batch
    of three; the batch slots are routed to its leaves from left to right,
    whatever their depth. *)
Example flatten_figure :
  let plan := node (node leaf leaf) leaf in
  u flatten plan = 3 /\
  forall (H0 : 0 < 3) (H1 : 1 < 3) (H2 : 2 < 3),
    f flatten plan (exist _ 0 H0) = inl (inl tt) /\
    f flatten plan (exist _ 1 H1) = inl (inr tt) /\
    f flatten plan (exist _ 2 H2) = inr tt.
Proof. repeat split. Qed.

(** ** Batches of items: a lifted adapter acts on contents

    Items of the interface [Turn] are numbers and admit a single response (an
    acknowledgement).  A conversation history is a move of the interface of
    batches of turns, [cComp ListC Turn], and the lifted window keeps its last
    turns, contents included. *)
Definition Turn : Container := mkCont (fun _ : nat => unit).

Definition history (l : list nat) : Shape (cComp ListC Turn) :=
  existT (fun n => Fin n -> nat) (length l) (fun i => nth (proj1_sig i) l 0).

Definition contents (s : Shape (cComp ListC Turn)) : list nat := to_list (ext_to_rep 0 s).

Example lifted_window :
  contents (u (whisker (window 2) Turn) (history [10; 20; 30; 40])) = [30; 40].
Proof. reflexivity. Qed.

Example lifted_reverse :
  contents (u (whisker reverse Turn) (history [10; 20; 30; 40])) = [40; 30; 20; 10].
Proof. reflexivity. Qed.
