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
Definition pinned (k : nat) : CMor ListC ListC := to_cmor (Pin_range k).
Definition firstk (k : nat) : CMor ListC ListC := to_cmor (Take_range k).
Definition dropk (k : nat) : CMor ListC ListC := to_cmor (Drop_range k).
Definition first : CMor ListC ListC := to_cmor Head_range.
Definition reverse : CMor ListC ListC := to_cmor Rev_range.
Definition rotate : CMor ListC ListC := to_cmor Rot_range.
Definition unrotate : CMor ListC ListC := to_cmor Unrot_range.

(** Appending two lists, as a morphism out of the product. *)
Definition append : CMor List2C ListC := to_cmor2 App_range.

(** The projections of the product are represented by [Fst] and [Snd]. *)
Lemma cfst_represents : represents src2 Fst (cfst ListC ListC).
Proof. intros [n1 n2]; split; [reflexivity | intros p; reflexivity]. Qed.

Lemma csnd_represents : represents src2 Snd (csnd ListC ListC).
Proof. intros [n1 n2]; split; [reflexivity | intros p; reflexivity]. Qed.

(** [adapter_law S H] proves an equation between composites of such
    morphisms, out of the source [S] (one list or two), from the arithmetic
    fact [H] about the representing terms. *)
Ltac represent :=
  repeat first [ apply comp1_represents | apply comp2_represents
               | apply to_cmor_represents | apply to_cmor2_represents
               | apply cid_represents | apply cfst_represents | apply csnd_represents ].

Ltac adapter_law S H :=
  eapply (@represents_cmorEq S); [ represent | represent | apply pcmEQ_pcmEQ_on, H ].

(** ** Laws of one list, as equations between container morphisms *)

(** Truncating a history to its last [k] items is idempotent. *)
Theorem window_idem : forall k, cmorEq (ccomp (window k) (window k)) (window k).
Proof. intros k. adapter_law src1 (lastk_idem k). Qed.

(** A [k]-window of a [(k+1)]-window is a [k]-window. *)
Theorem window_window : forall k, cmorEq (ccomp (window k) (window (S k))) (window k).
Proof. intros k. adapter_law src1 (lastk_lastk k). Qed.

(** The same for the window that pins the first turn, which moreover never
    loses that turn. *)
Theorem pinned_idem : forall k, cmorEq (ccomp (pinned k) (pinned k)) (pinned k).
Proof. intros k. adapter_law src1 (pin_idem k). Qed.

Theorem pinned_pinned : forall k, cmorEq (ccomp (pinned k) (pinned (S k))) (pinned k).
Proof. intros k. adapter_law src1 (pin_pin k). Qed.

Theorem first_pinned : forall k, cmorEq (ccomp first (pinned k)) first.
Proof. intros k. adapter_law src1 (head_pin k). Qed.

(** Reversal is an involution; rotation and unrotation are mutually inverse. *)
Theorem reverse_involutive : cmorEq (ccomp reverse reverse) (cid ListC).
Proof. adapter_law src1 rev_rev. Qed.

Theorem rotate_unrotate : cmorEq (ccomp rotate unrotate) (cid ListC).
Proof. adapter_law src1 rot_unrot. Qed.

Theorem unrotate_rotate : cmorEq (ccomp unrotate rotate) (cid ListC).
Proof. adapter_law src1 unrot_rot. Qed.

(** Skipping composes additively. *)
Theorem dropk_dropk : forall n m, cmorEq (ccomp (dropk n) (dropk m)) (dropk (n + m)).
Proof. intros n m. adapter_law src1 (drop_drop n m). Qed.

(** Fan-out and fan-in: splitting a batch in two, or in three, and
    re-assembling the parts is the identity adapter. *)
Theorem split_merge_cmor : forall m,
    cmorEq (ccomp append (cpair (firstk m) (dropk m))) (cid ListC).
Proof. intros m. adapter_law src1 (split_merge m). Qed.

Theorem split3_merge_cmor : forall a c,
    cmorEq (ccomp append
                  (cpair (firstk a)
                         (ccomp append (cpair (ccomp (firstk c) (dropk a)) (dropk (a + c))))))
           (cid ListC).
Proof. intros a c. adapter_law src1 (split3_merge a c). Qed.

(** ** Laws of two lists *)

(** The sliding-window invariant: appending and then truncating is the same
    as truncating, appending and truncating again.  Both sides are morphisms
    from a pair of lists (the history and the new turns) to a list. *)
Theorem window_append : forall k,
    cmorEq (ccomp (window k) append)
           (ccomp (window k)
                  (ccomp append (cpair (ccomp (window k) (cfst ListC ListC))
                                       (ccomp (cid ListC) (csnd ListC ListC))))).
Proof. intros k. adapter_law src2 (lastk_app k). Qed.

(** The same invariant for the window that pins the first turn. *)
Theorem pinned_append : forall k,
    cmorEq (ccomp (pinned k) append)
           (ccomp (pinned k)
                  (ccomp append (cpair (ccomp (pinned k) (cfst ListC ListC))
                                       (ccomp (cid ListC) (csnd ListC ListC))))).
Proof. intros k. adapter_law src2 (pin_app k). Qed.

(** Reversal distributes over appending, with the arguments exchanged. *)
Theorem reverse_append :
  cmorEq (ccomp reverse append)
         (ccomp append (cpair (ccomp reverse (csnd ListC ListC))
                              (ccomp reverse (cfst ListC ListC)))).
Proof. adapter_law src2 rev_app. Qed.

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

(** An agent whose interface is a pair of lists -- a history and the new
    turns -- behaves in the same way whichever implementation of the sliding
    window it is wrapped by. *)
Corollary window_append_run : forall k X E (a : Agent List2C X) (e : Env ListC E) x w n,
    run (wrap (ccomp (window k) append) a) e x w n
    = run (wrap (ccomp (window k)
                       (ccomp append (cpair (ccomp (window k) (cfst ListC ListC))
                                            (ccomp (cid ListC) (csnd ListC ListC))))) a)
          e x w n.
Proof. intros k X E a e x w n. apply cmorEq_run, window_append. Qed.

(** The first law for a planner served through [flatten]: it is the same
    statement, instantiated at the flattened planner. *)
Corollary planner_window_idem : forall k X E (a : Agent TreeC X) (e : Env ListC E) x w n,
    run (wrap (window k) (wrap (window k) (flat_planner a))) e x w n
    = run (wrap (window k) (flat_planner a)) e x w n.
Proof. intros. apply window_idem_run. Qed.

(** ** Adapters that are not equal

    A counterexample found by the search is an inequality of container
    morphisms and, by observational completeness, of behaviour: it is not
    the case that every agent behaves in the same way under the two
    adapters. *)

(** The window and the truncation to the first [k] items have the same shape
    map and are different adapters; so are the window and the pinned window. *)
Theorem window_ne_firstk : ~ cmorEq (window 3) (firstk 3).
Proof.
  apply (@find_cex_cmor (Lastk 3) (Take 3) _ _ 6 (PosCex 4 0));
    [apply to_cmor_represents | apply to_cmor_represents | vm_compute; reflexivity].
Qed.

Theorem window_ne_pinned : ~ cmorEq (window 3) (pinned 2).
Proof.
  apply (@find_cex_cmor (Lastk 3) (Pin 2) _ _ 6 (PosCex 4 0));
    [apply to_cmor_represents | apply to_cmor_represents | exact pin_lastk_cex].
Qed.

(** The tempting optimisation "drop the oldest turn of a wider window" is
    observably wrong: some agent, against some environment, behaves
    differently under it. *)
Theorem drop_window_observable :
  ~ (forall X E (a : Agent ListC X) (e : Env ListC E) x w n,
        run (wrap (ccomp (dropk 1) (window 2)) a) e x w n = run (wrap (window 1) a) e x w n).
Proof.
  intros H. apply list_adapters_iff_runs in H. revert H.
  apply (@find_cex_cmor (comp1 1 (Drop 1) (Lastk 2)) (Lastk 1) _ _ 4 (ShapeCex 1));
    [represent | represent | exact drop_lastk_cex].
Qed.

(** Conversely, for closed terms the arithmetic statement is equivalent to
    observational equivalence, so the tactic [containers] decides the latter.
    The instance for the idempotence of reversal: *)
Example rev_rev_exact :
  pcmEQ 1 (comp1 1 Rev Rev) idm <-> cmorEq (ccomp reverse reverse) (cid ListC).
Proof.
  apply (@pcmEQ_iff_cmorEq src1); [represent | represent | reflexivity | reflexivity].
Qed.

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

(** An environment that always answers the first item tells the plain window
    from the pinned one: the pinned window routes the answer to the first
    item of the agent's batch, the plain window to the oldest item that is
    still visible. *)
Definition first_slot : Env ListC unit :=
  fun _ n => match n with
             | 0 => None
             | S n' => Some (exist (fun i => i < S n') 0 (Nat.lt_0_succ n'), tt)
             end.

Example run_window_first : run (wrap (window 3) countdown) first_slot 5 tt 10 = [3; 2; 0].
Proof. reflexivity. Qed.

Example run_pinned_first : run (wrap (pinned 2) countdown) first_slot 5 tt 10 = [3; 0].
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

Example lifted_pinned :
  contents (u (whisker (pinned 2) Turn) (history [10; 20; 30; 40; 50])) = [10; 40; 50].
Proof. reflexivity. Qed.

Example lifted_reverse :
  contents (u (whisker reverse Turn) (history [10; 20; 30; 40])) = [40; 30; 20; 10].
Proof. reflexivity. Qed.

(** ** Typed tool calls

    The item interface of tool calls: a request asks either for a number or
    for a truth value, and the type of the result depends on the request.
    An agent holds a list of pending requests, emits them as a batch, and
    when the result of one of them arrives -- a slot together with a result
    of the type which the request in that slot demands -- removes that
    request from its list. *)
Inductive req : Set := AskNat | AskBool.

Definition res (r : req) : Set :=
  match r with
  | AskNat => nat
  | AskBool => bool
  end.

Definition Tool : Container := mkCont res.

Fixpoint remove_nth (i : nat) (l : list req) : list req :=
  match l, i with
  | [], _ => []
  | _ :: l', 0 => l'
  | x :: l', S i' => x :: remove_nth i' l'
  end.

Definition batch (l : list req) : Shape (cComp ListC Tool) :=
  existT (fun n => Fin n -> req) (length l) (fun i => nth (proj1_sig i) l AskNat).

Definition caller : Agent (cComp ListC Tool) (list req) :=
  fun l => existT (fun s => Pos (cComp ListC Tool) s -> list req)
                  (batch l)
                  (fun answer => remove_nth (proj1_sig (projT1 answer)) l).

(** An environment that executes the first call of whatever batch it is
    shown.  Its answer must have the type demanded by that call. *)
Definition execute (r : req) : res r :=
  match r with
  | AskNat => 42
  | AskBool => true
  end.

Definition slot0 (n : nat) : Fin (S n) := exist (fun i => i < S n) 0 (Nat.lt_0_succ n).

Definition first_call : Env (cComp ListC Tool) unit :=
  fun _ s =>
    match s as s0 return option (Pos (cComp ListC Tool) s0 * unit) with
    | existT _ n k =>
        match n as n0
              return forall k0 : Fin n0 -> req,
                       option (Pos (cComp ListC Tool) (existT (fun n => Fin n -> req) n0 k0) * unit)
        with
        | 0 => fun _ => None
        | S n' => fun k0 =>
            Some (existT (fun p => res (k0 p)) (slot0 n') (execute (k0 (slot0 n'))), tt)
        end k
    end.

(** The requests of a batch, as a list. *)
Definition calls (s : Shape (cComp ListC Tool)) : list req := to_list (ext_to_rep AskNat s).

Example run_caller :
  map calls (run caller first_call [AskNat; AskBool; AskNat] tt 5)
  = [[AskNat; AskBool; AskNat]; [AskBool; AskNat]; [AskNat]; []].
Proof. reflexivity. Qed.

(** Behind the lifted window the environment sees the last two requests.  It
    answers the first of them, a request for a truth value, with a truth
    value; the lifted adapter routes that answer to the second request of the
    agent's list, where its type is the right one, and the agent removes that
    request. *)
Example run_caller_window :
  map calls (run (wrap (whisker (window 2) Tool) caller) first_call
                 [AskNat; AskBool; AskNat] tt 5)
  = [[AskBool; AskNat]; [AskNat; AskNat]; [AskNat]; []].
Proof. reflexivity. Qed.
