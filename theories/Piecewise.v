(** * Piecewise-linear arithmetic terms

    Accompanies: R. Prince, "Arithmetic Analysis of Polymorphic Programs and
    Typed Agent Interfaces" (revised submission to Fundamenta Informaticae).

    This file gives a small syntax for Presburger-definable functions
    [nat^k -> nat]: linear terms built from variables, constants, addition and
    cut-off subtraction, together with a conditional ("piecewise") layer.  The
    syntax is deliberately non-dependent: variables are natural-number indices
    into an environment [rho : nat -> nat].  Every function expressible here is
    definable in Presburger arithmetic (Lemma [presburger_definable] below gives
    the graph as a quantifier-free formula), which is why the [lia] decision
    procedure can discharge equalities between them.

    Compared with the 2011 development (file [DecidableFunctions.v] in the
    [legacy/] directory) the representation is simpler (no [Fin]-indexed
    variables, no vectors) and the proofs are shorter; the mathematical content
    is the same. *)

From Coq Require Import Arith Lia Bool PeanoNat Compare_dec.

Set Implicit Arguments.

(** ** Linear terms *)

Inductive lfun : Set :=
| cnst : nat -> lfun            (** constant *)
| vr   : nat -> lfun            (** variable [vr j] reads [rho j] *)
| adD  : lfun -> lfun -> lfun   (** addition *)
| suB  : lfun -> lfun -> lfun.  (** cut-off subtraction, [a - b = 0] when [a <= b] *)

Fixpoint evl (e : lfun) (rho : nat -> nat) : nat :=
  match e with
  | cnst n  => n
  | vr j    => rho j
  | adD a b => evl a rho + evl b rho
  | suB a b => evl a rho - evl b rho
  end.

(** ** Piecewise terms

    [pf c l r] denotes [if 0 < c then l else r].  Since [c] may itself be a
    cut-off subtraction [a - b], this encodes the test [b < a]; together with
    nesting it gives arbitrary finite case analyses on linear inequalities. *)

Inductive Plfun : Set :=
| lp : lfun -> Plfun
| pf : Plfun -> Plfun -> Plfun -> Plfun.

Fixpoint pevl (p : Plfun) (rho : nat -> nat) : nat :=
  match p with
  | lp a     => evl a rho
  | pf c l r => if le_lt_dec (pevl c rho) 0 then pevl r rho else pevl l rho
  end.

(** Smart constructors used in the examples.  A condition [a < b] is written as
    the cut-off subtraction [b - a], which is positive exactly when [a < b]. *)
Definition kon (n : nat) : Plfun := lp (cnst n).
Definition x0 : lfun := vr 0.
Definition x1 : lfun := vr 1.
Definition x2 : lfun := vr 2.
Definition lt_ (a b : lfun) : Plfun := lp (suB b a).   (* "a < b" as a condition *)

(** ** Pointwise operations on piecewise terms

    To substitute piecewise terms for variables inside linear terms we need
    addition and subtraction of piecewise terms.  Conditionals are pushed
    outwards: [(if c then l else r) + q = if c then l + q else r + q]. *)

Fixpoint padd_l (a : lfun) (q : Plfun) : Plfun :=
  match q with
  | lp b     => lp (adD a b)
  | pf c l r => pf c (padd_l a l) (padd_l a r)
  end.

Fixpoint padd (p q : Plfun) : Plfun :=
  match p with
  | lp a     => padd_l a q
  | pf c l r => pf c (padd l q) (padd r q)
  end.

Fixpoint psub_l (a : lfun) (q : Plfun) : Plfun :=
  match q with
  | lp b     => lp (suB a b)
  | pf c l r => pf c (psub_l a l) (psub_l a r)
  end.

Fixpoint psub (p q : Plfun) : Plfun :=
  match p with
  | lp a     => psub_l a q
  | pf c l r => pf c (psub l q) (psub r q)
  end.

Lemma padd_l_ok : forall a q rho, pevl (padd_l a q) rho = evl a rho + pevl q rho.
Proof.
  induction q; intros; simpl; auto.
  destruct (le_lt_dec (pevl q1 rho) 0); auto.
Qed.

Lemma psub_l_ok : forall a q rho, pevl (psub_l a q) rho = evl a rho - pevl q rho.
Proof.
  induction q; intros; simpl; auto.
  destruct (le_lt_dec (pevl q1 rho) 0); auto.
Qed.

Lemma padd_ok : forall p q rho, pevl (padd p q) rho = pevl p rho + pevl q rho.
Proof.
  induction p; intros; simpl; [apply padd_l_ok |].
  destruct (le_lt_dec (pevl p1 rho) 0); auto.
Qed.

Lemma psub_ok : forall p q rho, pevl (psub p q) rho = pevl p rho - pevl q rho.
Proof.
  induction p; intros; simpl; [apply psub_l_ok |].
  destruct (le_lt_dec (pevl p1 rho) 0); auto.
Qed.

(** ** Substitution

    [lsubst e sigma] replaces each variable [j] of the linear term [e] by the
    piecewise term [sigma j]; [psubst] extends this to piecewise terms.  This is
    the only operation needed to define composition of morphisms. *)

Fixpoint lsubst (e : lfun) (sigma : nat -> Plfun) : Plfun :=
  match e with
  | cnst n  => lp (cnst n)
  | vr j    => sigma j
  | adD a b => padd (lsubst a sigma) (lsubst b sigma)
  | suB a b => psub (lsubst a sigma) (lsubst b sigma)
  end.

Fixpoint psubst (p : Plfun) (sigma : nat -> Plfun) : Plfun :=
  match p with
  | lp a     => lsubst a sigma
  | pf c l r => pf (psubst c sigma) (psubst l sigma) (psubst r sigma)
  end.

Lemma lsubst_ok : forall e sigma rho,
    pevl (lsubst e sigma) rho = evl e (fun j => pevl (sigma j) rho).
Proof.
  induction e; intros; simpl; auto.
  - rewrite padd_ok, IHe1, IHe2; auto.
  - rewrite psub_ok, IHe1, IHe2; auto.
Qed.

Lemma psubst_ok : forall p sigma rho,
    pevl (psubst p sigma) rho = pevl p (fun j => pevl (sigma j) rho).
Proof.
  induction p; intros; simpl.
  - apply lsubst_ok.
  - rewrite IHp1, IHp2, IHp3. reflexivity.
Qed.

(** ** Presburger definability

    The graph of every piecewise term is definable by a quantifier-free formula
    of Presburger arithmetic.  We make this explicit, since it is the formal
    reason why [lia] (a decision procedure for quantifier-free linear integer
    arithmetic) suffices for all the equalities proved in this development.
    Formulas are represented as Coq propositions built from [=], [<=], [/\],
    [\/]; the lemma states that evaluation is characterised by such a formula. *)

Lemma suB_graph : forall a b r : nat, r = a - b <-> (b <= a /\ r + b = a) \/ (a < b /\ r = 0).
Proof. intros; lia. Qed.

Lemma pf_graph : forall (c l r x : nat),
    (if le_lt_dec c 0 then r else l) = x <-> (0 < c /\ x = l) \/ (c = 0 /\ x = r).
Proof. intros; destruct (le_lt_dec c 0); lia. Qed.

(** ** Tactic support

    [case_dec] eliminates every [le_lt_dec] (from [pevl]) and
    [Nat.ltb] / [Nat.eqb] (from the interpretations in [ListMorphisms]) that
    occurs in the goal or hypotheses, leaving pure arithmetic for [lia]. *)

Ltac case_dec :=
  match goal with
  | [ |- context [le_lt_dec ?x ?y] ] => destruct (le_lt_dec x y)
  | [ H : context [le_lt_dec ?x ?y] |- _ ] => destruct (le_lt_dec x y)
  | [ |- context [Nat.ltb ?x ?y] ] =>
      let E := fresh "E" in destruct (Nat.ltb x y) eqn:E;
      [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E]
  | [ H : context [Nat.ltb ?x ?y] |- _ ] =>
      let E := fresh "E" in destruct (Nat.ltb x y) eqn:E;
      [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E]
  | [ |- context [Nat.eqb ?x ?y] ] =>
      let E := fresh "E" in destruct (Nat.eqb x y) eqn:E;
      [apply Nat.eqb_eq in E | apply Nat.eqb_neq in E]
  | [ H : context [Nat.eqb ?x ?y] |- _ ] =>
      let E := fresh "E" in destruct (Nat.eqb x y) eqn:E;
      [apply Nat.eqb_eq in E | apply Nat.eqb_neq in E]
  end.

Ltac arith := repeat case_dec; lia.
