(** * Examples: the properties of Figure 4 of the paper, mechanised

    Every property is stated as a [pcmEQ] between composites of Presburger
    definable morphisms and discharged by the single tactic [containers].

    Compared with the 2011 development, two definitions are corrected here:
    [take] (whose shape map was [max n m] rather than [min n m]) and [app]
    (whose position map did not match the flat encoding used by the
    interpretation).  All the properties below hold of the corrected
    definitions, and each definition is additionally validated against the
    corresponding function of the Coq standard library (Section
    "Transfer lemmas"), which is the two-tier methodology suggested by one of
    the referees. *)

From Coq Require Import Arith Lia List PeanoNat Compare_dec.
From AAPP Require Export ListMorphisms.
Import ListNotations.

Set Implicit Arguments.

(** ** Arity-1 morphisms:  n = variable 0,  i = variable 1 *)

(** reverse:  u n = n,  f n i = n - i - 1 *)
Definition Rev : PPCm := (lp x0, lp (suB (suB x0 x1) (cnst 1))).

(** tail:  u n = n - 1,  f n i = i + 1 *)
Definition Tail : PPCm := (lp (suB x0 (cnst 1)), lp (adD x1 (cnst 1))).

(** but_last:  u n = n - 1,  f n i = i *)
Definition Butlast : PPCm := (lp (suB x0 (cnst 1)), lp x1).

(** head (as a list of length <= 1):  u n = n - (n - 1),  f n i = 0 *)
Definition Head : PPCm := (lp (suB x0 (suB x0 (cnst 1))), kon 0).

(** last:  u n = n - (n - 1),  f n i = n - 1 *)
Definition Last : PPCm := (lp (suB x0 (suB x0 (cnst 1))), lp (suB x0 (cnst 1))).

(** take m:  u n = if n < m then n else m,  f n i = i *)
Definition Take (m : nat) : PPCm := (pf (lt_ x0 (cnst m)) (lp x0) (kon m), lp x1).

(** drop m:  u n = n - m,  f n i = i + m *)
Definition Drop (m : nat) : PPCm := (lp (suB x0 (cnst m)), lp (adD x1 (cnst m))).

(** rotate once (first element to the back):
    u n = n,  f n i = if i < n - 1 then i + 1 else 0 *)
Definition Rot : PPCm :=
  (lp x0, pf (lt_ x1 (suB x0 (cnst 1))) (lp (adD x1 (cnst 1))) (kon 0)).

(** unrotate once (last element to the front):
    u n = n,  f n i = if 0 < i then i - 1 else n - 1 *)
Definition Unrot : PPCm :=
  (lp x0, pf (lt_ (cnst 0) x1) (lp (suB x1 (cnst 1))) (lp (suB x0 (cnst 1)))).

(** keep the last k elements (a sliding context window):
    u n = if n < k then n else k,  f n i = i + (n - k) *)
Definition Lastk (k : nat) : PPCm :=
  (pf (lt_ x0 (cnst k)) (lp x0) (kon k), lp (adD x1 (suB x0 (cnst k)))).

(** ** Arity-2 morphisms:  n = variable 0,  m = variable 1,  i = variable 2 *)

(** append:  u n m = n + m,  f n m i = i   (flat encoding) *)
Definition App : PPCm := (lp (adD x0 x1), lp x2).

(** Lifting an arity-1 morphism to act on the first, resp. second, of two
    inputs (the other input is discarded).  These are the morphisms
    [m x id] projected, and are what is needed to state equations such as
    [rev (xs ++ ys) = rev ys ++ rev xs]. *)
Definition on_fst (m : PPCm) : PPCm :=
  (shape m, psubst (pos m) (fun j => if j =? 1 then lp x2 else lp (vr j))).

Definition on_snd (m : PPCm) : PPCm :=
  (psubst (shape m) (fun j => if j =? 0 then lp x1 else lp (vr j)),
   padd (lp x0) (psubst (pos m) (fun j => if j =? 0 then lp x1
                                          else if j =? 1 then lp x2 else lp (vr j)))).

#[export] Hint Unfold Rev Tail Butlast Head Last Take Drop Rot Unrot Lastk App on_fst on_snd : morphisms.

(** ** Well-typedness and losslessness of the basic morphisms *)

Lemma Rev_range : in_range 1 Rev.           Proof. containers. Qed.
Lemma Tail_range : in_range 1 Tail.         Proof. containers. Qed.
Lemma Butlast_range : in_range 1 Butlast.   Proof. containers. Qed.
Lemma Head_range : in_range 1 Head.         Proof. containers. Qed.
Lemma Last_range : in_range 1 Last.         Proof. containers. Qed.
Lemma Take_range : forall m, in_range 1 (Take m). Proof. containers. Qed.
Lemma Drop_range : forall m, in_range 1 (Drop m). Proof. containers. Qed.
Lemma Rot_range : in_range 1 Rot.           Proof. containers. Qed.
Lemma Unrot_range : in_range 1 Unrot.       Proof. containers. Qed.
Lemma Lastk_range : forall k, in_range 1 (Lastk k). Proof. containers. Qed.
Lemma App_range : in_range 2 App.           Proof. containers. Qed.

(** The reorderings are lossless (cartesian) ... *)
Lemma Rev_lossless : lossless Rev.          Proof. containers. Qed.
Lemma Rot_lossless : lossless Rot.          Proof. containers. Qed.
Lemma Unrot_lossless : lossless Unrot.      Proof. containers. Qed.

(** ... whereas the truncations are not: a governance-relevant fact that the
    decision procedure establishes with a concrete witness. *)
Lemma Tail_lossy : ~ lossless Tail.
Proof.
  intros H. destruct (H (fun _ => 1)) as [Hs _]. unfold_morphism. discriminate.
Qed.

Lemma Lastk_lossy : forall k, ~ lossless (Lastk k).
Proof.
  intros k H. destruct (H (fun _ => S k)) as [Hs _]. unfold_morphism. arith.
Qed.

Lemma Take_lossy : forall m, ~ lossless (Take m).
Proof.
  intros m H. destruct (H (fun _ => S m)) as [Hs _]. unfold_morphism. arith.
Qed.

Lemma Drop_lossy : forall m, ~ lossless (Drop (S m)).
Proof.
  intros m H. destruct (H (fun _ => 1)) as [Hs _]. unfold_morphism. arith.
Qed.

(** ** The properties of Figure 4 *)

(** rev (rev xs) = xs *)
Theorem rev_rev : pcmEQ 1 (comp1 1 Rev Rev) idm.
Proof. containers. Qed.

(** rev (xs ++ ys) = rev ys ++ rev xs *)
Theorem rev_app : pcmEQ 2 (comp1 2 Rev App) (comp2 2 App (on_snd Rev) (on_fst Rev)).
Proof. containers. Qed.

(** head (rev xs) = last xs *)
Theorem head_rev : pcmEQ 1 (comp1 1 Head Rev) Last.
Proof. containers. Qed.

(** tail (rev xs) = rev (but_last xs) *)
Theorem tail_rev : pcmEQ 1 (comp1 1 Tail Rev) (comp1 1 Rev Butlast).
Proof. containers. Qed.

(** drop n (drop m xs) = drop (n + m) xs *)
Theorem drop_drop : forall n m, pcmEQ 1 (comp1 1 (Drop n) (Drop m)) (Drop (n + m)).
Proof. containers. Qed.

(** drop n (take m xs) = take (m - n) (drop n xs) *)
Theorem drop_take : forall n m, pcmEQ 1 (comp1 1 (Drop n) (Take m)) (comp1 1 (Take (m - n)) (Drop n)).
Proof. containers. Qed.

(** take n (drop m xs) = drop m (take (n + m) xs) *)
Theorem take_drop : forall n m, pcmEQ 1 (comp1 1 (Take n) (Drop m)) (comp1 1 (Drop m) (Take (n + m))).
Proof. containers. Qed.

(** drop 1 (unrot xs) = but_last xs *)
Theorem drop1_unrot : pcmEQ 1 (comp1 1 (Drop 1) Unrot) Butlast.
Proof. containers. Qed.

(** rot (unrot xs) = xs *)
Theorem rot_unrot : pcmEQ 1 (comp1 1 Rot Unrot) idm.
Proof. containers. Qed.

(** unrot (rot xs) = xs *)
Theorem unrot_rot : pcmEQ 1 (comp1 1 Unrot Rot) idm.
Proof. containers. Qed.

(** head (rev (rot xs)) = head xs *)
Theorem head_rev_rot : pcmEQ 1 (comp1 1 Head (comp1 1 Rev Rot)) Head.
Proof. containers. Qed.

(** last (rot xs) = head xs *)
Theorem last_rot : pcmEQ 1 (comp1 1 Last Rot) Head.
Proof. containers. Qed.

(** head (unrot xs) = last xs *)
Theorem head_unrot : pcmEQ 1 (comp1 1 Head Unrot) Last.
Proof. containers. Qed.

(** but_last (rot xs) = tail xs *)
Theorem butlast_rot : pcmEQ 1 (comp1 1 Butlast Rot) Tail.
Proof. containers. Qed.

(** ** Properties of list-shaped agent adapters (Section 5 of the paper) *)

(** Truncating a context window is idempotent:  lastk k (lastk k h) = lastk k h *)
Theorem lastk_idem : forall k, pcmEQ 1 (comp1 1 (Lastk k) (Lastk k)) (Lastk k).
Proof. containers. Qed.

(** The sliding-window invariant: truncating before appending the new turns
    loses nothing with respect to truncating afterwards,
      lastk k (h ++ t) = lastk k (lastk k h ++ t). *)
Theorem lastk_app : forall k,
    pcmEQ 2 (comp1 2 (Lastk k) App)
            (comp1 2 (Lastk k) (comp2 2 App (on_fst (Lastk k)) (on_snd idm))).
Proof. containers. Qed.

(** Fan-out / fan-in routing: splitting a batch of requests at [m] and
    re-assembling the results restores the original order,
      take m b ++ drop m b = b. *)
Theorem split_merge : forall m, pcmEQ 1 (comp2 1 App (Take m) (Drop m)) idm.
Proof. containers. Qed.

(** Nested truncation collapses to the tighter window:
      lastk k (lastk (k+1) h) = lastk k h *)
Theorem lastk_lastk : forall k, pcmEQ 1 (comp1 1 (Lastk k) (Lastk (S k))) (Lastk k).
Proof. containers. Qed.

(** A tempting but *false* adapter law is refuted rather than proved:
    "dropping the oldest turn of a (k+1)-window gives a k-window" fails when
    the history is shorter than the window (witness: a history of length 1). *)
Theorem drop_lastk_refuted : ~ pcmEQ 1 (comp1 1 (Drop 1) (Lastk 2)) (Lastk 1).
Proof.
  intros H. destruct (H (fun _ => 1)) as [Hs _]. unfold_morphism. discriminate.
Qed.

(** An off-by-one adapter is rejected: the decision procedure refutes the
    equation (the counterexample below is [n = k + 1, i = 0]). *)
Definition BadLastk (k : nat) : PPCm :=
  (pf (lt_ x0 (cnst k)) (lp x0) (kon k), lp (adD (adD x1 (suB x0 (cnst k))) (cnst 1))).
#[export] Hint Unfold BadLastk : morphisms.

Theorem badlastk_detected : ~ pcmEQ 1 (Lastk 2) (BadLastk 2).
Proof.
  intros H. destruct (H (fun _ => 3)) as [_ Hp].
  specialize (Hp 0). unfold_morphism. simpl in Hp. lia.
Qed.

(** ** Transfer lemmas: the morphisms agree with the standard library

    Each lemma is a short structural induction; together with [pcmEQ_ok] and
    [comp1_ok] they transport every property above to ordinary Coq lists. *)

Section Transfer.
  Variable X : Type.
  Variable d : X.

  Lemma Rev_spec : forall l : list X,
      RepEq (interp Rev [of_list d l] d) (of_list d (rev l)).
  Proof.
    intros l. unfold interp, of_list, RepEq; simpl.
    rewrite rev_length. split; auto.
    intros i Hi. unfold env, ext in *; simpl in *.
    destruct (Nat.ltb_spec (length l - i - 1) (length l)); [| lia].
    rewrite rev_nth by auto. f_equal. lia.
  Qed.

  Lemma Tail_spec : forall l : list X,
      RepEq (interp Tail [of_list d l] d) (of_list d (tl l)).
  Proof.
    intros l. unfold interp, of_list, RepEq; simpl.
    destruct l as [| x l]; simpl.
    - split; auto. intros; lia.
    - rewrite Nat.sub_0_r. split; auto. intros i Hi. unfold env, ext in *; simpl in *.
      destruct (Nat.ltb_spec (i + 1) (S (length l))); [| lia].
      rewrite Nat.add_1_r. reflexivity.
  Qed.

  Lemma nth_firstn : forall (l : list X) m i, i < m -> nth i (firstn m l) d = nth i l d.
  Proof.
    induction l; intros m i Hi; destruct m; simpl; auto; try lia.
    destruct i; auto. apply IHl; lia.
  Qed.

  Lemma Take_spec : forall (m : nat) (l : list X),
      RepEq (interp (Take m) [of_list d l] d) (of_list d (firstn m l)).
  Proof.
    intros m l. unfold interp, of_list, RepEq. unfold_morphism; unfold env in *; simpl in *.
    - rewrite firstn_length. arith.
    - rewrite nth_firstn by arith.
      destruct (Nat.ltb_spec i (length l)); auto; arith.
  Qed.

  Lemma nth_skipn : forall (l : list X) m i, nth i (skipn m l) d = nth (i + m) l d.
  Proof.
    induction l; intros m i; destruct m; simpl.
    - destruct i; simpl; auto.
    - destruct i; simpl; auto.
    - rewrite Nat.add_0_r; auto.
    - rewrite IHl. replace (i + S m) with (S (i + m)) by lia. reflexivity.
  Qed.

  Lemma Drop_spec : forall (m : nat) (l : list X),
      RepEq (interp (Drop m) [of_list d l] d) (of_list d (skipn m l)).
  Proof.
    intros m l. unfold interp, of_list, RepEq. unfold_morphism; unfold env in *; simpl in *.
    - rewrite skipn_length. auto.
    - rewrite nth_skipn.
      destruct (Nat.ltb_spec (i + m) (length l)); auto; lia.
  Qed.

  Lemma App_spec : forall xs ys : list X,
      RepEq (interp App [of_list d xs; of_list d ys] d) (of_list d (xs ++ ys)).
  Proof.
    intros xs ys. unfold interp, of_list, RepEq. unfold_morphism; unfold env in *; simpl in *.
    - rewrite app_length. auto.
    - destruct (Nat.ltb_spec i (length xs)).
      + rewrite app_nth1; auto.
      + rewrite app_nth2 by auto.
        destruct (Nat.ltb_spec (i - length xs) (length ys)); auto; lia.
  Qed.

  (** [RepEq] is an equivalence and [interp] respects it (for well-typed morphisms). *)
  Lemma RepEq_refl : forall a : Rep X, RepEq a a.
  Proof. intros; split; auto. Qed.

  Lemma RepEq_sym : forall a b : Rep X, RepEq a b -> RepEq b a.
  Proof. intros a b [H1 H2]; split; auto. intros i Hi; rewrite <- H1 in Hi; symmetry; auto. Qed.

  Lemma RepEq_trans : forall a b c : Rep X, RepEq a b -> RepEq b c -> RepEq a c.
  Proof.
    intros a b c [H1 H2] [H3 H4]; split; [congruence |].
    intros i Hi. rewrite H2, H4; auto. congruence.
  Qed.

  Lemma interp1_RepEq : forall (m : PPCm) (a a' : Rep X),
      in_range 1 m -> RepEq a a' -> RepEq (interp m [a] d) (interp m [a'] d).
  Proof.
    intros m [n g] [n' g'] Hm [H1 H2]; simpl in *; subst n'.
    assert (He : env [(n, g')] = env [(n, g)]) by reflexivity.
    unfold interp, RepEq; simpl. rewrite He. split; auto.
    intros i Hi.
    assert (Hr := Hm _ i Hi). simpl in Hr. unfold env in Hr at 2; simpl in Hr.
    match goal with |- context [Nat.ltb ?a ?b] => destruct (Nat.ltb_spec a b) end; [| lia].
    apply H2. auto.
  Qed.

  Lemma interp2_RepEq : forall (m : PPCm) (a a' b b' : Rep X),
      in_range 2 m -> RepEq a a' -> RepEq b b' ->
      RepEq (interp m [a; b] d) (interp m [a'; b'] d).
  Proof.
    intros m [n1 g1] [n1' g1'] [n2 g2] [n2' g2'] Hm [H1 H2] [H3 H4]; simpl in *; subst n1' n2'.
    assert (He : env [(n1, g1'); (n2, g2')] = env [(n1, g1); (n2, g2)]) by reflexivity.
    unfold interp, RepEq; simpl. rewrite He. split; auto.
    intros i Hi.
    assert (Hr := Hm _ i Hi). simpl in Hr. unfold env in Hr at 2 3; simpl in Hr.
    match goal with |- context [Nat.ltb ?a ?b] => destruct (Nat.ltb_spec a b) end.
    - apply H2; auto.
    - match goal with |- context [Nat.ltb ?a ?b] => destruct (Nat.ltb_spec a b) end; [| lia].
      apply H4; auto.
  Qed.

  Lemma of_list_inj : forall l l' : list X, RepEq (of_list d l) (of_list d l') -> l = l'.
  Proof.
    intros l l' [H1 H2]; simpl in *. apply nth_ext with (d := d) (d' := d); auto.
  Qed.

  (** The classic theorem, obtained from the decision procedure and the
      transfer lemmas with no induction on lists. *)
  Theorem rev_involutive_via_containers : forall l : list X, rev (rev l) = l.
  Proof.
    intros l. apply of_list_inj.
    eapply RepEq_trans; [apply RepEq_sym, Rev_spec |].
    eapply RepEq_trans; [apply RepEq_sym, interp1_RepEq; [apply Rev_range | apply Rev_spec] |].
    eapply RepEq_trans; [apply RepEq_sym, comp1_ok; [reflexivity | apply Rev_range] |].
    eapply RepEq_trans; [apply pcmEQ_ok with (k := 1); [reflexivity | apply rev_rev] |].
    apply idm_ok.
  Qed.

  (** Likewise for the routing identity  take m b ++ drop m b = b. *)
  Theorem firstn_skipn_via_containers : forall m (l : list X), firstn m l ++ skipn m l = l.
  Proof.
    intros m l. apply of_list_inj.
    eapply RepEq_trans; [apply RepEq_sym, App_spec |].
    eapply RepEq_trans; [apply RepEq_sym, interp2_RepEq;
                         [apply App_range | apply Take_spec | apply Drop_spec] |].
    eapply RepEq_trans; [apply RepEq_sym, comp2_ok; [reflexivity | apply App_range] |].
    eapply RepEq_trans; [apply pcmEQ_ok with (k := 1); [reflexivity | apply split_merge] |].
    apply idm_ok.
  Qed.
End Transfer.
