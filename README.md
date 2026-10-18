# Arithmetic Analysis of Polymorphic Programs — accompanying development (2026 revision)

Accompanying code for

> R. Prince, *Arithmetic Analysis of Polymorphic Programs and Typed Agent Interfaces*,
> revised submission to Fundamenta Informaticae (original submission 2011, ref. 2014-3-Prince).

The development is a complete rewrite of the 2011 Coq code for modern Coq/Rocq.
It is self-contained (no dependence on the old finite-type libraries), axiom-free,
and every theorem of Figure 4 of the paper is discharged by a single tactic in
a fraction of a second.

## Requirements

* Coq 8.18 or later, or the Rocq Prover 9.x (uses only the standard library:
  `Arith`, `Lia`, `List`).
* `make` (uses `coq_makefile`).

```
make            # builds theories/*.v
```

Tested with Coq 8.18.0.

## Contents

| File | Content | Paper |
|------|---------|-------|
| `theories/Piecewise.v` | Linear terms `lfun`, piecewise terms `Plfun`, evaluation, substitution; Presburger-definability of their graphs; the `arith` tactic (`lia` after case analysis). | §4.2–4.3 |
| `theories/ListMorphisms.v` | Non-dependent list morphisms `PPCm` (shape map + position map), flat-index interpretation `interp`, the equality `pcmEQ` (eq. 16), its soundness `pcmEQ_ok`, well-typedness `in_range`, losslessness `lossless`, composition `comp1`/`comp2` with correctness proofs `comp1_ok`/`comp2_ok`, and the decision tactic `containers`. | §4.3–4.5 |
| `theories/Examples.v` | All fourteen properties of Figure 4; the agent-adapter properties of §5 (`lastk_idem`, `lastk_app`, `split_merge`, `lastk_lastk`); refutations of two false laws (`badlastk_detected`, `drop_lastk_refuted`); losslessness results; **transfer lemmas** relating every morphism to the Coq standard library (`Rev_spec`, `Tail_spec`, `Take_spec`, `Drop_spec`, `App_spec`) and two end-to-end theorems about ordinary lists obtained without induction (`rev_involutive_via_containers`, `firstn_skipn_via_containers`). | §4.6, §5 |
| `theories/Containers.v` | Containers, extensions, container morphisms (dependent lenses), `mmap`, composition and functoriality; agents as coalgebras, `wrap`, `run`, behavioural consequence of adapter equality; the list container and the bridge `to_cmor` / `to_cmor_interp` / `pcmEQ_wrap` to the arithmetic representation. | §2, §3, §5.1 |
| `legacy/` | The original 2011 sources (Coq 8.1), kept for reference. They do not compile with current Coq. | — |

## Changes with respect to the 2011 development

* `omega` (deprecated in Coq 8.12, removed in 8.14) is replaced by `lia`.
  The `optimiseOmega` pre-processing of the 2011 tactic is no longer needed.
  Typical proof times are 10–450 ms (Figure 4 lemmas: ≤ 40 ms each except
  `rev_app` at 0.18 s; `lastk_app` 0.43 s) on a 2.1 GHz Xeon — compared with
  6 s (thesis, 2010) and 75 s (referee report, 2014) for the 2011 code.
* Variables of linear terms are plain `nat` indices into an environment rather
  than `Fin n`-indexed; morphisms are first-order pairs of terms with the
  arity supplied to the equality and interpretation.  This removes all
  dependent pattern matching from the arithmetic core.
* Two definitions of the 2011 code were incorrect and are corrected here:
  `take1` had shape map `max n m` instead of `min n m`, and `appn1`'s position
  map did not follow the flat-index encoding used by the interpretation.
  All properties are re-proved for the corrected definitions, and each
  definition is validated against the corresponding standard-library
  function by a transfer lemma.
* Composition of an arity-2 morphism with two morphisms on the *same*
  inputs (`comp2`) is new; it is what allows `rev (xs ++ ys) = rev ys ++ rev xs`
  and the sliding-window invariant to be stated.
* Correctness of composition (`comp1_ok`, `comp2_ok`) is proved, under the
  well-typedness side condition `in_range`, which is itself decided by the
  same tactic.
* The container-theoretic layer (`Containers.v`) and the agent reading are new.

## Checking axiom-freedom

```
echo 'From AAPP Require Import Containers Examples.
Print Assumptions rev_involutive_via_containers.
Print Assumptions pcmEQ_wrap.' | coqtop -Q theories AAPP -q
```

Both print `Closed under the global context`.
