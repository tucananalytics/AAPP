# Arithmetic Analysis of Polymorphic Programs and the Verification of Typed Agent Interfaces

Coq development accompanying the paper

> R. Prince, *Arithmetic Analysis of Polymorphic Programs and the Verification of
> Typed Agent Interfaces* (`article/aapf2.pdf`).

Polymorphic functions between lists are represented, via the theory of containers,
by a map on lengths and a map on indices.  When both are piecewise linear, equality
of two such functions is a universal sentence of Presburger arithmetic, and it is
proved here by a single tactic, `containers`, without induction.  The same objects
are then read as *adapters* between typed agent interfaces.  For adapters between
lists the arithmetic equality is shown to coincide with equality of container
morphisms and with observational equivalence: two adapters are equal exactly when
every agent wrapped by them produces the same runs against every environment.

The development is self-contained, uses only the standard library, and contains no
axioms and no admitted lemmas.

## Building

Requirements: Coq 8.18 or later, or the Rocq Prover 9.x, and `make`.

```
make            # compiles theories/*.v  (about ten seconds)
make clean
```

The makefile uses `coq_makefile` when it is on the path and `rocq makefile`
otherwise; to choose explicitly, run `make GEN="rocq makefile"`.

Tested with Coq 8.18.0 and with Rocq 9.3.0 (standard library 9.2.0).  Under Rocq 9
each file produces one deprecation notice, because the sources use the spelling
`From Coq Require ...`, which is the one accepted by both systems.

## Contents

| File | Content | Paper |
|------|---------|-------|
| `theories/Piecewise.v` | Linear terms `lfun` and piecewise-linear terms `Plfun`; evaluation; substitution and its correctness; the quantifier-free graphs of cut-off subtraction and of the conditional; the tactic `arith` (case analysis, then `lia`). | §4.3, §4.6 |
| `theories/ListMorphisms.v` | List morphisms as pairs of terms, `PPCm` (shape map and position map); the interpretation `interp`; quasi-container equality `pcmEQ` and its soundness `pcmEQ_ok`; the range condition `in_range` and the losslessness condition `lossless`; composition `comp1`, `comp2` with correctness `comp1_ok`, `comp2_ok`; closed terms and `pcmEQ_on_pcmEQ`; the tactic `containers`; the counterexample search `find_cex` with its exact specification `find_cex_spec`, and the tactic `refute`. | §4.2–4.4, §4.6 |
| `theories/Examples.v` | The basic morphisms (reverse, tail, take, drop, rotations, last-*k*, the pinned window, append, projections, …) with their range and losslessness lemmas; the fourteen list identities of the figure "Properties of lists"; the adapter laws (`lastk_idem`, `lastk_app`, `pin_app`, `head_pin`, `split_merge`, `split3_merge`, …); refuted laws with their computed counterexamples; a transfer lemma relating each morphism to the corresponding standard-library function (`Rev_spec`, `Take_spec`, `Pin_spec`, `App_spec`, …); and theorems about ordinary lists obtained with no induction (`rev_involutive_via_containers`, `firstn_skipn_via_containers`). | §4.5, §4.6, §5.3 |
| `theories/Containers.v` | Containers, extensions, container morphisms (dependent lenses), `mmap` and functoriality, cartesian morphisms; products and pairing (`cProd`, `cpair`); composition of containers and lifting of morphisms (`cComp`, `whisker`, `lift_all`); agents, environments, `wrap`, `run`; equality of morphisms into the list container (`cmorEq`); observational equivalence (`cmorEq_run`, `runs_cmorEq`); the bridge from the arithmetic representation for one and two lists (`to_cmor`, `to_cmor2`, `comp1_represents`, `comp2_represents`, `represents_cmorEq`, `pcmEQ_iff_cmorEq`, `lossless_cartesian`); the tree container and the flattening morphism (`flatten`, `flatten_cartesian`). | §2, §3, §5.1–5.2 |
| `theories/AgentExamples.v` | The adapters as container morphisms; their laws as equations between container morphisms (`window_idem`, `window_append`, `pinned_append`, `split_merge_cmor`, …) and as statements about runs (`window_idem_run`, `window_append_run`, …); inequalities obtained from counterexamples (`window_ne_firstk`, `drop_window_observable`); losslessness of pipelines (`pipeline_cartesian`); concrete agents and environments, including typed tool calls, whose runs are computed by the kernel. | §5.3 |
| `article/` | The paper: `aapf2.tex`, its macros `aappmacros.sty`, the bibliography `aapp.bib` (and the generated `aapf2.bbl`), and the PDF.  `fundam.cls` and `fundam.bst` are the unmodified LaTeX class and BibTeX style of *Fundamenta Informaticae*. | |
| `legacy/` | Earlier Coq sources (Coq 8.1) that accompanied the author's doctoral thesis, kept for reference.  They do not compile with current versions of Coq. | |

## Where the results of the paper are

| Paper | Coq |
|-------|-----|
| Functoriality of `mmap`; composition of cartesian morphisms (§2.3) | `mmap_id`, `mmap_comp`, `cartesian_comp` |
| Products and pairing (§3.1) | `cProd`, `cpair`, `cfst_cpair`, `csnd_cpair` |
| Compositionality of wrapping (§3.3) | `wrap_id`, `wrap_comp`, `wrap_ext_eq`, `run_wrap_pull` |
| Lifting to lists of items (§3.4) | `whisker`, `whisker_comp`, `whisker_assoc`, `cmorEq_whisker`; `lift_all`, `lossless_all`, `flatten_all` |
| Flattening is cartesian; its shape map is not injective (§3.5) | `flatten_cartesian`, `Sum_not_injective` |
| Graphs of piecewise-linear terms (§4.3) | `suB_graph`, `pf_graph`, `psubst_ok` |
| Soundness of quasi-container equality (§4.4) | `pcmEQ_ok` |
| Correctness of composition (§4.4) | `comp1_ok`, `comp2_ok` |
| Properties of lists (§4.5) | `rev_rev`, `rev_app`, …, `butlast_rot` in `Examples.v` |
| The counterexample search is exact (§4.6) | `find_cex_spec`, `find_cex_sound` |
| From terms to container morphisms (Theorem 5.1) | `to_cmor`, `to_cmor2`, `to_cmor_interp`, `to_cmor2_interp`, `comp1_represents`, `comp2_represents`, `represents_cmorEq`, `pcmEQ_iff_cmorEq`, `find_cex_cmor`, `lossless_cartesian` |
| Observational equivalence (Theorem 5.2) | `cmorEq_run`, `runs_cmorEq`, `list_adapters_iff_runs`, `list2_adapters_iff_runs`, `pcmEQ_iff_runs`; the counterexample `pick_same_runs`, `pick_differ`; `cmorEq_run_lifted` |
| Losslessness (§5.2) | `lossless_cartesian`, `Rev_lossless`, `Rot_lossless`, `Unrot_lossless`, `Tail_lossy`, `Take_lossy`, `Drop_lossy`, `Lastk_lossy`, `Pin_lossy` |
| Context windows, pinned windows, refuted laws, fan-out/fan-in, tool calls, planners (§5.3) | `lastk_app`, `window_append`, `window_append_run`, `head_pin`, `pin_app`, `pinned_append`, `head_lastk_cex`, `drop_lastk_refuted`, `drop_window_observable`, `badlastk_detected`, `split_merge`, `split3_merge`, `run_window`, `run_firstk`, `run_caller_window`, `pcmEQ_run_planner`, `pipeline_cartesian` |

`cmorEq_run_lifted` takes function extensionality as an explicit hypothesis
(`FunExt`); nothing is assumed as an axiom.

## Proving and refuting a law

```coq
From AAPP Require Import Examples.

(* take n (drop m xs) = drop m (take (n + m) xs) *)
Goal forall n m, pcmEQ 1 (comp1 1 (Take n) (Drop m)) (comp1 1 (Drop m) (Take (n + m))).
Proof. containers. Qed.

(* drop 1 (last_2 xs) = last_1 xs  is false: the search returns a list of length 1 *)
Goal ~ pcmEQ 1 (comp1 1 (Drop 1) (Lastk 2)) (Lastk 1).
Proof. refute 4. Qed.
```

## Checking that no axioms are used

```
printf 'From AAPP Require Import Examples Containers AgentExamples.\nPrint Assumptions rev_involutive_via_containers.\nPrint Assumptions cmorEq_run.\nPrint Assumptions window_idem_run.\n' > /tmp/assumptions.v
coqc -Q theories AAPP /tmp/assumptions.v
```

Each line of output is `Closed under the global context`.

## Compiling the paper

```
cd article
pdflatex aapf2 && bibtex aapf2 && pdflatex aapf2 && pdflatex aapf2
```

## Licence

CC0 1.0 Universal; see `LICENSE`.
