# Lean formalization

This directory is a Lean 4 + Mathlib development of the sealed preprint at commit `c6d3eb76a0201c3df429f174e2970b588ee702b7`. It formalizes the main theorems and selected supporting statements. The precise coverage is listed in this README. The numbered inventory is **0** `sorry` and **0** `admit` (Phases 1–7). It is **not** a fully Lean-verified proof of the paper, and it is not a kernel verification from an empty axiom set. Five external citations remain axioms; see [`AXIOMS.md`](AXIOMS.md). Phases 2–7 added no hand-declared axioms. Finite checks use Lean's `native_decide` compiler/runtime trust mechanism, including trace witnesses, graph tables, and Petersen path/symmetry certificates. `GenK` and `Rad` remain definitions of propositions, not blanket axioms or assertions; the `GenK 3` clause is proved from the completed Section 5 bound.

## Build

Toolchain file `lean/lean-toolchain`:

```text
leanprover/lean4:v4.35.0
```

Versions used to typecheck this development:

| Tool | Version |
|------|---------|
| Lean | 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| Lake | 5.0.0-src+eb6cafb |
| Mathlib | `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` |

From this directory, with [elan](https://github.com/leanprover/elan) on `PATH`:

```bash
lake build
```

`lake build` elaborates every declaration and runs the native finite checks, including `four_seed_replay`. Follow it with `lake env lean Phase6Audit.lean` and `lake env lean Phase7Audit.lean` to inspect the completed targets' actual axiom dependencies.

The package is `inducedPaths`. Modules live under `InducedPaths/`.

## What the definitions are

`InducedPaths/Defs.lean` follows the preprint.

- `StrongC4Free` is absence of a `C₄` subgraph (`cycleGraph 4 ⊑ G`). `cC4` is `1` exactly then.
- `IsPkFree` is absence of an induced `Pₖ`. `inducedPathOrder` is the largest such order.
- `lambda`, `neighbourhoodIndependenceSum` (`S`), and `ell` (`ℓ = S / n`) are the neighbourhood-independence quantities.
- `radiusNat` is `G.radius.toNat`.
- `triangleCount`, `trianglesAt`, `deletionLoss` (`L(v) = S(G) - S(G - v)`, with `G - v` the induced subgraph on `{v}ᶜ`), cut vertices, and clique cutsets match Sections 2 and 5.
- `GenK` and `Rad` define the proposition families `GEN_K` and `RAD(r)`. They are not blanket theorem declarations; specific conditional clauses are proved where stated.

Concrete graphs (`Petersen`, `Γₕ`, `H₈`, the Chen–Xu list, the radius-4 extension, `θₖ`) are in `InducedPaths/Graphs.lean`.

## Numbered inventory

**0** `sorry` and **0** `admit`. Several declarations depend on the five citation axioms or on finite `native_decide` checks. None retains a proof placeholder. This count is not a claim that the paper is verified from an empty axiom set.

| Paper | Lean | Status |
|-------|------|--------|
| Lemma 2.1(1) | `commonNeighbors_subsingleton` | proved |
| Lemma 2.1(2), degree ≤ 1 in `G[N(v)]` | `neighborhood_degree_le_one` | proved |
| Lemma 2.1(2), `λ(v) = d(v) - t(v)` | `lambda_eq_degree_sub_trianglesAt` | proved |
| Lemma 2.1(2), component count | `lambda_eq_ncard_components` | proved |
| Lemma 2.1(3), `S = 2e - 3T` | `strongC4Free_S_identity` | proved |
| Lemma 2.1 | `lemma_2_1` | proved, including the component count |
| Lemma 2.2, `2λ - t = 2d - 3t` | `lemma_2_2_lambda` | proved |
| Lemma 2.2, `L(v) = 2d(v) - 3t(v)` | `lemma_2_2` | proved |
| Lemma 2.3, cut formula | `lemma_2_3` | proved; no `C₄`-free hypothesis |
| Lemma 2.7 | `lemma_2_7` | proved from the axiom `seinsche` |
| Lemma 2.8 | `lemma_2_8` | proved from the axiom `camby_schaudt` (requires `[Finite V]`) |
| Lemma 2.10 | `lemma_2_10` | proved; a 2-clique cutset produces an induced `P₇` |
| Geodesic `p ≥ r + 1` | `inducedPathOrder_ge_radius_succ` | proved |
| Lemma 3.1 | `lemma_3_1` | proved |
| Lemma 3.2 | `lemma_3_2` | proved from Lemma 2.7, hence from `seinsche` |
| Lemma 3.3 | `lemma_3_3` | proved; inactive neighbourhood components supply disjoint private simplicial vertices |
| Lemma 3.4 | `lemma_3_4` | proved; antipodal traces, exact mass, cardinality and radius bounds |
| Lemma 3.5 | `lemma_3_5` | proved from Lemmas 2.7, 2.8 and 3.4; uses existing `seinsche` and `camby_schaudt` |
| Theorem 3.6 | `theorem_3_6` | proved: sharp density envelope, complete equality list, and Petersen-only `S = 3n`; uses existing `karthick_maffray_C5` and finite native decisions |
| Lemma 4.1 | `lemma_4_1` | proved with the paper’s necessary `P₈`-free hypothesis restored; the earlier hypothesis-free statement has a formally checked counterexample |
| Theorem 4.2 | `theorem_4_2` | proved in both directions, including arbitrary extension attachments, radius and induced-path order |
| Remark 4.6 | `remark_4_6` | proved (arithmetic) |
| Corollary 4.4, exact mass | `corollary_4_4_mass` | proved from the forward radius-four classification and exact extension counts |
| Corollary 4.4, `S ≤ 2n` and `ℓ ≤ 2` | `corollary_4_4` | proved from the exact mass formula |
| Corollary 4.5 | `corollary_4_5` | proved; equality is exactly zero added-edge vertices and zero matching edges |
| Lemma 4.3 | `lemma_4_3` | proved; an off-cycle vertex of an induced path is an endpoint |
| Lemma 5.3 | `lemma_5_3` | proved from the distance layers at a vertex that starts no induced `P₄` |
| Lemma 5.8(1) | `lemma_5_8_share` | proved; the statement assumes `a ≠ d` |
| Lemma 5.8(2) | `lemma_5_8_disjoint` | proved; at most one cross edge between disjoint triangles |
| Lemma 5.8(4) | `lemma_5_8_path` | proved; two disjoint triangles at set-distance `d` give an induced path of order `d + 3` |
| Lemma 5.9 | `lemma_5_9` | proved; actual seed extraction, mask-loss identity, normalized ambient extensions and witnessed finite closure |
| Petersen induced-path order | `petersen_inducedPathOrder` | proved; explicit induced `P₅`, and no induced `P₆` by a `Bool` search |
| Remark 5.12 | `remark_5_12` | the case `c_{C₄} = 0` uses the proved geodesic; the case `c_{C₄} = 1` uses Theorems 5.11 and 5.10, Corollary 4.4, and `erdos_saks_sos` |
| Proposition 6.2, closed form and limit | `theta_closed_form`, `theta_gap_tendsto` | proved |
| Proposition 6.2, the graph `θₖ` | `proposition_6_2` | proved: strong `C₄`-free, order `2k+2`, radius 3, induced-path order 6, `S = 6k = 3n-6` |
| Corollary 6.1 | `corollary_6_1` | proved from the proved Theorem 5.11 and `erdos_saks_sos` |
| Corollary 6.3, `S ≤ 3n - 1` and `ℓ < 3` | `corollary_6_3` | proved from the proved Theorem 5.10 and `petersen_inducedPathOrder` |
| Appendix A choice-list lengths | `choicesDist0_length` … `choicesDist3_length` | proved by `rfl` (`36`, `31`, `46`, `5`) |
| Appendix A replay | `four_seed_replay` | proved by `native_decide` |

`trianglesAt_eq_neighborEdges` (triangles at `v` are the edges of `G[N(v)]`) is proved for every simple graph. It is the counting step inside Lemma 2.1(3).

## Phase 7: Section 5 proof completion

The remaining **8 → 0** direct proof placeholders are eliminated, with unchanged public theorem signatures:

- `lemma_5_2`: exact counts for the Chen–Xu family.
- `lemma_5_4`: literal degree-one stripping, connected terminal core classification, and exact edge/deficit identities.
- `theorem_5_5`: triangle-free edge bound and Petersen equality, the conditional `GenK 3` clause, and strict bipartite bound.
- `theorem_5_6_noniso`: all displayed nonisomorphism clauses via degree invariants.
- `theorem_5_6`: extremal envelope and actual canonical isomorphism classification, including Petersen leaf fibers and both F₂ leaf sites.
- `theorem_5_7`: at-most-one-triangle mass bound, with rooted cut-side induction and exact attachment counts.
- `theorem_5_10`: global mass bound and Petersen equality, combining the low-loss certificate with the concrete strict unique-triangle endgame.
- `theorem_5_11`: the `c_{C₄}` case split and radius/order analysis using the preceding bounds.

The strict endgame reconstructs an actual thirteen-vertex induced extension from a hypothetical equality core, then excludes it with an induced-P₇ certificate. Numerical equality alone is not substituted for graph isomorphism. `Statements.lean` assembles Theorems 5.5, 5.10 and 5.11 after Lemma 5.9, avoiding a universal-low-loss dependency cycle; import `InducedPaths.Statements` or `InducedPaths` for the complete numbered interface. No public theorem hypothesis was changed in Phase 7.

Run `lake env lean Phase7Audit.lean` to inspect all eight completed targets. None should list `sorryAx`. This does **not** remove the five external citation axioms or native-evaluator/compiler trust. In particular, Chen–Xu classification remains the declared `chen_xu_core` input; finite table, attachment, Petersen path and symmetry checks introduce generated native-decision dependencies rather than new handwritten mathematical axioms.

Lemma 5.9 is proved, but not by `four_seed_replay` alone. `SeedRealization` extracts an actual induced seed; `MaskGraph` identifies the executable loss with graph triangles and degree; `RealizedLoss` uses exact induced-subgraph locality; and the witnessed replay excludes an ambient graph with all losses at least four. The proof's axiom audit contains no `sorryAx` and no external citation axiom, only the standard Lean axioms and the finite trace check's native-decision trust dependency. `GenK` and `Rad` remain proposition definitions; no general `GenK`/`Rad` family is asserted.

`Statements.lean` preserves the public statement import and Lemma 5.9 signature. `StatementsCore.lean` assembles the numbered declarations without circular dependencies. Section 3 uses the complete hexagon classification (`C6Classification`, `C6Named*`, `C6Extremal`), pentagon mass bounds (`C5Mass`), direct hereditary simplicial elimination (`ChordalStructure`), and exhaustive upper-triangular Boolean graph checks for orders 2–6 (`SmallOrderExtremal`, at most 32,768 codes, with proved decoding and semantic transport). Section 4 uses actual finite path witnesses and ambient lifting (`C8Structure`, `C6RadiusStructure`), a standalone converse for arbitrary extension attachments (`RadiusFourConverse`), and bijective edge/triangle counts (`RadiusFourMass`).

Theorem 3.6 depends on the existing `karthick_maffray_C5` axiom, standard Lean axioms, and finite native-decision trust. Theorem 4.2 and its mass/equality corollaries depend on existing `camby_schaudt` and `seinsche` axioms plus standard/native trust. None of these completed targets depends on `sorryAx`. The chordal branch, arbitrary-extension converse, and extension mass count use only the standard Lean axioms. This does not verify the whole paper.

The five axioms in [`AXIOMS.md`](AXIOMS.md) are not included in that count.

## Certificate

`InducedPaths/Certificate.lean` copies the four distance rows of `certificates/gen3/verify_gen3.py` (not the obsolete one-triangle row). `replay` walks the same depth-first preorder, with fuel `choices.length + 1`. Traces of 6-sets are computed once per graph and then scanned against each mask.

- the designated vertex must have mask-loss `< 4`;
- a child mask must contain that vertex, must not give an old vertex two neighbours in the mask, and must not complete an induced `P₇` by the Appendix A trace test;
- `none` means the list is not a complete legal closing, so an unrestricted node is a failure.

`four_seed_replay` evaluates to `(nodes, max order, leaves) = (36, 17, 7)`, `(31, 15, 6)`, `(46, 11, 21)`, `(5, 10, 3)`. Because the checker has no unrestricted branch, those successes force unrestricted count `0`.

`TraceWitnessCheck` performs a strengthened replay with the original choices and `extensions`: at every one of the 118 nodes it independently constructs and verifies an injective induced-`P₇` path for every rejected trace attachment. The greedy path generator is not trusted: its output must satisfy all adjacency equivalences, injectivity and trace support. Successful replay yields `WitnessClosed` for each seed. This avoids assuming unproved generic correctness of `grow` or `componentList` and does not change the certificate semantics.

The ambient extension proof additionally preserves `Normalized` (all row bits below the current order), because in-range symmetry and looplessness alone do not prevent old high bits from contaminating a new vertex. The proof verifies the degree and triangle loss identity, produces a new ambient neighbour by locality, encodes its bounded neighbourhood mask, and follows a legal child. A finite witnessed closing tree makes an ambient counterexample impossible.
