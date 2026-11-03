# Lean formalization (Phase 1)

This directory is a Lean 4 + Mathlib scaffold for the sealed preprint at commit `c6d3eb76a0201c3df429f174e2970b588ee702b7`. It is **not** a verification of the paper. Most proofs are `sorry`. Five external citations are axioms; see [`AXIOMS.md`](AXIOMS.md).

## Build

Toolchain file `lean/lean-toolchain`:

```text
leanprover/lean4:v4.35.0
```

Versions used to typecheck this scaffold:

| Tool | Version |
|------|---------|
| Lean | 4.35.0, commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc` |
| Lake | 5.0.0-src+eb6cafb |
| Mathlib | `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` |

From this directory, with [elan](https://github.com/leanprover/elan) on `PATH`:

```bash
lake build
```

`lake build` elaborates every declaration. `sorry` is accepted. The build does not run the Appendix A search: `InducedPaths.Certificate.replay` is a total function, and `four_seed_replay` is an explicit `sorry`, not `native_decide`.

The package is `inducedPaths`. Modules live under `InducedPaths/`.

## What the definitions are

`InducedPaths/Defs.lean` follows the preprint.

- `StrongC4Free` is absence of a `C₄` subgraph (`cycleGraph 4 ⊑ G`). `cC4` is `1` exactly then.
- `IsPkFree` is absence of an induced `Pₖ`. `inducedPathOrder` is the largest such order.
- `lambda`, `neighbourhoodIndependenceSum` (`S`), and `ell` (`ℓ = S / n`) are the neighbourhood-independence quantities.
- `radiusNat` is `G.radius.toNat`.
- `triangleCount`, `trianglesAt`, `deletionLoss` (`L(v) = S(G) - S(G - v)`), cut vertices, and clique cutsets match Sections 2 and 5.
- `GenK` and `Rad` are the open statements `GEN_K` and `RAD(r)`. They are not theorems.

Concrete graphs (`Petersen`, `Γₕ`, `H₈`, the Chen–Xu list, the radius-4 extension, `θₖ`) are in `InducedPaths/Graphs.lean`.

## Proved in this scaffold

These declarations have no `sorry` in their own proof. Several still depend on a `sorry` or on an axiom; that is noted in the table.

| Paper | Lean | Status |
|-------|------|--------|
| Lemma 2.1(1) | `commonNeighbors_subsingleton` | proved |
| Lemma 2.1(2), degree ≤ 1 in `G[N(v)]` | `neighborhood_degree_le_one` | proved |
| Lemma 2.1(2), `λ(v) = d(v) - t(v)` | `lambda_eq_degree_sub_trianglesAt` | proved |
| Lemma 2.1(2), component count | `lambda_eq_ncard_components` | `sorry` |
| Lemma 2.1(3), `S = 2e - 3T` | `strongC4Free_S_identity` | proved |
| Lemma 2.1, the three identities above | `lemma_2_1` | proved, excluding the component sentence |
| Lemma 2.2, `2λ - t = 2d - 3t` | `lemma_2_2_lambda` | proved |
| Lemma 2.8 | `lemma_2_8` | proved from the axiom `camby_schaudt` |
| Remark 4.6 | `remark_4_6` | proved (arithmetic) |
| Corollary 4.4, `S ≤ 2n` and `ℓ ≤ 2` | `corollary_4_4` | proved from `corollary_4_4_mass`, which is `sorry` |
| Remark 5.12 | `remark_5_12` | proved from the geodesic lemma, Theorem 5.11, Theorem 5.10, Corollary 4.4, and `erdos_saks_sos`; those inputs are `sorry` or an axiom |
| Proposition 6.2, closed form and limit | `theta_closed_form`, `theta_gap_tendsto` | proved |
| Corollary 6.1 | `corollary_6_1` | proved from Theorem 5.11 (`sorry`) and `erdos_saks_sos` |
| Corollary 6.3, `S ≤ 3n - 1` and `ℓ < 3` | `corollary_6_3` | proved from Theorem 5.10 and `petersen_inducedPathOrder`, both `sorry` |
| Appendix A choice-list lengths | `choicesDist0_length` … `choicesDist3_length` | proved by `rfl` (`36`, `31`, `46`, `5`) |

`trianglesAt_eq_neighborEdges` (triangles at `v` are the edges of `G[N(v)]`) is proved for every simple graph. It is the counting step inside Lemma 2.1(3).

## Not proved

There are **33** declarations whose proof is `sorry`:

- `lambda_eq_ncard_components`
- `lemma_2_2`, `lemma_2_3`, `lemma_2_7`, `lemma_2_10`
- `inducedPathOrder_ge_radius_succ`
- `lemma_3_1`, `lemma_3_2`, `lemma_3_3`, `lemma_3_4`, `lemma_3_5`, `theorem_3_6`
- `lemma_4_1`, `theorem_4_2`, `lemma_4_3`, `corollary_4_4_mass`, `corollary_4_5`
- `lemma_5_2`, `lemma_5_3`, `lemma_5_4`, `theorem_5_5`, `theorem_5_6_noniso`, `theorem_5_6`, `theorem_5_7`
- `lemma_5_8_share`, `lemma_5_8_disjoint`, `lemma_5_8_path`, `lemma_5_9`, `petersen_inducedPathOrder`, `theorem_5_10`, `theorem_5_11`
- `proposition_6_2`
- `Certificate.four_seed_replay`

The five axioms in [`AXIOMS.md`](AXIOMS.md) are not included in that count.

## Certificate interface

`InducedPaths/Certificate.lean` copies the four distance rows of `certificates/gen3/verify_gen3.py` (not the obsolete one-triangle row). `replay` walks the same depth-first preorder, with fuel `choices.length + 1`:

- the designated vertex must have mask-loss `< 4`;
- a child mask must contain that vertex, must not give an old vertex two neighbours in the mask, and must not complete an induced `P₇` by the Appendix A trace test;
- `none` means the list is not a complete legal closing, so an unrestricted node is a failure.

Mask-loss `2d - 3t` is the paper's `L(v)` on a strong `C₄`-free graph only after Lemma 2.2, which is still `sorry`. `four_seed_replay` states that the four lists return `(nodes, max order, leaves) = (36, 17, 7)`, `(31, 15, 6)`, `(46, 11, 21)`, `(5, 10, 3)`. Because the checker has no unrestricted branch, those successes would force unrestricted count `0`. Lemma 5.9 does not follow from the replay alone; its `sorry` is the remaining mathematical step.
