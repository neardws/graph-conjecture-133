# Axioms

The package has five axioms, all in `InducedPaths/Axioms.lean`. Phases 2–7 added none. Each one is an external theorem the preprint cites and does not prove. Nothing proved in the preprint is an axiom. `GenK` and `Rad` are definitions of open statements; they are not axioms.

`sorry` and `admit` are separate from these axioms. They would be unfinished work inside this repository, not external citations. The numbered inventory currently has no `sorry` and no `admit`; see `lean/README.md`.

| Lean name | Paper | What is assumed |
|-----------|-------|-----------------|
| `erdos_saks_sos` | Theorem 2.4 | A connected finite graph satisfies `2 r ≤ p + 1`. Source: Erdős, Saks, and Sós, *Maximum induced trees in graphs*, J. Combin. Theory Ser. B 41 (1986). |
| `camby_schaudt` | Theorem 2.5 | For `k ≥ 4`, a connected `Pₖ`-free graph has a connected dominating set `X` such that `G[X]` is `P_{k-2}`-free or `G[X] ≅ Cₖ`. This is (i)⇒(ii) of Camby–Schaudt, Theorem 5, with `H = G`. Source: Algorithmica 75 (2016). |
| `seinsche` | Theorem 2.6 | A graph on at least two vertices with no induced `P₄` is disconnected or has disconnected complement. Source: Seinsche, J. Combin. Theory Ser. B 16 (1974). |
| `karthick_maffray_C5` | Lemma 2.9 | Emptiness list for an induced `C₅` in a graph with no induced `P₆`, `C₄`, or `C₆`. Indices are in `Fin 5`, with the preprint's translation `v_{i+1} = cᵢ`. Source: Karthick–Maffray, Theorem 3.2(d). |
| `chen_xu_core` | Lemma 5.1 | A connected `(P₇, induced C₄, triangle)`-free graph with no clique cutset, other than a complete graph, lies in `InChenXuFamily`. Source: Chen–Xu, Lemma 3.4. |

`lemma_2_8` is not an axiom: it is `camby_schaudt` at `k = 6`. Lemma 5.2 (the edge table for `𝔉`) is not an axiom.

No axiom has been checked against Mathlib's axiom footprint beyond the declarations above. A later phase should prove or replace each of them.
