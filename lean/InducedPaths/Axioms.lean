/-
External theorems cited by the preprint and not proved in this development.
Every axiom in the package is declared in this file. See `lean/AXIOMS.md`.
-/
module

public import InducedPaths.Graphs

open Classical
open scoped SimpleGraph
open SimpleGraph

@[expose] public section

namespace InducedPaths

variable {V : Type*}

/-- Vertices outside the image of an embedded 5-cycle. -/
def outsideCycle (c : Fin 5 → V) : Set V :=
  {v | ∀ i, c i ≠ v}

/-- Neighbourhood of `v` on the embedded 5-cycle, as a set of indices. -/
def cycleTrace (G : SimpleGraph V) (c : Fin 5 → V) (v : V) : Set (Fin 5) :=
  {i | G.Adj v (c i)}

/-- `Wᵢ` in Lemma 2.9: vertices outside `C` whose trace is exactly `{cᵢ}`. -/
def kmW (G : SimpleGraph V) (c : Fin 5 → V) (i : Fin 5) : Set V :=
  {v | v ∈ outsideCycle c ∧ cycleTrace G c v = {i}}

/-- `X_{i,i+1}` in Lemma 2.9: vertices outside `C` whose trace is exactly `{cᵢ, cᵢ₊₁}`. -/
def kmX (G : SimpleGraph V) (c : Fin 5 → V) (i : Fin 5) : Set V :=
  {v | v ∈ outsideCycle c ∧ cycleTrace G c v = {i, i + 1}}

/-- Theorem 2.4. Erdős–Saks–Sós: a connected graph has an induced path on at least `2r - 1`
vertices. The form `2r ≤ p + 1` avoids truncating subtraction at radius `0`.

Source: P. Erdős, M. Saks, and V. T. Sós, *Maximum induced trees in graphs*,
J. Combin. Theory Ser. B 41 (1986). -/
axiom erdos_saks_sos {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (h : G.Connected) :
    2 * radiusNat G ≤ inducedPathOrder G + 1

/-- Theorem 2.5. Camby–Schaudt, the implication (i)⇒(ii) of their Theorem 5 applied at `H = G`.
A connected `Pₖ`-free graph, `k ≥ 4`, has a connected dominating set `X` such that `G[X]` is
`P_{k-2}`-free or `G[X] ≅ Cₖ`.

Source: E. Camby and O. Schaudt, *A new characterization of Pk-free graphs*,
Algorithmica 75 (2016), Theorem 5. -/
axiom camby_schaudt {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (hk : 4 ≤ k) (hconn : G.Connected) (hp : IsPkFree G k) :
    ∃ X : Set V, (G.induce X).Connected ∧
      (∀ v, ∃ x ∈ X, v = x ∨ G.Adj v x) ∧
      (IsPkFree (G.induce X) (k - 2) ∨ Nonempty ((G.induce X) ≃g cycleGraph k))

/-- Theorem 2.6. Seinsche: a graph on at least two vertices with no induced `P₄` is disconnected
or has disconnected complement.

Source: D. Seinsche, *On a property of the class of n-colorable graphs*,
J. Combin. Theory Ser. B 16 (1974). -/
axiom seinsche {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hcard : 2 ≤ Fintype.card V) (hp : IsPkFree G 4) :
    ¬ G.Connected ∨ ¬ Gᶜ.Connected

/-- Lemma 2.9. Karthick–Maffray, Theorem 3.2(d), translated by `v_{i+1} = cᵢ`.
The cycle is induced. `C₄` and `C₆` in the hypothesis are induced cycles, as in their statement.
Indices are read in `Fin 5`.

Source: T. Karthick and F. Maffray, *Coloring (gem, co-gem)-free unit disk graphs*,
the emptiness list is their Theorem 3.2(d); the preprint cites that part only. -/
axiom karthick_maffray_C5 {V : Type*} (G : SimpleGraph V)
    (hp : IsPkFree G 6) (hc4 : ¬ cycleGraph 4 ⊴ G) (hc6 : ¬ cycleGraph 6 ⊴ G)
    (c : cycleGraph 5 ↪g G) :
    ∀ i : Fin 5,
      (kmX G c i = ∅ ∨ kmX G c (i + 1) = ∅) ∧
      (kmW G c i = ∅ ∨ kmW G c (i + 2) = ∅) ∧
      (kmX G c i = ∅ ∨ kmW G c (i - 1) ∪ kmW G c (i + 2) = ∅)

/-- Lemma 5.1. Chen–Xu, Lemma 3.4: a connected `(P₇, C₄, C₃)`-free graph with no clique cutset,
other than a complete graph, belongs to `𝔉`. Here `C₄` and `C₃` are induced, as in their statement.
`F₅` is the Petersen graph. The concrete members are defined in `InducedPaths.Graphs`.

Source: Chen and Xu, the family constructed in their Lemmas 3.1–3.3 and classified by Lemma 3.4. -/
axiom chen_xu_core {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hp : IsPkFree G 7)
    (hc4 : ¬ cycleGraph 4 ⊴ G) (htri : G.CliqueFree 3)
    (hcut : ¬ HasCliqueCutset G) (hcomplete : G ≠ ⊤) :
    InChenXuFamily G

end InducedPaths
