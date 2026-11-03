/-
Definitions for the JGT R15 preprint at `c6d3eb76` (paper/main.tex).

`StrongC4Free` is absence of a `C₄` subgraph (chords allowed): the paper's strong
`C₄`-free condition, and `cC4 = 1` exactly then. `IsPkFree` is absence of an
induced `Pₖ`. Neighbourhood independence `lambda`, the sum `S`, and the average
`ell` match Section 2. `deletionLoss` is `L(v) = S(G) - S(G - v)`.
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Diam
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Lattice.Nat

open Classical
open scoped SimpleGraph
open SimpleGraph

@[expose] public section

namespace InducedPaths

variable {V : Type*}

/-- No `C₄` subgraph. This is the paper's strong `C₄`-free condition. -/
def StrongC4Free (G : SimpleGraph V) : Prop := ¬ cycleGraph 4 ⊑ G

/-- `c_{C₄}(G)`, equal to `1` precisely on strong `C₄`-free graphs. -/
noncomputable def cC4 (G : SimpleGraph V) : ℕ :=
  if StrongC4Free G then 1 else 0

/-- `G` has no induced path on `k` vertices. -/
def IsPkFree (G : SimpleGraph V) (k : ℕ) : Prop := ¬ pathGraph k ⊴ G

/-- Largest order of an induced path. `sSup` of an unbounded set of naturals is `0`,
so finiteness is part of every lemma that treats this as a maximum. -/
noncomputable def inducedPathOrder (G : SimpleGraph V) : ℕ :=
  sSup {n | pathGraph n ⊴ G}

/-- Independence number of the induced subgraph on `s`. -/
noncomputable def alphaIn (G : SimpleGraph V) (s : Set V) : ℕ :=
  (G.induce s).indepNum

/-- `λ(v) = α(G[N(v)])`. -/
noncomputable def lambda (G : SimpleGraph V) (v : V) : ℕ :=
  alphaIn G (G.neighborSet v)

variable [Fintype V]

/-- `S(G) = ∑_v λ(v)`. -/
noncomputable def neighbourhoodIndependenceSum (G : SimpleGraph V) : ℕ :=
  ∑ v, lambda G v

/-- `ℓ(G) = S(G) / n`. Division by zero is the junk value `0`. -/
noncomputable def ell (G : SimpleGraph V) : ℚ :=
  (neighbourhoodIndependenceSum G : ℚ) / (Fintype.card V : ℚ)

/-- Radius as a natural number. For a connected finite graph this is the paper's `r(G)`. -/
noncomputable def radiusNat (G : SimpleGraph V) : ℕ := G.radius.toNat

variable [DecidableEq V]

/-- Number of edges. -/
noncomputable def edgeCount (G : SimpleGraph V) [Fintype G.edgeSet] : ℕ :=
  G.edgeFinset.card

/-- Number of triangles, `T(G)`. -/
noncomputable def triangleCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (G.cliqueFinset 3).card

/-- Number of triangles incident with `v`, the paper's `t(v)`. -/
noncomputable def trianglesAt (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  ({s ∈ G.cliqueFinset 3 | v ∈ s} : Finset _).card

/-- `L(v) = S(G) - S(G - v)`, as a truncated natural difference. On a strong
`C₄`-free graph Lemma 2.2 shows the difference is nonnegative and equals `2d(v) - 3t(v)`. -/
noncomputable def deletionLoss (G : SimpleGraph V) (v : V) : ℕ :=
  neighbourhoodIndependenceSum G -
    neighbourhoodIndependenceSum (G.induce {w | w ≠ v})

/-- `D_G(U) = S(G) - S(G - U)`. -/
noncomputable def deletionLossSet (G : SimpleGraph V) (U : Set V) [DecidablePred (· ∈ U)] : ℕ :=
  neighbourhoodIndependenceSum G - neighbourhoodIndependenceSum (G.induce Uᶜ)

/-- A vertex whose deletion destroys preconnectedness. `K₁` has no cut vertex:
the induced subgraph on the empty set is preconnected. -/
def IsCutVertex (G : SimpleGraph V) (v : V) : Prop :=
  ¬ (G.induce {w | w ≠ v}).Preconnected

/-- A clique cutset in the sense used for Lemma 2.10 and Chen–Xu: a nonempty proper
clique whose deletion leaves a graph that is not preconnected. -/
def HasCliqueCutset (G : SimpleGraph V) : Prop :=
  ∃ s : Set V, G.IsClique s ∧ s.Nonempty ∧ sᶜ.Nonempty ∧ ¬ (G.induce sᶜ).Preconnected

/-- REAL-133 for one graph: `p ≥ r + ℓ^{c_{C₄}}` whenever `n ≥ 2` and `G` is connected.
The exponent is a natural-number power, so `c = 0` yields `1`, including at `ℓ = 0`. -/
def SatisfiesReal133 (G : SimpleGraph V) : Prop :=
  2 ≤ Fintype.card V → G.Connected →
    (inducedPathOrder G : ℚ) ≥ (radiusNat G : ℚ) + ell G ^ cC4 G

/-- Conjecture 1.1, quantified over finite connected graphs of order at least 2. -/
def Real133 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V), SatisfiesReal133 G

/-- `M(n)` from Theorem 3.6, including the orders `2 ≤ n ≤ 6` recorded in that theorem.
The value `0` for `n < 2` is unused. -/
def extremalDensity (n : ℕ) : ℚ :=
  match n with
  | 2 => 1
  | 3 => 4 / 3
  | 4 => 3 / 2
  | 5 => 2
  | 6 => 2
  | 7 => 16 / 7
  | 8 => 5 / 2
  | 9 => 8 / 3
  | 10 => 3
  | n => if 11 ≤ n then 2 + (2 : ℚ) / n else 0

/-- `f(n) = 3n - min{n - 10, 5 + 1_{n even}}` from Theorem 5.6. Used for `n ≥ 10`. -/
def edgeExtremal (n : ℕ) : ℕ :=
  3 * n - min (n - 10) (5 + if Even n then 1 else 0)

/-- `GEN_K` for `K ≥ 3`: every connected strong `C₄`-free graph with `p ≤ 2K` has `S ≤ Kn`.
This is an open proposition. It is not asserted. -/
def GenK (K : ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → StrongC4Free G → inducedPathOrder G ≤ 2 * K →
      neighbourhoodIndependenceSum G ≤ K * Fintype.card V

/-- `RAD(r)` for `r ≥ 4`: every connected strong `C₄`-free graph with radius `r` and
induced-path order `2r - 1` has `ℓ ≤ r - 1`. Open; not asserted.
The subtraction `2 * r - 1` is the natural truncation, so the equality hypothesis is the
paper's equality whenever `r ≥ 1`. -/
def Rad (r : ℕ) : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    G.Connected → StrongC4Free G → radiusNat G = r → inducedPathOrder G = 2 * r - 1 →
      ell G ≤ (r - 1 : ℚ)

end InducedPaths
