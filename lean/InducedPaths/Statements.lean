/-
Statements of the preprint, in dependency order. Proofs are `sorry` except where noted.
Paper numbers refer to `paper/main.tex` at `c6d3eb76`.
-/
module

public import InducedPaths.Basic
public import InducedPaths.Certificate
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

open scoped SimpleGraph
open Finset SimpleGraph

@[expose] public section

namespace InducedPaths

variable {V : Type*} {G : SimpleGraph V}

/-! ### Lemma 2.1 assembled -/

/-- Lemma 2.1, the three identities that are proved. The sentence
`λ(v)` equals the number of components of `G[N(v)]` is
`lambda_eq_ncard_components` and is still `sorry`. -/
theorem lemma_2_1 (hG : StrongC4Free G) [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    (∀ x y, x ≠ y → (G.commonNeighbors x y).Subsingleton) ∧
      (∀ v, lambda G v = G.degree v - trianglesAt G v) ∧
      neighbourhoodIndependenceSum G = 2 * edgeCount G - 3 * triangleCount G := by
  refine ⟨?_, ?_, strongC4Free_S_identity hG⟩
  · intro x y hxy
    exact commonNeighbors_subsingleton hG hxy
  · intro v
    exact lambda_eq_degree_sub_trianglesAt hG v

/-- Lemma 2.2, the numeric identity `2λ(v) - t(v) = 2d(v) - 3t(v)`. -/
theorem lemma_2_2_lambda (hG : StrongC4Free G) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (v : V) :
    2 * lambda G v - trianglesAt G v = 2 * G.degree v - 3 * trianglesAt G v := by
  have h := lambda_add_trianglesAt hG v
  omega

/-- Lemma 2.2. `L(v) = 2d(v) - 3t(v)`. The general unit-sum formula needs the
component identification, which is still open; see `lambda_eq_ncard_components`. -/
theorem lemma_2_2 (hG : StrongC4Free G) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (v : V) :
    deletionLoss G v = 2 * G.degree v - 3 * trianglesAt G v := by
  sorry

/-- Lemma 2.3. No `C₄`-free hypothesis. `A` and `B` are the two sides of `G - v`. -/
theorem lemma_2_3 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {v : V}
    (A B : Finset V) (hA : A.Nonempty) (hB : B.Nonempty) (hdisj : Disjoint A B)
    (hcover : (A ∪ B : Set V) = {w | w ≠ v})
    (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    neighbourhoodIndependenceSum G =
      neighbourhoodIndependenceSum (G.induce (insert v A : Set V)) +
        neighbourhoodIndependenceSum (G.induce (insert v B : Set V)) := by
  sorry

/-- Lemma 2.7. A connected strong `C₄`-free `P₄`-free graph on at least two vertices
has a universal vertex. Intended proof: Seinsche, then a `C₄` unless one side of the
join is a singleton. -/
theorem lemma_2_7 [Fintype V] [DecidableEq V] (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 4) (hcard : 2 ≤ Fintype.card V) :
    ∃ u, ∀ v, v = u ∨ G.Adj u v := by
  sorry

/-- Lemma 2.10. Proved in the preprint; not an external axiom. -/
theorem lemma_2_10 [Fintype V] [DecidableEq V] (hconn : G.Connected)
    (htri : G.CliqueFree 3) (hC : StrongC4Free G) (hp : IsPkFree G 7)
    (hcut : ∀ v, ¬ IsCutVertex G v) : ¬ HasCliqueCutset G := by
  sorry

/-- A connected finite graph satisfies `p ≥ r + 1` by a geodesic. Used for `c_{C₄} = 0`. -/
theorem inducedPathOrder_ge_radius_succ [Fintype V] [DecidableEq V] (hconn : G.Connected) :
    radiusNat G + 1 ≤ inducedPathOrder G := by
  sorry

/-! ### Section 3 -/

/-- Lemma 3.1. `m` is the number of edges of `G[N(u)]` for a dominating vertex `u`. -/
theorem lemma_3_1 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hr : radiusNat G = 1) :
    ∃ u, (∀ v, v = u ∨ G.Adj u v) ∧
      neighbourhoodIndependenceSum G =
        2 * (Fintype.card V - 1) - edgeCount (G.induce (G.neighborSet u)) ∧
      ell G < 2 ∧
      (inducedPathOrder G : ℚ) ≥ (radiusNat G : ℚ) + ell G := by
  sorry

/-- Lemma 3.2. -/
theorem lemma_3_2 [Fintype V] [DecidableEq V] (hconn : G.Connected) (hC : StrongC4Free G)
    (hr : 2 ≤ radiusNat G) : 4 ≤ inducedPathOrder G := by
  sorry

/-- Lemma 3.3. `h` is the number of vertices with `λ ≥ 3`. -/
theorem lemma_3_3 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 5) :
    neighbourhoodIndependenceSum G ≤
        2 * Fintype.card V -
          (Finset.univ.filter fun v => 3 ≤ lambda G v).card ∧
      neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V := by
  sorry

/-- Lemma 3.4. Dominating induced `C₆`. -/
theorem lemma_3_4 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i)) :
    let W := {v | ∀ i, c i ≠ v}
    (∀ w ∈ W, ∃ i : Fin 6, ∀ j, G.Adj w (c j) ↔ j = i ∨ j = i + 3) ∧
      (W.Pairwise fun w w' =>
        ∀ i, ¬ (G.Adj w (c i) ∧ G.Adj w' (c i))) ∧
      W.Pairwise (¬ G.Adj · ·) ∧
      Nat.card W ≤ 3 ∧
      neighbourhoodIndependenceSum G = 12 + 4 * Nat.card W ∧
      neighbourhoodIndependenceSum G < 3 * Fintype.card V ∧
      (W.Nonempty → radiusNat G ≤ 2) := by
  sorry

/-- Lemma 3.5. -/
theorem lemma_3_5 [Fintype V] [DecidableEq V] (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 6) :
    (∃ v, G.eccent v ≤ 2) ∨ Nonempty (G ≃g cycleGraph 6) := by
  sorry

/-- Extremal graphs of Theorem 3.6, including the orders `2 ≤ n ≤ 6`. -/
def IsP6Extremal {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  match Fintype.card V with
  | 2 => Nonempty (G ≃g k2Graph)
  | 3 => Nonempty (G ≃g p3Graph)
  | 4 => Nonempty (G ≃g p4Graph) ∨ Nonempty (G ≃g clawGraph)
  | 5 => Nonempty (G ≃g cycleGraph 5)
  | 6 => Nonempty (G ≃g cycleGraph 6) ∨ Nonempty (G ≃g c5PlusLeaf)
  | 7 => Nonempty (G ≃g gammaGraph 0)
  | 8 => Nonempty (G ≃g h8Graph)
  | 9 => Nonempty (G ≃g petersenMinus)
  | 10 => Nonempty (G ≃g petersenGraph)
  | n => if 11 ≤ n then Nonempty (G ≃g gammaGraph (n - 7)) else False

/-- Theorem 3.6. `M(n)` is `extremalDensity`. Equality `S = 3n` holds only for Petersen. -/
theorem theorem_3_6 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (hn : 2 ≤ Fintype.card V) :
    ell G ≤ extremalDensity (Fintype.card V) ∧
      (ell G = extremalDensity (Fintype.card V) ↔ IsP6Extremal G) ∧
      neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V ∧
      (neighbourhoodIndependenceSum G = 3 * Fintype.card V ↔
        Nonempty (G ≃g petersenGraph)) := by
  sorry

/-! ### Section 4 -/

/-- Lemma 4.1. An induced dominating `C₈` in radius at least 4 is the whole graph. -/
theorem lemma_4_1 [Fintype V] [DecidableEq V] (hconn : G.Connected) (hC : StrongC4Free G)
    (c : cycleGraph 8 ↪g G) (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i))
    (hr : 4 ≤ radiusNat G) : Nonempty (G ≃g cycleGraph 8) := by
  sorry

/-- Theorem 4.2. -/
theorem theorem_4_2 [Fintype V] [DecidableEq V] :
    (G.Connected ∧ StrongC4Free G ∧ radiusNat G = 4 ∧ inducedPathOrder G = 7) ↔
      Nonempty (G ≃g cycleGraph 8) ∨ IsRadiusFourExtension G := by
  sorry

/-- Lemma 4.3. Off-cycle vertices of an induced path of order at least 3 are endpoints. -/
theorem lemma_4_3 {n : ℕ} (E : RadiusFourExtension G) (f : pathGraph n ↪g G) (hn : 3 ≤ n) :
    ∀ i : Fin n, (∀ j, E.cycleEmb j ≠ f i) → i.val = 0 ∨ i.val = n - 1 := by
  sorry

/-- Corollary 4.4, the mass formula. `C₈` is the case `b = m = 0` outside the extension. -/
theorem corollary_4_4_mass [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hr : radiusNat G = 4)
    (hp : inducedPathOrder G = 7) :
    (Nonempty (G ≃g cycleGraph 8) ∧
        neighbourhoodIndependenceSum G = 2 * Fintype.card V) ∨
      (∃ E : RadiusFourExtension G,
        neighbourhoodIndependenceSum G =
          2 * Fintype.card V - addedCount E - matchingCount E) := by
  sorry

/-- Corollary 4.4, the inequalities. They follow from the mass formula. -/
theorem corollary_4_4 [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hr : radiusNat G = 4)
    (hp : inducedPathOrder G = 7) :
    neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V ∧ ell G ≤ 2 := by
  have hmass := corollary_4_4_mass hconn hC hr hp
  have hS : neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V := by
    rcases hmass with ⟨_, hS⟩ | ⟨_, hS⟩
    · exact le_of_eq hS
    · rw [hS]
      exact (Nat.sub_le _ _).trans (Nat.sub_le _ _)
  refine ⟨hS, ?_⟩
  have : Nonempty V := hconn.nonempty
  have hn : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  rw [ell, div_le_iff₀ hn]
  have hcast : (neighbourhoodIndependenceSum G : ℚ) ≤ 2 * (Fintype.card V : ℚ) := by
    exact_mod_cast hS
  simpa [mul_comm] using hcast

/-- Corollary 4.5. `S = 2n` for `C₈`, and for a 6-cycle with at least one leaf at each vertex. -/
theorem corollary_4_5 [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hr : radiusNat G = 4)
    (hp : inducedPathOrder G = 7) :
    neighbourhoodIndependenceSum G = 2 * Fintype.card V ↔
      Nonempty (G ≃g cycleGraph 8) ∨
        ∃ E : RadiusFourExtension G, addedCount E = 0 ∧ matchingCount E = 0 ∧
          ∀ i, ∃ v ∈ E.attach i, ∀ w ∈ E.attach i, ¬ G.Adj v w := by
  sorry

/-! ### Section 5 -/

/-- Lemma 5.2, the edge table for `𝔉`. Not an external axiom. -/
theorem lemma_5_2 [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : InChenXuFamily G) :
    (Nonempty (G ≃g petersenGraph) ∧ 2 * edgeCount G = 3 * Fintype.card V) ∨
      (¬ Nonempty (G ≃g petersenGraph) ∧
        2 * edgeCount G ≤ 3 * Fintype.card V - 3) := by
  sorry

/-- Lemma 5.3. No induced `P₄` starts at `s`, and `m = e(G[N(s)])`. -/
theorem lemma_5_3 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) {s : V}
    (hp : ∀ n (hn : 4 ≤ n) (f : pathGraph n ↪g G),
      f ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 4) hn⟩ ≠ s) :
    neighbourhoodIndependenceSum G ≤
      2 * (Fintype.card V - 1) - edgeCount (G.induce (G.neighborSet s)) := by
  sorry

/-- Lemma 5.4. Tree stripping down to a core `K₁`, `K₂`, or a member of `𝔉`. -/
theorem lemma_5_4 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (htri : G.CliqueFree 3) (hC : StrongC4Free G) (hp : IsPkFree G 7) :
    ∃ (Q : Set V) (_ : DecidablePred (· ∈ Q)),
      (G.induce Q).Connected ∧ (G.induce Q).CliqueFree 3 ∧ StrongC4Free (G.induce Q) ∧
        IsPkFree (G.induce Q) 7 ∧ ¬ HasCliqueCutset (G.induce Q) ∧
        (Nonempty ((G.induce Q) ≃g (completeGraph (Fin 1))) ∨
          Nonempty ((G.induce Q) ≃g k2Graph) ∨ InChenXuFamily (G.induce Q)) ∧
        edgeCount G = edgeCount (G.induce Q) + (Fintype.card V - Nat.card Q) ∧
        3 * Fintype.card V - 2 * edgeCount G =
          (3 * Nat.card Q - 2 * edgeCount (G.induce Q)) +
            (Fintype.card V - Nat.card Q) := by
  sorry

/-- Theorem 5.5. -/
theorem theorem_5_5 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (htri : G.CliqueFree 3) (hC : StrongC4Free G) (hp : IsPkFree G 7) :
    2 * edgeCount G ≤ 3 * Fintype.card V ∧
      (2 * edgeCount G = 3 * Fintype.card V ↔ Nonempty (G ≃g petersenGraph)) ∧
      (inducedPathOrder G ≤ 6 → GenK 3) ∧
      (G.IsBipartite → inducedPathOrder G ≤ 6 →
        neighbourhoodIndependenceSum G + 1 ≤ 3 * Fintype.card V) := by
  sorry

/-- Canonical leaf placements and the extra `F₂` / `F'₀` models of Theorem 5.6. -/
def IsFnExtremal {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  let n := Fintype.card V
  if 10 ≤ n ∧ n ≤ 14 then
    ∃ a b, a + b = n - 10 ∧ (b = 0 ∨ (1 ≤ a ∧ a ≤ b)) ∧
      Nonempty (G ≃g petersenWithLeaves a b)
  else if n = 15 then
    (∃ a b, a + b = 5 ∧ (b = 0 ∨ (1 ≤ a ∧ a ≤ b)) ∧
        Nonempty (G ≃g petersenWithLeaves a b)) ∨
      Nonempty (G ≃g f2Graph 5)
  else if n = 16 then
    (∃ a b, a + b = 6 ∧ (b = 0 ∨ (1 ≤ a ∧ a ≤ b)) ∧
        Nonempty (G ≃g petersenWithLeaves a b)) ∨
      Nonempty (G ≃g f0pGraph 5) ∨
      Nonempty (G ≃g f2HubLeaf 5) ∨
      Nonempty (G ≃g f2MidLeaf 5)
  else if 17 ≤ n ∧ n % 2 = 1 then
    Nonempty (G ≃g f2Graph ((n - 5) / 2))
  else if 18 ≤ n ∧ n % 2 = 0 then
    let t := (n - 6) / 2
    Nonempty (G ≃g f0pGraph t) ∨
      Nonempty (G ≃g f2HubLeaf t) ∨
      Nonempty (G ≃g f2MidLeaf t)
  else
    False

/-- Distinct canonical Petersen leaf-pairs, and `F₂` not isomorphic to a leaf extension
of Petersen. The remaining pairwise checks among `F'₀`, `F₂`-leaves and Petersen leaves
are part of this `sorry`. -/
theorem theorem_5_6_noniso :
    (∀ a b a' b' : ℕ,
      a + b = a' + b' → (b = 0 ∨ 1 ≤ a ∧ a ≤ b) → (b' = 0 ∨ 1 ≤ a' ∧ a' ≤ b') →
        Nonempty (petersenWithLeaves a b ≃g petersenWithLeaves a' b') → a = a' ∧ b = b') ∧
      (∀ t, 0 < t → ∀ a b, ¬ Nonempty (f2Graph t ≃g petersenWithLeaves a b)) ∧
      (∀ t, 0 < t → ¬ Nonempty (f0pGraph t ≃g f2HubLeaf t)) ∧
      (∀ t, 0 < t → ¬ Nonempty (f0pGraph t ≃g f2MidLeaf t)) ∧
      (∀ t, 0 < t → ¬ Nonempty (f2HubLeaf t ≃g f2MidLeaf t)) := by
  sorry

/-- Theorem 5.6. `f(n)` is `edgeExtremal`. -/
theorem theorem_5_6 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (htri : G.CliqueFree 3) (hC : StrongC4Free G) (hp : IsPkFree G 7)
    (hn : 10 ≤ Fintype.card V) :
    2 * edgeCount G ≤ edgeExtremal (Fintype.card V) ∧
      (2 * edgeCount G = edgeExtremal (Fintype.card V) ↔ IsFnExtremal G) := by
  sorry

/-- Theorem 5.7. At most one triangle. -/
theorem theorem_5_7 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 7) (htri : triangleCount G ≤ 1) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V := by
  sorry

/-- Lemma 5.8(1). A cross edge between two triangles that share a vertex spans a `C₄`. -/
theorem lemma_5_8_share (hC : StrongC4Free G) {u a b c d : V}
    (hab : G.Adj u a) (hbb : G.Adj a b) (hbu : G.Adj b u) (huc : G.Adj u c) (hcd : G.Adj c d)
    (hdu : G.Adj d u) (hne : a ≠ c) (_hb : b ≠ d) :
    ¬ G.Adj a c := by
  sorry

/-- Lemma 5.8(2). Two disjoint triangles span at most one cross edge. -/
theorem lemma_5_8_disjoint (hC : StrongC4Free G) [DecidableRel G.Adj] {a b c x y z : V}
    (htri1 : G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)
    (htri2 : G.Adj x y ∧ G.Adj y z ∧ G.Adj z x)
    (hdisj : ({a, b, c} : Set V) ∩ {x, y, z} = ∅) :
    (if G.Adj a x then 1 else 0) + (if G.Adj a y then 1 else 0) + (if G.Adj a z then 1 else 0) +
        (if G.Adj b x then 1 else 0) + (if G.Adj b y then 1 else 0) +
        (if G.Adj b z then 1 else 0) +
        (if G.Adj c x then 1 else 0) + (if G.Adj c y then 1 else 0) +
        (if G.Adj c z then 1 else 0) ≤
      1 := by
  sorry

/-- Lemma 5.8(4). `d` is the distance between two disjoint triangles, realised by `u` and `v`.
`x` and `z` lie on those triangles and are not the attachment vertices. The induced path
`x, u, …, v, z` has order `d + 3`. Part (3), that the induced subgraph on the two triangles
and a shortest path is exactly those edges, is the reason this path is induced. -/
theorem lemma_5_8_path (hC : StrongC4Free G) {u v x z : V} {d : ℕ}
    (hdist : G.dist u v = d) (hx : x ≠ u ∧ G.Adj x u) (hz : z ≠ v ∧ G.Adj v z)
    (hmin : ∀ u' v', G.Adj x u' → G.Adj u' x → G.Adj z v' → G.Adj v' z → d ≤ G.dist u' v') :
    d + 3 ≤ inducedPathOrder G := by
  sorry

/-- Lemma 5.9. The search hypothesis is `Certificate.four_seed_replay`, still `sorry`.
Closing that replay is not by itself this lemma: the embedding of the four seeds and
the deletion-loss comparison stay in this `sorry`. -/
theorem lemma_5_9 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 7) (htri : 2 ≤ triangleCount G) :
    ∃ v, deletionLoss G v ≤ 3 := by
  sorry

/-- The induced-path order of the Petersen graph. -/
theorem petersen_inducedPathOrder : inducedPathOrder petersenGraph = 5 := by
  sorry

/-- Theorem 5.10. -/
theorem theorem_5_10 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 7) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V ∧
      (neighbourhoodIndependenceSum G = 3 * Fintype.card V ↔
        Nonempty (G ≃g petersenGraph)) := by
  sorry

/-- Theorem 5.11, REAL-133 for `ℓ ≤ 4`. -/
theorem theorem_5_11 [Fintype V] [DecidableEq V] (hell : ell G ≤ 4)
    (hn : 2 ≤ Fintype.card V) (hconn : G.Connected) :
    (inducedPathOrder G : ℚ) ≥ (radiusNat G : ℚ) + ell G ^ cC4 G := by
  sorry

end InducedPaths
