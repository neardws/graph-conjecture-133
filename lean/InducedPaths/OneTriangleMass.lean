/- Concrete unique-triangle facts and mass arithmetic for Theorem 5.7.
This module deliberately does not import StatementsCore or the Chen–Xu core. -/
module

public import InducedPaths.Basic

open Finset SimpleGraph

@[expose] public section
namespace InducedPaths

variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- In a graph with at most one triangle, every triangle is the designated one. -/
theorem oneTriangle_clique_eq (hT : triangleCount G ≤ 1)
    {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : G.Adj u w)
    {s : Finset V} (hs : G.IsNClique 3 s) : s = {v, u, w} := by
  have hsub : (G.cliqueFinset 3 : Set (Finset V)).Subsingleton := by
    exact Finset.card_le_one.mp hT
  exact hsub (mem_cliqueFinset_iff.mpr hs)
    (mem_cliqueFinset_iff.mpr (is3Clique_triple_iff.mpr ⟨hvu, hvw, huw⟩))

/-- The unique common neighbour along the designated triangle edge. This uses
only the at-most-one-triangle hypothesis, not strong C4-freeness. -/
theorem oneTriangle_common_neighbor (hT : triangleCount G ≤ 1)
    {v u w x : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hvx : G.Adj v x) (hux : G.Adj u x) : x = w := by
  have heq := oneTriangle_clique_eq hT hvu hvw huw
    (is3Clique_triple_iff.mpr ⟨hvu, hvx, hux⟩)
  have hx : x ∈ ({v, u, w} : Finset V) := by rw [← heq]; simp
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with hx | hx | hx
  · exact (hvx.ne hx.symm).elim
  · exact (hux.ne hx.symm).elim
  · exact hx

/-- A triangle vertex lies in the only triangle. -/
theorem oneTriangle_trianglesAt_eq_one (hT : triangleCount G ≤ 1)
    {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : G.Adj u w) :
    trianglesAt G v = 1 := by
  have heq : G.cliqueFinset 3 = {{v, u, w}} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨mem_cliqueFinset_iff.mpr (is3Clique_triple_iff.mpr ⟨hvu, hvw, huw⟩), ?_⟩
    intro s hs
    exact oneTriangle_clique_eq hT hvu hvw huw (mem_cliqueFinset_iff.mp hs)
  have hpos : 0 < trianglesAt G v := by
    apply Finset.card_pos.mpr
    exact ⟨{v, u, w}, mem_filter.mpr
      ⟨mem_cliqueFinset_iff.mpr (is3Clique_triple_iff.mpr ⟨hvu, hvw, huw⟩), by simp⟩⟩
  have hle : trianglesAt G v ≤ triangleCount G := Finset.card_le_card (filter_subset _ _)
  omega

/-- Deleting any vertex of the unique triangle destroys all triangles. -/
theorem oneTriangle_delete_triangleCount (hT : triangleCount G ≤ 1)
    {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : G.Adj u w) :
    triangleCount (G.induce {v}ᶜ) = 0 := by
  have h := triangleCount_induce_compl_add (G := G) v
  have ht := oneTriangle_trianglesAt_eq_one hT hvu hvw huw
  omega

/-- Vertices outside the core and the deleted vertex which are not adjacent
 to the deleted triangle vertex (the paper's set counted by `c`). -/
noncomputable def oneTriangleRemainder (G : SimpleGraph V) (Q : Finset V) (v : V) : Finset V := by
  classical
  exact univ.filter fun x => x ≠ v ∧ x ∉ Q ∧ ¬ G.Adj v x

/-- Degree inside a vertex set, without introducing a subtype graph. -/
noncomputable def oneTriangleCoreNeighbors (G : SimpleGraph V) (Q : Finset V) (u : V) : Finset V := by
  classical
  exact G.neighborFinset u ∩ Q

/-- Outside the other two triangle vertices, every neighbour of a triangle
 vertex either belongs to the core or to the non-neighbour remainder. -/
theorem oneTriangle_neighbor_cover (hT : triangleCount G ≤ 1)
    {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : G.Adj u w)
    (Q : Finset V) :
    G.neighborFinset u ⊆ insert v (insert w
      (oneTriangleCoreNeighbors G Q u ∪ oneTriangleRemainder G Q v)) := by
  classical
  intro x hx
  by_cases hxv : x = v
  · simp [hxv]
  by_cases hxw : x = w
  · simp [hxw]
  apply mem_insert_of_mem
  apply mem_insert_of_mem
  by_cases hxQ : x ∈ Q
  · apply mem_union_left
    simpa only [oneTriangleCoreNeighbors, mem_inter, mem_neighborFinset] using
      (show G.Adj u x ∧ x ∈ Q from ⟨by simpa using hx, hxQ⟩)
  · apply mem_union_right
    simp only [oneTriangleRemainder, mem_filter, mem_univ, true_and]
    refine ⟨hxv, hxQ, ?_⟩
    intro hvx
    exact hxw (oneTriangle_common_neighbor hT hvu hvw huw hvx
      (by simpa using hx))

/-- The outside-core case: the rooted-tree invariant is needed only as the
concrete bound of one on the number of core neighbours. -/
theorem oneTriangle_degree_le_remainder_add_three (hT : triangleCount G ≤ 1)
    {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : G.Adj u w)
    (Q : Finset V) (hattach : (oneTriangleCoreNeighbors G Q u).card ≤ 1) :
    G.degree u ≤ (oneTriangleRemainder G Q v).card + 3 := by
  have hcov := card_le_card (oneTriangle_neighbor_cover hT hvu hvw huw Q)
  have h1 := card_insert_le v (insert w
    (oneTriangleCoreNeighbors G Q u ∪ oneTriangleRemainder G Q v))
  have h2 := card_insert_le w
    (oneTriangleCoreNeighbors G Q u ∪ oneTriangleRemainder G Q v)
  have h3 := card_union_le (oneTriangleCoreNeighbors G Q u) (oneTriangleRemainder G Q v)
  rw [card_neighborFinset_eq_degree] at hcov
  omega

/-- If the other triangle vertex is in the core, no exceptional outside-core
neighbour is needed. This is the second degree estimate of Theorem 5.7. -/
theorem oneTriangle_degree_le_core_add_remainder (hT : triangleCount G ≤ 1)
    {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : G.Adj u w)
    (Q : Finset V) (hwQ : w ∈ Q) :
    G.degree u ≤ 1 + (oneTriangleRemainder G Q v).card +
      (oneTriangleCoreNeighbors G Q u).card := by
  have hcov : G.neighborFinset u ⊆ insert v
      (oneTriangleCoreNeighbors G Q u ∪ oneTriangleRemainder G Q v) := by
    intro x hx
    have hc := oneTriangle_neighbor_cover hT hvu hvw huw Q hx
    rcases mem_insert.mp hc with hc | hc
    · exact mem_insert.mpr (Or.inl hc)
    rcases mem_insert.mp hc with hc | hc
    · subst x
      exact mem_insert_of_mem (mem_union_left _ (mem_inter.mpr ⟨by simpa using huw, hwQ⟩))
    · exact mem_insert_of_mem hc
  have h := card_le_card hcov
  have h1 := card_insert_le v
    (oneTriangleCoreNeighbors G Q u ∪ oneTriangleRemainder G Q v)
  have h2 := card_union_le (oneTriangleCoreNeighbors G Q u) (oneTriangleRemainder G Q v)
  rw [card_neighborFinset_eq_degree] at h
  omega

/-- Natural-number formulation of the final deficit calculation. The two
alternatives are precisely the outside-core and inside-core triangle cases.
All subtraction in this interface is avoided. -/
theorem oneTriangle_mass_arithmetic
    {S n e eH eQ d h t a c eta k : ℕ}
    (hS : S + 3 = 2 * e) (he : e = eH + d)
    (hstrip : eH = eQ + t) (hdef : 2 * eQ + eta = 3 * h)
    (hn : n = h + t + 1) (ht : t + a = d + c)
    (hcases : (d ≤ c + 3 ∧ a ≤ eta + 3) ∨
      (d ≤ 1 + c + k ∧ a + k ≤ eta + 5)) : S ≤ 3 * n := by
  rcases hcases with hcases | hcases <;> omega

/-- Selected neighbours of an outside vertex have disjoint open
neighbourhoods in an induced core. This is the exact interface needed by the
finite Chen–Xu attachment bounds. -/
theorem oneTriangle_core_neighborSets_disjoint (hC : StrongC4Free G)
    (Q : Set V) {v : V} (hv : v ∉ Q) {x y : Q}
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hxy : x ≠ y) :
    Disjoint ((G.induce Q).neighborSet x) ((G.induce Q).neighborSet y) := by
  apply Set.disjoint_left.mpr
  intro z hxz hyz
  have hne : (x : V) ≠ y := fun h => hxy (Subtype.ext h)
  have hsub := commonNeighbors_subsingleton hC hne
  have hvcommon : v ∈ G.commonNeighbors x y := by
    exact ⟨hvx.symm, hvy.symm⟩
  have hzcommon : (z : V) ∈ G.commonNeighbors x y := by
    exact ⟨hxz, hyz⟩
  have heq : v = z := hsub hvcommon hzcommon
  exact hv (heq ▸ z.property)

/-- Core degrees coincide with ambient neighbour counts restricted to the
core, so attachment-bound statements need not depend on ambient subtypes. -/
theorem oneTriangle_core_degree (Q : Finset V) {u : V} (hu : u ∈ Q) :
    (G.induce (Q : Set V)).degree ⟨u, hu⟩ =
      (oneTriangleCoreNeighbors G Q u).card := by
  classical
  rw [← card_neighborSet_eq_degree]
  let e : (G.induce (Q : Set V)).neighborSet ⟨u, hu⟩ ≃
      {x // x ∈ oneTriangleCoreNeighbors G Q u} :=
    { toFun := fun x => ⟨x.val.val, by
        simpa only [oneTriangleCoreNeighbors, mem_inter, mem_neighborFinset] using
          (show G.Adj u x.val.val ∧ x.val.val ∈ Q from ⟨x.property, x.val.property⟩)⟩
      invFun := fun x => ⟨⟨x.val, by
        have hx := x.property
        simp only [oneTriangleCoreNeighbors, mem_inter, mem_neighborFinset] at hx
        exact hx.2⟩, by
          have hx := x.property
          simp only [oneTriangleCoreNeighbors, mem_inter, mem_neighborFinset] at hx
          exact hx.1⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => Subtype.ext rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

/-- Selected core vertices adjacent to the deleted vertex, as a finset on
 the core's own vertex type. -/
noncomputable def oneTriangleSelected (Q : Finset V) (v : V) : Finset (Q : Set V) := by
  classical
  exact univ.filter fun x => G.Adj v x

/-- The selected-core cardinality is the ambient count `a`. -/
theorem oneTriangleSelected_card (Q : Finset V) (v : V) :
    (oneTriangleSelected (G := G) Q v).card =
      (oneTriangleCoreNeighbors G Q v).card := by
  classical
  let e : {x // x ∈ oneTriangleSelected (G := G) Q v} ≃
      {x // x ∈ oneTriangleCoreNeighbors G Q v} :=
    { toFun := fun x => ⟨x.val.val, by
        have hx : G.Adj v x.val := by
          simpa only [oneTriangleSelected, mem_filter, mem_univ, true_and] using x.property
        simpa only [oneTriangleCoreNeighbors, mem_inter, mem_neighborFinset] using
          (show G.Adj v x.val.val ∧ x.val.val ∈ Q from ⟨hx, x.val.property⟩)⟩
      invFun := fun x => ⟨⟨x.val, by
        have hx := x.property
        simp only [oneTriangleCoreNeighbors, mem_inter, mem_neighborFinset] at hx
        exact hx.2⟩, by
          have hx := x.property
          simp only [oneTriangleCoreNeighbors, mem_inter, mem_neighborFinset] at hx
          simpa only [oneTriangleSelected, mem_filter, mem_univ, true_and] using hx.1⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => Subtype.ext rfl }
  simpa only [Fintype.card_coe] using Fintype.card_congr e

/-- A nonzero triangle count supplies a triangle, oriented so that its
first vertex has minimum degree among its three vertices. -/
theorem oneTriangle_exists_min_degree (hT : triangleCount G ≠ 0) :
    ∃ v u w : V, G.Adj v u ∧ G.Adj v w ∧ G.Adj u w ∧
      G.degree v ≤ G.degree u ∧ G.degree v ≤ G.degree w := by
  have hnon : (G.cliqueFinset 3).Nonempty := Finset.card_ne_zero.mp hT
  obtain ⟨s, hs⟩ := hnon
  obtain ⟨v, u, w, hvu, hvw, huw, _⟩ :=
    is3Clique_iff.mp (mem_cliqueFinset_iff.mp hs)
  by_cases hvu' : G.degree v ≤ G.degree u
  · by_cases hvw' : G.degree v ≤ G.degree w
    · exact ⟨v, u, w, hvu, hvw, huw, hvu', hvw'⟩
    · exact ⟨w, v, u, hvw.symm, huw.symm, hvu, by omega, by omega⟩
  · by_cases huw' : G.degree u ≤ G.degree w
    · exact ⟨u, v, w, hvu.symm, huw, hvw, by omega, huw'⟩
    · exact ⟨w, v, u, hvw.symm, huw.symm, hvu, by omega, by omega⟩

/-- Exact cardinality bookkeeping for the paper's `t = d - a + c`.
Here `t` counts all vertices outside the core and the deleted vertex. -/
theorem oneTriangle_attachment_partition (Q : Finset V) (v : V) :
    (univ \ (insert v Q)).card + (oneTriangleCoreNeighbors G Q v).card =
      G.degree v + (oneTriangleRemainder G Q v).card := by
  classical
  let O : Finset V := univ \ insert v Q
  let N := G.neighborFinset v
  have hN : N \ Q ⊆ O := by
    intro x hx
    rcases mem_sdiff.mp hx with ⟨hxN, hxQ⟩
    simp only [O, mem_sdiff, mem_univ, true_and, mem_insert, not_or]
    exact ⟨(show G.Adj v x by simpa [N] using hxN).ne.symm, hxQ⟩
  have hR : O \ (N \ Q) = oneTriangleRemainder G Q v := by
    ext x
    simp only [O, N, oneTriangleRemainder, mem_sdiff, mem_univ, true_and,
      mem_insert, mem_filter, mem_neighborFinset]
    tauto
  have hsplit := card_sdiff_add_card_eq_card hN
  rw [hR] at hsplit
  have hNsplit := card_sdiff_add_card_inter N Q
  have hdegree : N.card = G.degree v := by simp [N]
  have ha : (N ∩ Q).card = (oneTriangleCoreNeighbors G Q v).card := by
    congr 1
    ext x
    simp [N, oneTriangleCoreNeighbors]
  change O.card + _ = _
  omega

/-- Assembly of the one-triangle bound from a concrete core witness. The
classification-dependent inputs are exactly `hcore`, `hedge`, and `hattach`;
all unique-triangle degree bookkeeping is discharged here. The parameters
`eQ`, `eta`, `t`, `a` are the paper's edge count, deficit, number of attached
vertices, and number of neighbours of the deleted vertex in the core. -/
theorem oneTriangle_mass_of_core_data
    (hC : StrongC4Free G) (hT : triangleCount G ≤ 1)
    {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hdu : G.degree v ≤ G.degree u) (hdw : G.degree v ≤ G.degree w)
    (Q : Finset V) (eQ eta t a : ℕ)
    (hstrip : edgeCount (G.induce {v}ᶜ) = eQ + t)
    (hdef : 2 * eQ + eta = 3 * Q.card)
    (hn : Fintype.card V = Q.card + t + 1)
    (ht : t + a = G.degree v + (oneTriangleRemainder G Q v).card)
    (hcore : a ≤ eta + 3)
    (hedge : ∀ x ∈ Q, ∀ y ∈ Q, G.Adj v x → G.Adj v y → G.Adj x y →
      a + min (oneTriangleCoreNeighbors G Q x).card
        (oneTriangleCoreNeighbors G Q y).card ≤ eta + 5)
    (hattach : ∀ x, x ≠ v → x ∉ Q →
      (oneTriangleCoreNeighbors G Q x).card ≤ 1) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V := by
  have htv := oneTriangle_trianglesAt_eq_one hT hvu hvw huw
  have htle : trianglesAt G v ≤ triangleCount G :=
    Finset.card_le_card (filter_subset _ _)
  have hTeq : triangleCount G = 1 := by omega
  have hSi := strongC4Free_S_identity hC
  have hlow := three_mul_triangleCount_le_two_edge hC
  have hS : neighbourhoodIndependenceSum G + 3 = 2 * edgeCount G := by
    rw [hTeq] at hSi hlow
    omega
  have he := edgeCount_induce_compl_add (G := G) v
  apply oneTriangle_mass_arithmetic hS he.symm hstrip hdef hn ht
    (k := min (oneTriangleCoreNeighbors G Q u).card
      (oneTriangleCoreNeighbors G Q w).card)
  by_cases huQ : u ∈ Q
  · by_cases hwQ : w ∈ Q
    · right
      refine ⟨?_, hedge u huQ w hwQ hvu hvw huw⟩
      have hu := oneTriangle_degree_le_core_add_remainder hT hvu hvw huw Q hwQ
      have hw := oneTriangle_degree_le_core_add_remainder hT hvw hvu huw.symm Q huQ
      omega
    · left
      refine ⟨?_, hcore⟩
      have hw := oneTriangle_degree_le_remainder_add_three hT hvw hvu huw.symm Q
        (hattach w hvw.ne.symm hwQ)
      omega
  · left
    refine ⟨?_, hcore⟩
    have hu := oneTriangle_degree_le_remainder_add_three hT hvu hvw huw Q
      (hattach u hvu.ne.symm huQ)
    omega

end InducedPaths
