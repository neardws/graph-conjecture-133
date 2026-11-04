/-
The local elimination estimate used in the chordal branch of Theorem 3.6.
This file does not assert the chordal simplicial-vertex theorem or the full
extremal classification. Its hypothesis is explicitly that the neighbourhood
of the vertex being deleted is a clique.
-/
module

public import InducedPaths.Basic

open Finset SimpleGraph

@[expose] public section
namespace InducedPaths

/-- The local deletion identity of Lemma 2.2, factored below StatementsCore
so that simplicial elimination can be used in the statements module. -/
lemma deletionLoss_eq_degree_sub_trianglesAt {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hC : StrongC4Free G) (v : V) :
    deletionLoss G v = 2 * G.degree v - 3 * trianglesAt G v := by
  have hS := strongC4Free_S_identity hC
  have hC' : StrongC4Free (G.induce ({v}ᶜ : Set V)) :=
    strongC4Free_induce (s := ({v}ᶜ : Set V)) hC
  have hS' := strongC4Free_S_identity hC'
  have he := edgeCount_induce_compl_add (G := G) v
  have ht := triangleCount_induce_compl_add (G := G) v
  have h3 := three_mul_trianglesAt_le_two_degree hC v
  have h3' := three_mul_triangleCount_le_two_edge hC'
  have hmain : neighbourhoodIndependenceSum G =
      neighbourhoodIndependenceSum (G.induce ({v}ᶜ : Set V)) +
        (2 * G.degree v - 3 * trianglesAt G v) := by
    omega
  rw [deletionLoss, hmain]
  exact Nat.add_sub_cancel_left _ _

/-- A vertex with clique neighbourhood has neighbourhood independence at most one,
including an isolated vertex, whose neighbourhood independence is zero. -/
lemma lambda_le_one_of_neighbor_clique {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (v : V) (hcl : G.IsClique (G.neighborSet v)) :
    lambda G v ≤ 1 := by
  classical
  let H := G.induce (G.neighborSet v)
  obtain ⟨s, hs⟩ := H.exists_isNIndepSet_indepNum
  have hc : s.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hne
    exact hs.isIndepSet hx hy hne
      (show H.Adj x y from hcl x.property y.property (Subtype.coe_ne_coe.mpr hne))
  have he := hs.card_eq
  change H.indepNum ≤ 1
  omega

/-- The simplicial deletion step in the chordal branch of Theorem 3.6.
No assertion that a simplicial vertex exists is assumed implicitly. -/
lemma simplicial_deletionLoss_le_two {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hC : StrongC4Free G)
    (v : V) (hcl : G.IsClique (G.neighborSet v)) : deletionLoss G v ≤ 2 := by
  have hlam := lambda_le_one_of_neighbor_clique v hcl
  have hL := deletionLoss_eq_degree_sub_trianglesAt hC v
  have hsum := lambda_add_trianglesAt hC v
  have ht := two_mul_trianglesAt_le_degree hC v
  omega

/-- The corresponding additive estimate, avoiding truncated subtraction. -/
lemma simplicial_mass_le_deleted_add_two {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hC : StrongC4Free G)
    (v : V) (hcl : G.IsClique (G.neighborSet v)) :
    neighbourhoodIndependenceSum G ≤
      neighbourhoodIndependenceSum (G.induce ({v}ᶜ : Set V)) + 2 := by
  have h := simplicial_deletionLoss_le_two hC v hcl
  unfold deletionLoss at h
  omega

end InducedPaths
