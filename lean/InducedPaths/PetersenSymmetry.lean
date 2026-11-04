/-
Actual automorphisms of the Kneser model of the Petersen graph.
The finite transitivity certificates enumerate the 120 permutations of `Fin 5`.
`native_decide` is used explicitly, so these certificates trust Lean's native evaluator.
-/
module

public import InducedPaths.Basic
public import InducedPaths.Graphs
public meta import InducedPaths.Graphs
public import Mathlib.Data.Fintype.Perm
public meta import Mathlib.Data.Fintype.Powerset
public meta import Mathlib.Data.Fintype.Perm

open scoped SimpleGraph

@[expose] public section

namespace InducedPaths

/-- Relabel a two-element subset by a permutation of the five ground points. -/
def petersenPermEquiv (σ : Equiv.Perm (Fin 5)) : PetersenVertex ≃ PetersenVertex where
  toFun s := ⟨s.1.map σ.toEmbedding, by simp [s.2]⟩
  invFun s := ⟨s.1.map σ.symm.toEmbedding, by simp [s.2]⟩
  left_inv s := by
    apply Subtype.ext
    simp [Finset.map_map]
  right_inv s := by
    apply Subtype.ext
    simp [Finset.map_map]

/-- Ground-set permutations induce genuine Petersen graph automorphisms. -/
def petersenPermIso (σ : Equiv.Perm (Fin 5)) : petersenGraph ≃g petersenGraph where
  toEquiv := petersenPermEquiv σ
  map_rel_iff' := by
    intro s t
    exact Finset.disjoint_map σ.toEmbedding

/-- Finite certificate: some ground permutation takes every directed edge to the hubs.
This checks only 120 ground permutations, not permutations of the ten vertices. -/
theorem petersen_ground_edge_certificate :
    ∀ u v : PetersenVertex, petersenGraph.Adj u v →
      ∃ σ : Equiv.Perm (Fin 5),
        petersenPermEquiv σ u = petersenHub ∧
        petersenPermEquiv σ v = petersenHubB := by
  native_decide

/-- Finite certificate for vertex transitivity, using the same ground action. -/
theorem petersen_ground_vertex_certificate :
    ∀ u : PetersenVertex, ∃ σ : Equiv.Perm (Fin 5),
      petersenPermEquiv σ u = petersenHub := by
  native_decide

/-- Directed-edge transitivity in the actual graph-isomorphism type. -/
theorem petersen_edge_transitive (u v : PetersenVertex) (h : petersenGraph.Adj u v) :
    ∃ e : petersenGraph ≃g petersenGraph,
      e u = petersenHub ∧ e v = petersenHubB := by
  obtain ⟨σ, hu, hv⟩ := petersen_ground_edge_certificate u v h
  exact ⟨petersenPermIso σ, hu, hv⟩

/-- Vertex transitivity in the actual graph-isomorphism type. -/
theorem petersen_vertex_transitive (u : PetersenVertex) :
    ∃ e : petersenGraph ≃g petersenGraph, e u = petersenHub := by
  obtain ⟨σ, hu⟩ := petersen_ground_vertex_certificate u
  exact ⟨petersenPermIso σ, hu⟩

end InducedPaths
