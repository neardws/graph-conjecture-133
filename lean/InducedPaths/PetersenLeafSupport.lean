module
public import InducedPaths.Basic
public import InducedPaths.Graphs
public import InducedPaths.PetersenPaths

open Finset SimpleGraph
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

@[expose] public section
namespace InducedPaths
namespace SectionFiveGlobal

/-- A degree-one vertex has no neighbour other than its specified neighbour. -/
lemma leaf_neighbor_unique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x a z : V}
    (hx : G.degree x = 1) (ha : G.Adj x a) (hz : G.Adj x z) : z = a := by
  by_contra hne
  have h := pair_degree_ge_two G hz ha hne
  omega

/-- The supports of exterior leaves on a Petersen core form a clique in a P7-free graph. -/
theorem petersen_leaf_support_adj {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : petersenGraph ↪g G) (hfree : IsPkFree G 7)
    (a b : PetersenVertex) (hab : a ≠ b)
    (hx : ∃ x, x ∉ Set.range e ∧ G.Adj x (e a) ∧ G.degree x = 1)
    (hy : ∃ y, y ∉ Set.range e ∧ G.Adj y (e b) ∧ G.degree y = 1) :
    G.Adj (e a) (e b) := by
  by_contra hn
  have hn' : ¬ petersenGraph.Adj a b := fun h => hn (e.map_adj_iff.mpr h)
  obtain ⟨c, d, z, hc⟩ := petersen_nonedge_P5 a b hab hn'
  obtain ⟨x, hxout, hxa, hxd⟩ := hx
  obtain ⟨y, hyout, hyb, hyd⟩ := hy
  let f : Fin 5 → V := fun i => e (five a c d z b i)
  have fi : Function.Injective f := e.injective.comp hc.1
  have fa : f 0 = e a := by simp [f, five]
  have fb : f 4 = e b := by simp [f, five]
  have fx : ∀ i, x ≠ f i := fun i h => hxout ⟨_, h.symm⟩
  have fy : ∀ i, y ≠ f i := fun i h => hyout ⟨_, h.symm⟩
  have hxy : x ≠ y := by
    intro h
    have heq := leaf_neighbor_unique G hxd hxa (h ▸ hyb)
    exact hab (e.injective heq.symm)
  have ax : ∀ i, G.Adj x (f i) ↔ i = 0 := by
    intro i
    constructor
    · intro h
      apply fi
      exact (leaf_neighbor_unique G hxd hxa h).trans fa.symm
    · rintro rfl
      simpa only [fa] using hxa
  have ay : ∀ i, G.Adj y (f i) ↔ i = 4 := by
    intro i
    constructor
    · intro h
      apply fi
      exact (leaf_neighbor_unique G hyd hyb h).trans fb.symm
    · rintro rfl
      simpa only [fb] using hyb
  have nxy : ¬ G.Adj x y := by
    intro h
    have hy := leaf_neighbor_unique G hxd hxa h
    exact hyout ⟨a, hy.symm⟩
  have af : ∀ i j, G.Adj (f i) (f j) ↔ (pathGraph 5).Adj i j := by
    intro i j
    exact e.map_adj_iff.trans (hc.2 i j)
  let g : Fin 7 → V := ![x, f 0, f 1, f 2, f 3, f 4, y]
  have gi : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [g] at hij ⊢ <;>
      first | exact False.elim (hxy hij) | exact False.elim (hxy hij.symm) |
        exact False.elim (fx _ hij) | exact False.elim (fx _ hij.symm) |
        exact False.elim (fy _ hij) | exact False.elim (fy _ hij.symm) |
        exact False.elim (by have := fi hij; contradiction)
  have ga : ∀ i j, G.Adj (g i) (g j) ↔ (pathGraph 7).Adj i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [g, ax, ay, af, nxy, G.adj_comm, pathGraph_adj]
  exact hfree (PathCertificate.isIndContained ⟨gi, ga⟩)

end SectionFiveGlobal
end InducedPaths
