/- The bipartite final clause of Theorem 5.5, independent of GEN₃. -/
module

public import InducedPaths.TriangleFreeMass

open SimpleGraph

@[expose] public section
namespace InducedPaths

/-- Bipartiteness pulls back along every graph homomorphism. -/
theorem isBipartite_of_hom {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (hb : H.IsBipartite) : G.IsBipartite :=
  hb.of_hom f

/-- In particular, bipartiteness pulls back along an induced embedding. -/
theorem isBipartite_of_embedding {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ↪g H) (hb : H.IsBipartite) : G.IsBipartite :=
  isBipartite_of_hom f.toHom hb

/-- Bipartiteness is invariant under graph isomorphism. -/
theorem isBipartite_iff_of_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : G.IsBipartite ↔ H.IsBipartite :=
  ⟨isBipartite_of_hom e.symm.toHom, isBipartite_of_hom e.toHom⟩

/-- An explicit pentagon in the disjoint-pair model of the Petersen graph. -/
def petersenPentagonVertex (i : Fin 5) : PetersenVertex :=
  ![⟨{0, 1}, by decide⟩, ⟨{2, 3}, by decide⟩, ⟨{0, 4}, by decide⟩,
    ⟨{1, 2}, by decide⟩, ⟨{3, 4}, by decide⟩] i

/-- The displayed five pairs form an induced `C₅`, not merely a closed walk. -/
def petersenPentagonEmbedding : cycleGraph 5 ↪g petersenGraph where
  toFun := petersenPentagonVertex
  inj' := by decide
  map_rel_iff' := by decide

/-- The elementary odd-cycle certificate: no two-coloring of a pentagon exists. -/
theorem cycle5_not_isBipartite : ¬ (cycleGraph 5).IsBipartite := by
  rintro ⟨c⟩
  have h01 := c.valid (show (cycleGraph 5).Adj 0 1 by decide)
  have h12 := c.valid (show (cycleGraph 5).Adj 1 2 by decide)
  have h23 := c.valid (show (cycleGraph 5).Adj 2 3 by decide)
  have h34 := c.valid (show (cycleGraph 5).Adj 3 4 by decide)
  have h40 := c.valid (show (cycleGraph 5).Adj 4 0 by decide)
  omega

/-- Petersen is excluded from the bipartite equality case by its explicit pentagon. -/
theorem petersen_not_isBipartite : ¬ petersenGraph.IsBipartite := by
  intro hb
  exact cycle5_not_isBipartite (isBipartite_of_embedding petersenPentagonEmbedding hb)

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The exact final clause of Theorem 5.5: the triangle-free bipartite bound is strict. -/
theorem bipartite_triangleFree_mass_strict (hconn : G.Connected) (htri : G.CliqueFree 3)
    (hC : StrongC4Free G) (hp : IsPkFree G 7) (hb : G.IsBipartite) :
    neighbourhoodIndependenceSum G + 1 ≤ 3 * Fintype.card V := by
  obtain ⟨hle, heq⟩ := triangleFree_mass_bound hconn htri hC hp
  have hne : neighbourhoodIndependenceSum G ≠ 3 * Fintype.card V := by
    intro he
    obtain ⟨e⟩ := heq.mp he
    exact petersen_not_isBipartite ((isBipartite_iff_of_iso e).mp hb)
  omega

end InducedPaths
