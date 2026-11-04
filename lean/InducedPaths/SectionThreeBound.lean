/-
The global density-three conclusion of Section 3, separated from the sharper
order-by-order extremal envelope and its equality classification.
-/
module

public import InducedPaths.C6Classification
public import InducedPaths.C5Mass
public import InducedPaths.ChordalStructure
public import InducedPaths.CanonicalMass

open SimpleGraph

@[expose] public section
namespace InducedPaths

/-- Every connected strong-C4-free P6-free graph has mass at most three times
its order; the equality case is exactly the Petersen graph. -/
theorem section_three_mass_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (hn : 2 ≤ Fintype.card V) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V ∧
      (neighbourhoodIndependenceSum G = 3 * Fintype.card V ↔
        Nonempty (G ≃g petersenGraph)) := by
  classical
  have hb : neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V ∧
      (neighbourhoodIndependenceSum G = 3 * Fintype.card V →
        Nonempty (G ≃g petersenGraph)) := by
    by_cases h6 : cycleGraph 6 ⊴ G
    · obtain ⟨c⟩ := h6
      exact hex_mass_le_three hconn hC hp c
    · by_cases h5 : cycleGraph 5 ⊴ G
      · obtain ⟨c⟩ := h5
        have hS := pentagon_mass_le hconn hC hp h6 c
        exact ⟨by omega, fun he => by omega⟩
      · have hS := chordal_branch_mass_bound hC hp h5 h6
        exact ⟨by omega, fun he => by omega⟩
  exact ⟨hb.1, hb.2, mass_eq_three_card_of_iso_petersen⟩

end InducedPaths
