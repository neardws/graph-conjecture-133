module

public import InducedPaths.C6NamedMaps

open scoped SimpleGraph
open SimpleGraph

@[expose] public section
namespace InducedPaths

variable {V : Type*} {G : SimpleGraph V}

/-- The two-apex, empty second-layer row is the named graph H₈. -/
theorem hexTwo_zero_iso_h8 [Fintype V] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (a b : hexFirst c) (hab : a ≠ b)
    (hk : Nat.card (hexFirst c) = 2) (hh : Nat.card (hexSecond c) = 0) :
    Nonempty (G ≃g h8Graph) := by
  obtain ⟨f, hf, ⟨e⟩⟩ := hexShape_iso hconn hC hp c a b hab 2 0 hk hh
  exact ⟨e.trans (hexShapeTwoZeroIsoH8 f hf)⟩

/-- The two-apex, one-hub row is Petersen with one vertex deleted. -/
theorem hexTwo_one_iso_petersenMinus [Fintype V] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (a b : hexFirst c) (hab : a ≠ b)
    (hk : Nat.card (hexFirst c) = 2) (hh : Nat.card (hexSecond c) = 1) :
    Nonempty (G ≃g petersenMinus) := by
  obtain ⟨f, hf, ⟨e⟩⟩ := hexShape_iso hconn hC hp c a b hab 2 1 hk hh
  exact ⟨e.trans (hexShapeTwoOneIsoPetersenMinus f hf)⟩

/-- The three-apex, empty second-layer row is Petersen with one vertex deleted. -/
theorem hexThree_zero_iso_petersenMinus [Fintype V] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (a b : hexFirst c) (hab : a ≠ b)
    (hk : Nat.card (hexFirst c) = 3) (hh : Nat.card (hexSecond c) = 0) :
    Nonempty (G ≃g petersenMinus) := by
  obtain ⟨f, hf, ⟨e⟩⟩ := hexShape_iso hconn hC hp c a b hab 3 0 hk hh
  exact ⟨e.trans (hexShapeThreeZeroIsoPetersenMinus f hf)⟩

end InducedPaths
