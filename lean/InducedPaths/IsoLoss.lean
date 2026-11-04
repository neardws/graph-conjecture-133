/-
Transport of neighbourhood mass and deletion loss under graph isomorphisms.
-/
module

public import InducedPaths.Basic

open Finset SimpleGraph

@[expose] public section

namespace InducedPaths

/-- Neighbourhood independence is invariant under graph isomorphisms. -/
theorem lambda_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (v : V) : lambda G v = lambda H (e v) := by
  let f : G.neighborSet v ≃ H.neighborSet (e v) :=
    { toFun := fun x => ⟨e x.val, e.map_rel_iff.mpr x.property⟩
      invFun := fun y => ⟨e.symm y.val, by
        have hy := e.symm.map_rel_iff.mpr y.property
        simpa using hy⟩
      left_inv := fun x => Subtype.ext (e.left_inv x.val)
      right_inv := fun y => Subtype.ext (e.right_inv y.val) }
  let iso : G.induce (G.neighborSet v) ≃g H.induce (H.neighborSet (e v)) :=
    { toEquiv := f
      map_rel_iff' := by intro x y; exact e.map_rel_iff }
  exact indepNum_iso iso

/-- Total neighbourhood independence is invariant under graph isomorphisms. -/
theorem neighbourhoodIndependenceSum_iso {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    neighbourhoodIndependenceSum G = neighbourhoodIndependenceSum H := by
  unfold neighbourhoodIndependenceSum
  exact Fintype.sum_equiv e.toEquiv _ _ (fun v => lambda_iso e v)

/-- Deletion loss is invariant under graph isomorphisms, without a `C₄` condition. -/
theorem deletionLoss_iso {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) (v : V) :
    deletionLoss G v = deletionLoss H (e v) := by
  classical
  let f : ({v}ᶜ : Set V) ≃ ({e v}ᶜ : Set W) :=
    { toFun := fun x => ⟨e x.val, by simpa using fun h => x.property (e.injective h)⟩
      invFun := fun y => ⟨e.symm y.val, by
        intro hy
        have heq : e.symm y.val = v := by simpa using hy
        have : y.val = e v := by simpa using congrArg e heq
        exact y.property (by simpa using this)⟩
      left_inv := fun x => Subtype.ext (e.left_inv x.val)
      right_inv := fun y => Subtype.ext (e.right_inv y.val) }
  let iso : G.induce ({v}ᶜ : Set V) ≃g H.induce ({e v}ᶜ : Set W) :=
    { toEquiv := f
      map_rel_iff' := by intro x y; exact e.map_rel_iff }
  rw [deletionLoss, deletionLoss, neighbourhoodIndependenceSum_iso e,
    neighbourhoodIndependenceSum_iso iso]

end InducedPaths
