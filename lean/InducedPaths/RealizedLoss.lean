/-
The deletion-loss step for a mask graph realized as an induced subgraph.
-/
module

public import InducedPaths.StatementsCore
public import InducedPaths.ExtensionSoundness
public import InducedPaths.IsoLoss

open SimpleGraph

@[expose] public section

namespace InducedPaths.Certificate

/-- An ambient realization enforces symmetry and looplessness of in-range masks. -/
theorem Realizes.wellFormed {V : Type*} {G : SimpleGraph V} {g : List ℕ}
    (r : Realizes G g) : WellFormed g := by
  refine ⟨?_, ?_⟩
  · intro i j
    apply Bool.eq_iff_iff.mpr
    rw [← r.adj_iff, ← r.adj_iff, G.adj_comm]
  · intro i
    apply Bool.eq_false_iff.mpr
    intro h
    exact G.irrefl ((r.adj_iff i i).mpr h)

/-- The decoded mask graph is isomorphic to its actual induced image. -/
noncomputable def Realizes.imageIso {V : Type*} {G : SimpleGraph V} {g : List ℕ}
    (r : Realizes G g) : toSimpleGraph g r.wellFormed ≃g G.induce (Set.range r.vertices) := by
  let f : Fin g.length ≃ Set.range r.vertices :=
    Equiv.ofBijective (fun i => (⟨r.vertices i, ⟨i, rfl⟩⟩ : Set.range r.vertices)) (by
      constructor
      · intro i j h; exact r.vertices.injective (congrArg Subtype.val h)
      · rintro ⟨x, i, rfl⟩; exact ⟨i, rfl⟩)
  exact { toEquiv := f, map_rel_iff' := by intro i j; exact r.adj_iff i j }

/-- A deficient mask vertex has a new ambient neighbour if all ambient losses
are at least four. No monotonicity of deletion loss is assumed. -/
theorem Realizes.exists_neighbor_outside {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {g : List ℕ}
    (r : Realizes G g) (hG : StrongC4Free G)
    (hlarge : ∀ v, 4 ≤ deletionLoss G v) (c : Fin g.length)
    (hsmall : loss g c.val < 4) :
    ∃ x, G.Adj x (r.vertices c) ∧ ∀ i, x ≠ r.vertices i := by
  classical
  let s : Set V := Set.range r.vertices
  letI : Fintype s := Subtype.fintype (Membership.mem s)
  have hC : StrongC4Free (toSimpleGraph g r.wellFormed) := by
    intro h
    exact hG (h.trans r.imageIso.isContained |>.trans (Embedding.induce s).isContained)
  have heq : loss g c.val = deletionLoss (G.induce s) (r.imageIso c) := by
    rw [certificate_loss_eq_deletionLoss g r.wellFormed hC,
      deletionLoss_iso r.imageIso]
  have hv : r.vertices c ∈ s := ⟨c, rfl⟩
  have hs : deletionLoss (G.induce s) ⟨r.vertices c, hv⟩ < 4 := by
    simpa [Realizes.imageIso] using (heq ▸ hsmall)
  obtain ⟨x, hx, hxs⟩ := exists_neighbor_outside_of_loss hG hv hs (hlarge _)
  exact ⟨x, hx.symm, fun i hi => hxs ⟨i, hi.symm⟩⟩

end InducedPaths.Certificate
