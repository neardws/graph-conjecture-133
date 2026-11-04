module

public import InducedPaths.C6Classification
public meta import InducedPaths.C6Classification

open scoped SimpleGraph
open SimpleGraph

@[expose] public section
namespace InducedPaths

variable {V : Type*} {G : SimpleGraph V}

/-- Finite coordinates retaining the antipodal trace of every apex. -/
abbrev HexShapeV (k h : ℕ) := Fin 6 ⊕ (Fin k ⊕ Fin h)

def hexShape (k h : ℕ) (f : Fin k → Fin 3) : SimpleGraph (HexShapeV k h) :=
  simpleOf fun
  | .inl i, .inl j => (cycleGraph 6).Adj i j
  | .inl i, .inr (.inl j) => i.val % 3 = (f j).val
  | .inr (.inl j), .inl i => i.val % 3 = (f j).val
  | .inr (.inl _), .inr (.inr _) => True
  | .inr (.inr _), .inr (.inl _) => True
  | _, _ => False

instance (k h : ℕ) (f : Fin k → Fin 3) : DecidableRel (hexShape k h f).Adj := by
  intro a b
  rcases a with i | a <;> try rcases a with a | x
  all_goals rcases b with j | b <;> try rcases b with b | y
  all_goals unfold hexShape simpleOf
  all_goals dsimp
  all_goals infer_instance

/-- Coordinate classification, including the actual adjacency relation, in the
multi-apex branch. No labelling of the occupied antipodal pairs is assumed. -/
theorem hexShape_iso [Fintype V] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (a b : hexFirst c) (hab : a ≠ b) (k h : ℕ)
    (hk : Nat.card (hexFirst c) = k) (hh : Nat.card (hexSecond c) = h) :
    ∃ f : Fin k → Fin 3, Function.Injective f ∧ Nonempty (G ≃g hexShape k h f) := by
  classical
  let ea : hexFirst c ≃ Fin k := Fintype.equivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hk)
  let ex : hexSecond c ≃ Fin h := Fintype.equivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hh)
  let f : Fin k → Fin 3 := fun j => hexFirstIndex hC hp c (ea.symm j)
  refine ⟨f, (hexFirstIndex_injective hC hp c).comp ea.symm.injective, ?_⟩
  let e : V ≃ HexShapeV k h := (hexLayerPartition c).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr ea ex))
  have hs (w : hexFirst c) (i : Fin 6) :
      G.Adj w.val (c i) ↔ i.val % 3 = (f (ea w)).val := by
    simpa only [f, Equiv.symm_apply_apply] using hexFirstIndex_spec hC hp c w i
  have hn (i : Fin 6) (x : hexSecond c) : ¬ G.Adj (c i) x.val :=
    fun h => x.property.2 i h.symm
  have hadj (u v : V) : (hexShape k h f).Adj (e u) (e v) ↔ G.Adj u v := by
    obtain ⟨u, rfl⟩ := (hexLayerPartition c).surjective u
    obtain ⟨v, rfl⟩ := (hexLayerPartition c).surjective v
    change (hexShape k h f).Adj
      ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr ea ex))
        ((hexLayerPartition c).symm ((hexLayerPartition c) u)))
      ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr ea ex))
        ((hexLayerPartition c).symm ((hexLayerPartition c) v))) ↔ _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases u with i | u <;> try rcases u with a | x
    all_goals rcases v with j | v <;> try rcases v with b | y
    all_goals simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, id_eq]
    all_goals change (hexShape k h f).Adj _ _ ↔ G.Adj _ _
    all_goals simp only [hexShape, simpleOf, hexLayerPartition,
      Equiv.ofBijective_apply, Sum.elim_inl, Sum.elim_inr]
    all_goals try simp only [Equiv.refl_apply]
    all_goals simp only [ne_eq, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, not_false_eq_true, true_and,
      or_self, false_or, and_false, and_true, false_iff, true_iff]
    all_goals first
      | (solve | rw [c.map_rel_iff]; exact
          ⟨fun h => h.2.elim id Adj.symm, fun h => ⟨h.ne, Or.inl h⟩⟩)
      | (solve | simp [hexFirst_independent hC hp c])
      | (solve | simp [hexSecond_independent hconn hC hp c a b hab])
      | exact hn _ _
      | exact fun h => hn _ _ h.symm
      | exact (hs _ _).symm
      | (solve | simpa only [G.adj_comm] using (hs b i).symm)
      | exact hexSecond_complete hconn hC hp c _ _
      | exact (hexSecond_complete hconn hC hp c _ _).symm
  exact ⟨{ e with map_rel_iff' := fun {u v} => hadj u v }⟩

end InducedPaths
