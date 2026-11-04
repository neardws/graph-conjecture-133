module

public import InducedPaths.Basic
public import InducedPaths.Graphs
public import Mathlib.Tactic

open SimpleGraph

@[expose] public section
namespace InducedPaths
namespace SectionFiveReconstruction

open Classical
noncomputable local instance {V : Type*} (Q : Set V) : DecidablePred (· ∈ Q) := Classical.decPred _

/-- A core of full cardinality is the entire graph, not merely equinumerous with it. -/
noncomputable def isoInduceOfCardEq {V : Type*} [Fintype V]
    (G : SimpleGraph V) (Q : Set V) [Fintype Q]
    (hq : Fintype.card Q = Fintype.card V) : G ≃g G.induce Q := by
  classical
  have hQ : Q = Set.univ := (set_fintype_card_eq_univ_iff Q).mp hq
  subst Q
  exact { toFun := fun v => ⟨v, Set.mem_univ v⟩
          invFun := Subtype.val
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_rel_iff' := Iff.rfl }

/-- Reconstruct a one-vertex extension when the exterior vertex is a leaf.
The explicit complement and unique-neighbor conditions isolate the local structural API. -/
noncomputable def isoAddLeafOfComplementSingleton {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (Q : Set V) (x : V) (r : Q)
    (hx : ∀ v, v ∉ Q ↔ v = x)
    (hroot : ∀ v : Q, G.Adj x v ↔ v = r) :
    G ≃g addLeaf (G.induce Q) r where
  toFun v := if hv : v ∈ Q then some ⟨v, hv⟩ else none
  invFun v := match v with | none => x | some v => v.val
  left_inv v := by
    by_cases hv : v ∈ Q
    · simp [hv]
    · have hxx := (hx x).mpr rfl
      simp [hv, (hx v).mp hv, hxx]
  right_inv v := by
    cases v with
    | none =>
      have hxx : x ∉ Q := (hx x).mpr rfl
      simp [hxx]
    | some v => simp [v.property]
  map_rel_iff' := by
    intro v w
    change (addLeaf (G.induce Q) r).Adj
      (if hv : v ∈ Q then some ⟨v, hv⟩ else none)
      (if hw : w ∈ Q then some ⟨w, hw⟩ else none) ↔ G.Adj v w
    by_cases hv : v ∈ Q <;> by_cases hw : w ∈ Q
    · simp only [dif_pos hv, dif_pos hw, addLeaf, simpleOf, Option.some.injEq]
      simp only [ne_eq, Option.some.injEq]
      change (¬(⟨v, hv⟩ : Q) = ⟨w, hw⟩ ∧ (G.Adj v w ∨ G.Adj w v)) ↔ G.Adj v w
      constructor
      · exact fun h => h.2.elim id Adj.symm
      · exact fun h => ⟨fun he => h.ne (congrArg Subtype.val he), Or.inl h⟩
    · have hwx : w = x := (hx w).mp hw
      subst w
      simp only [dif_pos hv, dif_neg hw, addLeaf, simpleOf]
      have hr := hroot ⟨v, hv⟩
      simpa [G.adj_comm] using hr.symm
    · have hvx : v = x := (hx v).mp hv
      subst v
      simp only [dif_neg hv, dif_pos hw, addLeaf, simpleOf]
      simpa using (hroot ⟨w, hw⟩).symm
    · have hvx : v = x := (hx v).mp hv
      have hwx : w = x := (hx w).mp hw
      simp [hv, hw, hvx, hwx, addLeaf, simpleOf]

/-- A cardinal gap of one is a literal singleton complement. -/
lemma complement_singleton_of_card {V : Type*} [Fintype V] (Q : Set V) [Fintype Q]
    (hq : Fintype.card Q + 1 = Fintype.card V) :
    ∃ x : V, ∀ v, v ∉ Q ↔ v = x := by
  classical
  have hQ : Fintype.card {v // v ∈ Q} = Fintype.card Q := Fintype.card_congr (Equiv.refl _)
  have hn : Fintype.card ↥(Qᶜ) = 1 := by
    have h := Fintype.card_subtype_compl (fun v => v ∈ Q)
    change Fintype.card ↥(Qᶜ) = Fintype.card V - Fintype.card {v // v ∈ Q} at h
    omega
  have hs : (Qᶜ).ncard = 1 := by
    rw [Set.ncard_eq_toFinset_card]
    simpa using hn
  obtain ⟨x, hx⟩ := Set.ncard_eq_one.mp hs
  refine ⟨x, fun v => ?_⟩
  change v ∈ Qᶜ ↔ v ∈ ({x} : Set V)
  rw [hx]

/-- Connectedness supplies the root of a singleton exterior, and the stripping
witness supplies uniqueness via the subsingleton-neighbor condition. -/
theorem exists_root_of_singleton_exterior {V : Type*} [Nontrivial V]
    (G : SimpleGraph V) (Q : Set V) (x : V) (hc : G.Connected)
    (hx : ∀ v, v ∉ Q ↔ v = x)
    (hunique : (Q ∩ G.neighborSet x).Subsingleton) :
    ∃ r : Q, ∀ v : Q, G.Adj x v ↔ v = r := by
  obtain ⟨y, hxy⟩ := hc.preconnected.exists_adj_of_nontrivial x
  have hyQ : y ∈ Q := by
    by_contra hy
    have hyx := (hx y).mp hy
    exact hxy.ne hyx.symm
  refine ⟨⟨y, hyQ⟩, fun v => ?_⟩
  constructor
  · intro hv
    exact Subtype.ext (hunique ⟨v.property, hv⟩ ⟨hyQ, hxy⟩)
  · intro hv
    simpa only [hv] using hxy

/-- Full reconstruction in the one-exterior-vertex case. The last hypothesis is
exactly `ChenXuLeafStrips.outside_neighbors`, kept abstract to avoid a core import. -/
theorem isoAddLeafOfCardGapOne {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) (Q : Set V) [Fintype Q] (hc : G.Connected)
    (hq : Fintype.card Q + 1 = Fintype.card V)
    (hu : ∀ x, x ∉ Q → (Q ∩ G.neighborSet x).Subsingleton) :
    ∃ r : Q, Nonempty (G ≃g addLeaf (G.induce Q) r) := by
  obtain ⟨x, hx⟩ := complement_singleton_of_card Q hq
  obtain ⟨r, hr⟩ := exists_root_of_singleton_exterior G Q x hc hx (hu x ((hx x).mpr rfl))
  exact ⟨r, ⟨isoAddLeafOfComplementSingleton G Q x r hx hr⟩⟩

/-- Leaf attachment is functorial under graph isomorphisms, with the root transported. -/
noncomputable def addLeafIso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (r : V) : addLeaf G r ≃g addLeaf H (e r) where
  toEquiv := Equiv.optionCongr e.toEquiv
  map_rel_iff' := by
    intro v w
    cases v with
    | none =>
      cases w with
      | none => simp [addLeaf, simpleOf]
      | some w => simp [addLeaf, simpleOf]
    | some v =>
      cases w with
      | none => simp [addLeaf, simpleOf]
      | some w =>
        simp only [Equiv.optionCongr_apply, Option.map_some, addLeaf, simpleOf,
          ne_eq, Option.some.injEq]
        change (e v ≠ e w ∧ (H.Adj (e v) (e w) ∨ H.Adj (e w) (e v))) ↔
          (v ≠ w ∧ (G.Adj v w ∨ G.Adj w v))
        rw [ne_eq, ne_eq, e.injective.eq_iff]
        simp only [e.map_adj_iff]

/-- One stripped vertex over an identified core gives a leaf extension of that named core. -/
theorem isoNamedLeafOfCardGapOne {V W : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) (H : SimpleGraph W) (Q : Set V) [Fintype Q]
    (hc : G.Connected) (hq : Fintype.card Q + 1 = Fintype.card V)
    (hu : ∀ x, x ∉ Q → (Q ∩ G.neighborSet x).Subsingleton)
    (hi : Nonempty (G.induce Q ≃g H)) :
    ∃ r : W, Nonempty (G ≃g addLeaf H r) := by
  obtain ⟨r, ⟨i⟩⟩ := isoAddLeafOfCardGapOne G Q hc hq hu
  obtain ⟨e⟩ := hi
  exact ⟨e r, ⟨i.trans (addLeafIso e r)⟩⟩

end SectionFiveReconstruction
end InducedPaths
