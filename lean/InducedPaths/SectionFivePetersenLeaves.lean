module

public import InducedPaths.SectionFiveReconstruction
public import InducedPaths.PetersenSymmetry
public import InducedPaths.PetersenLeafSupport

open SimpleGraph
set_option maxHeartbeats 4000000

@[expose] public section
namespace InducedPaths
namespace SectionFiveReconstruction
open Classical

/-- Fiberwise reconstruction after the two support sites have been normalized.
All exterior vertices are genuine leaves, and the sites are the fixed Petersen edge. -/
theorem petersen_leaf_fiber_iso {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Set V) [Fintype Q]
    (e : G.induce Q ≃g petersenGraph)
    (hleaf : ∀ x, x ∉ Q → ∀ y z, G.Adj x y → G.Adj x z → y = z)
    (hcover : ∀ x, x ∉ Q →
      G.Adj x (e.symm petersenHub).val ∨ G.Adj x (e.symm petersenHubB).val) :
    ∃ a b, a + b + 10 = Fintype.card V ∧
      Nonempty (G ≃g petersenWithLeaves a b) := by
  classical
  let u : V := (e.symm petersenHub).val
  let v : V := (e.symm petersenHubB).val
  have hu : u ∈ Q := (e.symm petersenHub).property
  have hv : v ∈ Q := (e.symm petersenHubB).property
  have huv : u ≠ v := by
    intro h
    have h' : e.symm petersenHub = e.symm petersenHubB := Subtype.ext h
    have : petersenHub = petersenHubB := e.symm.injective h'
    exact (by decide : petersenHub ≠ petersenHubB) this
  let A := {x : V // x ∉ Q ∧ G.Adj x u}
  let B := {x : V // x ∉ Q ∧ G.Adj x v}
  let a := Fintype.card A
  let b := Fintype.card B
  let ea : Fin a ≃ A := (Fintype.equivFin A).symm
  let eb : Fin b ≃ B := (Fintype.equivFin B).symm
  let f : PetersenLeaves a b → V
    | .core s => (e.symm s).val
    | .leafA i => (ea i).val
    | .leafB i => (eb i).val
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      cases x with
      | core s =>
        cases y with
        | core t => exact congrArg PetersenLeaves.core (e.symm.injective (Subtype.ext h))
        | leafA i =>
          change (e.symm s).val = (ea i).val at h
          exact ((ea i).property.1 (h ▸ (e.symm s).property)).elim
        | leafB i =>
          change (e.symm s).val = (eb i).val at h
          exact ((eb i).property.1 (h ▸ (e.symm s).property)).elim
      | leafA i =>
        cases y with
        | core s =>
          change (ea i).val = (e.symm s).val at h
          exact ((ea i).property.1 (h.symm ▸ (e.symm s).property)).elim
        | leafA j => exact congrArg PetersenLeaves.leafA (ea.injective (Subtype.ext h))
        | leafB j =>
          change (ea i).val = (eb j).val at h
          have ha : G.Adj (ea i).val u := (ea i).property.2
          have hb : G.Adj (ea i).val v := h.symm ▸ (eb j).property.2
          exact (huv (hleaf _ (ea i).property.1 _ _ ha hb)).elim
      | leafB i =>
        cases y with
        | core s =>
          change (eb i).val = (e.symm s).val at h
          exact ((eb i).property.1 (h.symm ▸ (e.symm s).property)).elim
        | leafA j =>
          change (eb i).val = (ea j).val at h
          have hb : G.Adj (eb i).val v := (eb i).property.2
          have ha : G.Adj (eb i).val u := h.symm ▸ (ea j).property.2
          exact (huv (hleaf _ (eb i).property.1 _ _ ha hb)).elim
        | leafB j => exact congrArg PetersenLeaves.leafB (eb.injective (Subtype.ext h))
    · intro x
      by_cases hx : x ∈ Q
      · exact ⟨.core (e ⟨x, hx⟩), by simp [f]⟩
      · rcases hcover x hx with ha | hb
        · exact ⟨.leafA (ea.symm ⟨x, hx, ha⟩), by simp [f]⟩
        · exact ⟨.leafB (eb.symm ⟨x, hx, hb⟩), by simp [f]⟩
  have ha (i : Fin a) (w : V) : G.Adj (ea i).val w ↔ w = u := by
    constructor
    · intro hw; exact hleaf _ (ea i).property.1 _ _ hw (ea i).property.2
    · intro hw; simpa [hw] using (ea i).property.2
  have hb (i : Fin b) (w : V) : G.Adj (eb i).val w ↔ w = v := by
    constructor
    · intro hw; exact hleaf _ (eb i).property.1 _ _ hw (eb i).property.2
    · intro hw; simpa [hw] using (eb i).property.2
  have hcoreA (s : PetersenVertex) : (e.symm s).val = u ↔ s = petersenHub := by
    constructor
    · intro h; exact e.symm.injective (Subtype.ext h)
    · intro h; subst s; rfl
  have hcoreB (s : PetersenVertex) : (e.symm s).val = v ↔ s = petersenHubB := by
    constructor
    · intro h; exact e.symm.injective (Subtype.ext h)
    · intro h; subst s; rfl
  let iso : petersenWithLeaves a b ≃g G :=
    { toEquiv := Equiv.ofBijective f hf
      map_rel_iff' := by
        intro x y
        change G.Adj (f x) (f y) ↔ (petersenWithLeaves a b).Adj x y
        cases x with
        | core s =>
          cases y with
          | core t =>
            have he := e.symm.map_adj_iff (v := s) (w := t)
            change (G.induce Q).Adj (e.symm s) (e.symm t) ↔ _
            rw [he]
            simp only [petersenWithLeaves, simpleOf, ne_eq, PetersenLeaves.core.injEq]
            change petersenGraph.Adj s t ↔
              s ≠ t ∧ (petersenGraph.Adj s t ∨ petersenGraph.Adj t s)
            constructor
            · exact fun h => ⟨h.ne, Or.inl h⟩
            · exact fun h => h.2.elim id Adj.symm
          | leafA j => simpa [f, G.adj_comm, petersenWithLeaves, simpleOf, hcoreA] using ha j (e.symm s).val
          | leafB j => simpa [f, G.adj_comm, petersenWithLeaves, simpleOf, hcoreB] using hb j (e.symm s).val
        | leafA i =>
          cases y with
          | core s => simpa [f, petersenWithLeaves, simpleOf, hcoreA] using ha i (e.symm s).val
          | leafA j =>
            have hn : (ea j).val ≠ u := fun h => (ea j).property.1 (h.symm ▸ hu)
            simp [f, ha, hn, petersenWithLeaves, simpleOf]
          | leafB j =>
            have hn : (eb j).val ≠ u := fun h => (eb j).property.1 (h.symm ▸ hu)
            simp [f, ha, hn, petersenWithLeaves, simpleOf]
        | leafB i =>
          cases y with
          | core s => simpa [f, petersenWithLeaves, simpleOf, hcoreB] using hb i (e.symm s).val
          | leafA j =>
            have hn : (ea j).val ≠ v := fun h => (ea j).property.1 (h.symm ▸ hv)
            simp [f, hb, hn, petersenWithLeaves, simpleOf]
          | leafB j =>
            have hn : (eb j).val ≠ v := fun h => (eb j).property.1 (h.symm ▸ hv)
            simp [f, hb, hn, petersenWithLeaves, simpleOf] }
  refine ⟨a, b, ?_, ⟨iso.symm⟩⟩
  have hc := Fintype.card_congr iso.toEquiv
  have hp : Fintype.card PetersenVertex = 10 := by decide
  have hc' := Fintype.card_congr (PetersenLeaves.proxyTypeEquiv a b)
  simp only [Fintype.card_sum, Fintype.card_fin, hp] at hc'
  omega

/-- Normalize an arbitrary occupied edge before invoking fiber reconstruction. -/
theorem petersen_leaf_edge_iso {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Q : Set V) [Fintype Q]
    (e : G.induce Q ≃g petersenGraph) (u v : Q) (huv : G.Adj u v)
    (hleaf : ∀ x, x ∉ Q → ∀ y z, G.Adj x y → G.Adj x z → y = z)
    (hcover : ∀ x, x ∉ Q → G.Adj x u.val ∨ G.Adj x v.val) :
    ∃ a b, a + b + 10 = Fintype.card V ∧
      Nonempty (G ≃g petersenWithLeaves a b) := by
  obtain ⟨σ, hσu, hσv⟩ := petersen_edge_transitive (e u) (e v) (e.map_adj_iff.mpr huv)
  let e' := e.trans σ
  have hu' : e'.symm petersenHub = u := by
    apply e'.injective
    simpa [e'] using hσu.symm
  have hv' : e'.symm petersenHubB = v := by
    apply e'.injective
    simpa [e'] using hσv.symm
  apply petersen_leaf_fiber_iso G Q e' hleaf
  simpa only [hu', hv'] using hcover

noncomputable def petersenLeavesSwap (a b : ℕ) :
    petersenWithLeaves a b ≃g petersenWithLeaves b a := by
  let h := petersen_edge_transitive petersenHubB petersenHub (by decide)
  let σ := Classical.choose h
  have hB := (Classical.choose_spec h).1
  have hA := (Classical.choose_spec h).2
  have hAi : σ.symm petersenHubB = petersenHub := σ.injective (by simpa using hA.symm)
  have hBi : σ.symm petersenHub = petersenHubB := σ.injective (by simpa using hB.symm)
  refine {
    toFun := fun x => match x with
      | .core s => .core (σ s)
      | .leafA i => .leafB i
      | .leafB i => .leafA i
    invFun := fun x => match x with
      | .core s => .core (σ.symm s)
      | .leafA i => .leafB i
      | .leafB i => .leafA i
    left_inv := ?_
    right_inv := ?_
    map_rel_iff' := ?_ }
  · intro x; cases x <;> simp
  · intro x; cases x <;> simp
  · intro x y
    have h0 (s : PetersenVertex) : σ s = petersenHub ↔ s = petersenHubB := by
      rw [← hB, σ.injective.eq_iff]
    have h1 (s : PetersenVertex) : σ s = petersenHubB ↔ s = petersenHub := by
      rw [← hA, σ.injective.eq_iff]
    cases x <;> cases y <;>
      simp [petersenWithLeaves, simpleOf, σ.map_adj_iff, σ.injective.eq_iff, h0, h1]

/-- Order the two leaf fibers exactly as in the public predicate. -/
theorem petersen_leaf_pair_order {V : Type*} {G : SimpleGraph V} {a b : ℕ}
    (hi : Nonempty (G ≃g petersenWithLeaves a b)) :
    ∃ a' b', a' + b' = a + b ∧ (b' = 0 ∨ 1 ≤ a' ∧ a' ≤ b') ∧
      Nonempty (G ≃g petersenWithLeaves a' b') := by
  obtain ⟨e⟩ := hi
  by_cases hb : b = 0
  · exact ⟨a, b, rfl, Or.inl hb, ⟨e⟩⟩
  · by_cases ha : a = 0
    · exact ⟨b, a, by omega, Or.inl ha, ⟨e.trans (petersenLeavesSwap a b)⟩⟩
    · by_cases hab : a ≤ b
      · exact ⟨a, b, rfl, Or.inr ⟨by omega, hab⟩, ⟨e⟩⟩
      · exact ⟨b, a, by omega, Or.inr ⟨by omega, by omega⟩,
          ⟨e.trans (petersenLeavesSwap a b)⟩⟩

/-- A clique of occupied sites in a triangle-free Petersen core lies on one edge. -/
theorem petersen_support_edge {V : Type*} (G : SimpleGraph V) (Q : Set V)
    (e : G.induce Q ≃g petersenGraph) (ht : G.CliqueFree 3)
    (hroot : ∀ x, x ∉ Q → ∃ u : Q, G.Adj x u.val)
    (hsup : ∀ u v : Q, u ≠ v →
      (∃ x, x ∉ Q ∧ G.Adj x u.val) →
      (∃ x, x ∉ Q ∧ G.Adj x v.val) → G.Adj u.val v.val) :
    ∃ u v : Q, G.Adj u.val v.val ∧
      ∀ x, x ∉ Q → G.Adj x u.val ∨ G.Adj x v.val := by
  classical
  let A : Set Q := {u | ∃ x, x ∉ Q ∧ G.Adj x u.val}
  have hnbr (u : Q) : ∃ v : Q, G.Adj u.val v.val := by
    have hp : ∀ s : PetersenVertex, ∃ t, petersenGraph.Adj s t := by decide
    obtain ⟨v, hv⟩ := hp (e u)
    exact ⟨e.symm v, by simpa using e.symm.map_adj_iff.mpr hv⟩
  by_cases ha : A.Nonempty
  · obtain ⟨u, hu⟩ := ha
    by_cases hb : ∃ v ∈ A, v ≠ u
    · obtain ⟨v, hv, hvu⟩ := hb
      have huv := hsup u v hvu.symm hu hv
      refine ⟨u, v, huv, fun x hx => ?_⟩
      obtain ⟨w, hw⟩ := hroot x hx
      have hwA : w ∈ A := ⟨x, hx, hw⟩
      by_cases hwu : w = u
      · exact Or.inl (by simpa [hwu] using hw)
      · by_cases hwv : w = v
        · exact Or.inr (by simpa [hwv] using hw)
        · have huw := hsup u w (Ne.symm hwu) hu hwA
          have hvw := hsup v w (Ne.symm hwv) hv hwA
          have huv' : u.val ≠ v.val := fun h => hvu (Subtype.ext h.symm)
          have huw' : u.val ≠ w.val := fun h => hwu (Subtype.ext h.symm)
          have hvw' : v.val ≠ w.val := fun h => hwv (Subtype.ext h.symm)
          exact (ht {u.val, v.val, w.val}
            (is3Clique_triple_iff.mpr ⟨huv, huw, hvw⟩)).elim
    · obtain ⟨v, huv⟩ := hnbr u
      refine ⟨u, v, huv, fun x hx => ?_⟩
      obtain ⟨w, hw⟩ := hroot x hx
      have hwu : w = u := by
        by_contra hn
        exact hb ⟨w, ⟨x, hx, hw⟩, hn⟩
      exact Or.inl (by simpa [hwu] using hw)
  · let u := e.symm petersenHub
    obtain ⟨v, huv⟩ := hnbr u
    refine ⟨u, v, huv, fun x hx => ?_⟩
    obtain ⟨w, hw⟩ := hroot x hx
    exact (ha ⟨w, x, hx, hw⟩).elim

/-- Genuine Petersen reconstruction from the depth-one conclusion of stripping. -/
theorem petersen_leaves_canonical {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Set V) [Fintype Q]
    (e : G.induce Q ≃g petersenGraph) (ht : G.CliqueFree 3) (hp : IsPkFree G 7)
    (hdeg : ∀ x, x ∉ Q → G.degree x = 1)
    (hroot : ∀ x, x ∉ Q → ∃ u : Q, G.Adj x u.val) :
    ∃ a b, a + b + 10 = Fintype.card V ∧ (b = 0 ∨ 1 ≤ a ∧ a ≤ b) ∧
      Nonempty (G ≃g petersenWithLeaves a b) := by
  classical
  let emb : petersenGraph ↪g G := (SimpleGraph.Embedding.induce (G := G) Q).comp e.symm.toEmbedding
  have hem (s : PetersenVertex) : emb s = (e.symm s).val := rfl
  have hrange : Set.range emb = Q := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩; exact (e.symm s).property
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp [emb]⟩
  have hsup : ∀ u v : Q, u ≠ v →
      (∃ x, x ∉ Q ∧ G.Adj x u.val) →
      (∃ x, x ∉ Q ∧ G.Adj x v.val) → G.Adj u.val v.val := by
    intro u v huv hx hy
    obtain ⟨x, hx, hxu⟩ := hx
    obtain ⟨y, hy, hyv⟩ := hy
    have hadj := SectionFiveGlobal.petersen_leaf_support_adj G emb hp (e u) (e v)
      (fun h => huv (e.injective h))
      ⟨x, by simpa [hrange] using hx, by simpa [hem] using hxu, hdeg x hx⟩
      ⟨y, by simpa [hrange] using hy, by simpa [hem] using hyv, hdeg y hy⟩
    simpa [hem] using hadj
  obtain ⟨u, v, huv, hcover⟩ := petersen_support_edge G Q e ht hroot hsup
  have hleaf : ∀ x, x ∉ Q → ∀ y z, G.Adj x y → G.Adj x z → y = z := by
    intro x hx y z hxy hxz
    exact SectionFiveGlobal.leaf_neighbor_unique G (hdeg x hx) hxz hxy
  obtain ⟨a, b, hab, hi⟩ := petersen_leaf_edge_iso G Q e u v huv hleaf hcover
  obtain ⟨a', b', heq, hord, hi'⟩ := petersen_leaf_pair_order hi
  exact ⟨a', b', by omega, hord, hi'⟩

end SectionFiveReconstruction
end InducedPaths
