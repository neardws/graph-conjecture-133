module

public import InducedPaths.Basic
public import InducedPaths.Graphs
public import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators SimpleGraph
open SimpleGraph Finset

@[expose] public section
namespace InducedPaths
namespace SectionFiveNoniso

noncomputable local instance {V : Type*} (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _

lemma f2_sum (t : ℕ) (f : F2V t → ℕ) :
    ∑ v, f v = (∑ i, f (.cycle i)) + (∑ i, f (.A1 i)) + ∑ i, f (.A3 i) := by
  rw [← Equiv.sum_comp (F2V.proxyTypeEquiv t)]
  simp [Fintype.sum_sum_type, F2V.proxyTypeEquiv, add_assoc]

lemma f2_degree (t : ℕ) (v : F2V t) : (f2Graph t).degree v =
    match v with
    | .cycle i => 2 + if i = 0 ∨ i = 2 then t else 0
    | .A1 _ => 2
    | .A3 _ => 2 := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_eq_sum_ones,
    Finset.sum_filter, f2_sum]
  cases v with
  | cycle i =>
    fin_cases i <;> simp [f2Graph, simpleOf, cycleGraph_adj] <;> decide
  | A1 i => simp [f2Graph, simpleOf]
  | A3 i => simp [f2Graph, simpleOf]

lemma f0p_degree (t : ℕ) (v : F0pV t) : (f0pGraph t).degree v =
    match v with
    | .cycle i => 2 + if i = 0 ∨ i = 3 then t else 0
    | .Y1 _ => 2
    | .Y4 _ => 2 := by
  classical
  have sum (f : F0pV t → ℕ) : ∑ v, f v =
      (∑ i, f (.cycle i)) + (∑ i, f (.Y1 i)) + ∑ i, f (.Y4 i) := by
    rw [← Equiv.sum_comp (F0pV.proxyTypeEquiv t)]
    simp [Fintype.sum_sum_type, F0pV.proxyTypeEquiv, add_assoc]
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_eq_sum_ones,
    Finset.sum_filter, sum]
  cases v with
  | cycle i =>
    fin_cases i <;> simp [f0pGraph, simpleOf, cycleGraph_adj] <;> decide
  | Y1 i => simp [f0pGraph, simpleOf]
  | Y4 i => simp [f0pGraph, simpleOf]

lemma addLeaf_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (v : Option V) : (addLeaf G r).degree v =
    match v with
    | none => 1
    | some w => G.degree w + if w = r then 1 else 0 := by
  classical
  cases v with
  | none =>
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
      Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
    simp [addLeaf, simpleOf]
  | some w =>
    simp only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
      Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_option]
    simp only [addLeaf, simpleOf, ne_eq, Option.some.injEq, Option.some_ne_none,
      not_false_eq_true, or_self]
    have h (x : V) : (w ≠ x ∧ G.Adj w x) ↔ G.Adj w x :=
      ⟨And.right, fun h => ⟨h.ne, h⟩⟩
    simp only [G.adj_comm, or_self, h, true_and]
    omega

lemma petersen_degree (s : PetersenVertex) : petersenGraph.degree s = 3 := by
  have h : ∀ s : PetersenVertex, petersenGraph.degree s = 3 := by decide
  exact h s

lemma petersen_leaves_degree (a b : ℕ) (v : PetersenLeaves a b) :
    (petersenWithLeaves a b).degree v = match v with
    | .core s => 3 + (if s = petersenHub then a else 0) +
        (if s = petersenHubB then b else 0)
    | .leafA _ => 1
    | .leafB _ => 1 := by
  classical
  have sum (f : PetersenLeaves a b → ℕ) : ∑ v, f v =
      (∑ s, f (.core s)) + (∑ i, f (.leafA i)) + ∑ i, f (.leafB i) := by
    rw [← Equiv.sum_comp (PetersenLeaves.proxyTypeEquiv a b)]
    simp [Fintype.sum_sum_type, PetersenLeaves.proxyTypeEquiv, add_assoc]
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter, sum]
  cases v with
  | core s =>
    have hr (x : PetersenVertex) : (s ≠ x ∧ petersenGraph.Adj s x) ↔ petersenGraph.Adj s x :=
      ⟨And.right, fun h => ⟨h.ne, h⟩⟩
    have h : ∑ x, (if s ≠ x ∧ petersenGraph.Adj s x then 1 else 0) = 3 := by
      simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter,
        Finset.card_eq_sum_ones, Finset.sum_filter, hr] using petersen_degree s
    simp [petersenWithLeaves, simpleOf, petersenGraph.adj_comm, h]
  | leafA i => simp [petersenWithLeaves, simpleOf]
  | leafB i => simp [petersenWithLeaves, simpleOf]

lemma petersen_hubs_ne : petersenHub ≠ petersenHubB := by decide

lemma petersen_leaves_degree_le (a b : ℕ) (v : PetersenLeaves a b) :
    (petersenWithLeaves a b).degree v ≤ 3 + max a b := by
  rw [petersen_leaves_degree]
  cases v with
  | core s =>
    by_cases h : s = petersenHub
    · subst s
      simp only [ite_true, petersen_hubs_ne, ite_false, add_zero]
      omega
    · simp only [h, ite_false, add_zero]
      split <;> omega
  | leafA i => simp; omega
  | leafB i => simp; omega

lemma petersen_leaves_degree_top (a b : ℕ) :
    ∃ v, (petersenWithLeaves a b).degree v = 3 + max a b := by
  by_cases h : a ≤ b
  · refine ⟨.core petersenHubB, ?_⟩
    simp [petersen_leaves_degree, Ne.symm petersen_hubs_ne, max_eq_right h]
  · refine ⟨.core petersenHub, ?_⟩
    simp [petersen_leaves_degree, petersen_hubs_ne, max_eq_left (by omega : b ≤ a)]

/-- The maximum degree and the number of leaves recover the canonical pair. -/
theorem petersen_pairs (a b a' b' : ℕ) (hs : a + b = a' + b')
    (hc : b = 0 ∨ 1 ≤ a ∧ a ≤ b) (hc' : b' = 0 ∨ 1 ≤ a' ∧ a' ≤ b')
    (hi : Nonempty (petersenWithLeaves a b ≃g petersenWithLeaves a' b')) :
    a = a' ∧ b = b' := by
  obtain ⟨e⟩ := hi
  have le (a b a' b' : ℕ) (e : petersenWithLeaves a b ≃g petersenWithLeaves a' b') :
      max a b ≤ max a' b' := by
    obtain ⟨v, hv⟩ := petersen_leaves_degree_top a b
    have hb := petersen_leaves_degree_le a' b' (e v)
    rw [e.degree_eq, hv] at hb
    omega
  have hm : max a b = max a' b' := Nat.le_antisymm (le _ _ _ _ e) (le _ _ _ _ e.symm)
  rcases hc with h | ⟨ha, hb⟩ <;> rcases hc' with h' | ⟨ha', hb'⟩
  · simp_all
  · simp only [h, max_eq_left (Nat.zero_le _), max_eq_right hb'] at hm
    omega
  · simp only [h', max_eq_left (Nat.zero_le _), max_eq_right hb] at hm
    omega
  · rw [max_eq_right hb, max_eq_right hb'] at hm
    omega

lemma f2_degree_ge_two (t : ℕ) (v : F2V t) : 2 ≤ (f2Graph t).degree v := by
  rw [f2_degree]
  cases v <;> simp only <;> omega

lemma f0p_degree_ge_two (t : ℕ) (v : F0pV t) : 2 ≤ (f0pGraph t).degree v := by
  rw [f0p_degree]
  cases v <;> simp only <;> omega

/-- The family `F₂` has no leaves; the zero-leaf Petersen graph has even order. -/
theorem f2_not_petersen (t : ℕ) (_ht : 0 < t) (a b : ℕ) :
    ¬ Nonempty (f2Graph t ≃g petersenWithLeaves a b) := by
  rintro ⟨e⟩
  have ha : a = 0 := by
    by_contra h
    let v : PetersenLeaves a b := .leafA ⟨0, by omega⟩
    have hg := f2_degree_ge_two t (e.symm v)
    rw [e.symm.degree_eq, petersen_leaves_degree] at hg
    contradiction
  have hb : b = 0 := by
    by_contra h
    let v : PetersenLeaves a b := .leafB ⟨0, by omega⟩
    have hg := f2_degree_ge_two t (e.symm v)
    rw [e.symm.degree_eq, petersen_leaves_degree] at hg
    contradiction
  subst a; subst b
  have hc := Fintype.card_congr e.toEquiv
  have hp : Fintype.card PetersenVertex = 10 := by decide
  have h1 := Fintype.card_congr (F2V.proxyTypeEquiv t)
  have h2 := Fintype.card_congr (PetersenLeaves.proxyTypeEquiv 0 0)
  simp only [Fintype.card_sum, Fintype.card_fin, hp] at h1 h2
  omega

/-- `F'₀` has minimum degree two, whereas the extension has a leaf. -/
theorem f0p_not_hub (t : ℕ) (_ht : 0 < t) :
    ¬ Nonempty (f0pGraph t ≃g f2HubLeaf t) := by
  rintro ⟨e⟩
  have hg := f0p_degree_ge_two t (e.symm none)
  rw [e.symm.degree_eq] at hg
  change 2 ≤ (addLeaf (f2Graph t) (.cycle 0)).degree none at hg
  rw [addLeaf_degree] at hg
  change 2 ≤ 1 at hg
  omega

/-- The same minimum-degree invariant separates the midpoint extension. -/
theorem f0p_not_mid (t : ℕ) (_ht : 0 < t) :
    ¬ Nonempty (f0pGraph t ≃g f2MidLeaf t) := by
  rintro ⟨e⟩
  have hg := f0p_degree_ge_two t (e.symm none)
  rw [e.symm.degree_eq] at hg
  change 2 ≤ (addLeaf (f2Graph t) (.cycle 1)).degree none at hg
  rw [addLeaf_degree] at hg
  change 2 ≤ 1 at hg
  omega

lemma extension_unique_leaf (t : ℕ) (r : F2V t) (v : Option (F2V t))
    (h : (addLeaf (f2Graph t) r).degree v = 1) : v = none := by
  cases v with
  | none => rfl
  | some v =>
    rw [addLeaf_degree] at h
    dsimp only at h
    have hg := f2_degree_ge_two t v
    omega

/-- The unique leaf has support degree `t+3` at a hub and `3` at the midpoint. -/
theorem hub_not_mid (t : ℕ) (ht : 0 < t) :
    ¬ Nonempty (f2HubLeaf t ≃g f2MidLeaf t) := by
  rintro ⟨e⟩
  have he : e none = none := by
    apply extension_unique_leaf t (.cycle 1)
    change (f2MidLeaf t).degree (e none) = 1
    rw [e.degree_eq]
    change (addLeaf (f2Graph t) (.cycle 0)).degree none = 1
    exact addLeaf_degree (f2Graph t) (.cycle 0) none
  have hadj : (f2MidLeaf t).Adj none (e (some (.cycle 0))) := by
    rw [← he, e.map_adj_iff]
    simp [f2HubLeaf, addLeaf, simpleOf]
  have hs : e (some (.cycle 0)) = some (.cycle 1) := by
    change (addLeaf (f2Graph t) (.cycle 1)).Adj none (e (some (.cycle 0))) at hadj
    cases h : e (some (.cycle 0)) with
    | none => rw [h] at hadj; exact False.elim (hadj.ne rfl)
    | some v =>
      rw [h] at hadj
      have hv : v = .cycle 1 := by simpa [addLeaf, simpleOf] using hadj
      exact congrArg some hv
  have hd := e.degree_eq (some (.cycle 0))
  rw [hs] at hd
  change (addLeaf (f2Graph t) (.cycle 1)).degree (some (.cycle 1)) =
    (addLeaf (f2Graph t) (.cycle 0)).degree (some (.cycle 0)) at hd
  rw [addLeaf_degree, addLeaf_degree] at hd
  simp [f2_degree] at hd
  omega

end SectionFiveNoniso

/-- All five canonical nonisomorphism clauses of Theorem 5.6. -/
theorem sectionFive_noniso :
    (∀ a b a' b' : ℕ,
      a + b = a' + b' → (b = 0 ∨ 1 ≤ a ∧ a ≤ b) → (b' = 0 ∨ 1 ≤ a' ∧ a' ≤ b') →
        Nonempty (petersenWithLeaves a b ≃g petersenWithLeaves a' b') → a = a' ∧ b = b') ∧
      (∀ t, 0 < t → ∀ a b, ¬ Nonempty (f2Graph t ≃g petersenWithLeaves a b)) ∧
      (∀ t, 0 < t → ¬ Nonempty (f0pGraph t ≃g f2HubLeaf t)) ∧
      (∀ t, 0 < t → ¬ Nonempty (f0pGraph t ≃g f2MidLeaf t)) ∧
      (∀ t, 0 < t → ¬ Nonempty (f2HubLeaf t ≃g f2MidLeaf t)) :=
  ⟨SectionFiveNoniso.petersen_pairs, SectionFiveNoniso.f2_not_petersen,
    SectionFiveNoniso.f0p_not_hub, SectionFiveNoniso.f0p_not_mid, SectionFiveNoniso.hub_not_mid⟩

end InducedPaths
