module

public import InducedPaths.ChenXuCounts
public import InducedPaths.SectionFiveNoniso
public import InducedPaths.SectionFiveExtremalArithmetic

open scoped BigOperators SimpleGraph
open SimpleGraph Finset

@[expose] public section
namespace InducedPaths
namespace SectionFiveExtremal

noncomputable local instance {V : Type*} (G : SimpleGraph V) : DecidableRel G.Adj := Classical.decRel _

/-- Standalone copy of the public equality predicate, avoiding a StatementsCore import cycle. -/
def Canonical {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  let n := Fintype.card V
  if 10 ≤ n ∧ n ≤ 14 then
    ∃ a b, a + b = n - 10 ∧ (b = 0 ∨ (1 ≤ a ∧ a ≤ b)) ∧
      Nonempty (G ≃g petersenWithLeaves a b)
  else if n = 15 then
    (∃ a b, a + b = 5 ∧ (b = 0 ∨ (1 ≤ a ∧ a ≤ b)) ∧
        Nonempty (G ≃g petersenWithLeaves a b)) ∨
      Nonempty (G ≃g f2Graph 5)
  else if n = 16 then
    (∃ a b, a + b = 6 ∧ (b = 0 ∨ (1 ≤ a ∧ a ≤ b)) ∧
        Nonempty (G ≃g petersenWithLeaves a b)) ∨
      Nonempty (G ≃g f0pGraph 5) ∨
      Nonempty (G ≃g f2HubLeaf 5) ∨
      Nonempty (G ≃g f2MidLeaf 5)
  else if 17 ≤ n ∧ n % 2 = 1 then
    Nonempty (G ≃g f2Graph ((n - 5) / 2))
  else if 18 ≤ n ∧ n % 2 = 0 then
    let t := (n - 6) / 2
    Nonempty (G ≃g f0pGraph t) ∨
      Nonempty (G ≃g f2HubLeaf t) ∨
      Nonempty (G ≃g f2MidLeaf t)
  else False

lemma addLeaf_edgeCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : edgeCount (addLeaf G r) = edgeCount G + 1 := by
  classical
  have h := (addLeaf G r).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_option] at h
  simp only [SectionFiveNoniso.addLeaf_degree] at h
  rw [Finset.sum_add_distrib] at h
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  have hG := G.sum_degrees_eq_twice_card_edges
  simp only [edgeCount] at hG ⊢
  omega

lemma petersen_leaves_edgeCount (a b : ℕ) :
    edgeCount (petersenWithLeaves a b) = 15 + a + b := by
  classical
  have h := (petersenWithLeaves a b).sum_degrees_eq_twice_card_edges
  have sum (f : PetersenLeaves a b → ℕ) : ∑ v, f v =
      (∑ s, f (.core s)) + (∑ i, f (.leafA i)) + ∑ i, f (.leafB i) := by
    rw [← Equiv.sum_comp (PetersenLeaves.proxyTypeEquiv a b)]
    simp [Fintype.sum_sum_type, PetersenLeaves.proxyTypeEquiv, add_assoc]
  rw [sum] at h
  simp only [SectionFiveNoniso.petersen_leaves_degree] at h
  have hc : Fintype.card PetersenVertex = 10 := by decide
  simp [Finset.sum_add_distrib, hc, edgeCount] at h ⊢
  omega

lemma edgeCount_iso {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
    [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W} (e : G ≃g H) :
    edgeCount G = edgeCount H := by
  exact e.card_edgeFinset_eq

lemma petersen_iso_equality {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : ℕ} (hn : 10 ≤ Fintype.card V)
    (hm : Fintype.card V ≤ 16) (hab : a + b = Fintype.card V - 10)
    (hi : Nonempty (G ≃g petersenWithLeaves a b)) :
    2 * edgeCount G = edgeExtremal (Fintype.card V) := by
  obtain ⟨i⟩ := hi
  rw [edgeCount_iso i, petersen_leaves_edgeCount, edgeExtremal_small hn hm]
  omega

lemma f2_iso_equality {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {t : ℕ} (hn : 15 ≤ Fintype.card V)
    (hi : Nonempty (G ≃g f2Graph t)) :
    2 * edgeCount G = edgeExtremal (Fintype.card V) := by
  obtain ⟨i⟩ := hi
  have hc : Fintype.card V = 5 + 2*t :=
    (Fintype.card_congr i.toEquiv).trans (f2_card t)
  rw [edgeCount_iso i, f2_edgeCount, edgeExtremal_odd hn (by omega)]
  omega

lemma f0p_iso_equality {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {t : ℕ} (hn : 16 ≤ Fintype.card V)
    (hi : Nonempty (G ≃g f0pGraph t)) :
    2 * edgeCount G = edgeExtremal (Fintype.card V) := by
  obtain ⟨i⟩ := hi
  have hc : Fintype.card V = 6 + 2*t :=
    (Fintype.card_congr i.toEquiv).trans (f0p_card t)
  rw [edgeCount_iso i, f0p_edgeCount, edgeExtremal_even hn (by omega)]
  omega

lemma f2_leaf_iso_equality {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {t : ℕ} {r : F2V t} (hn : 16 ≤ Fintype.card V)
    (hi : Nonempty (G ≃g addLeaf (f2Graph t) r)) :
    2 * edgeCount G = edgeExtremal (Fintype.card V) := by
  obtain ⟨i⟩ := hi
  have hc : Fintype.card V = 6 + 2*t := by
    have := Fintype.card_congr i.toEquiv
    rw [Fintype.card_option, f2_card] at this
    omega
  rw [edgeCount_iso i, addLeaf_edgeCount, f2_edgeCount, edgeExtremal_even hn (by omega)]
  omega

/-- All models in the exact public equality predicate attain its numerical value. -/
theorem canonical_equality {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hc : Canonical G) :
    2 * edgeCount G = edgeExtremal (Fintype.card V) := by
  unfold Canonical at hc
  dsimp only at hc
  split_ifs at hc with hs h15 h16 ho he
  · obtain ⟨a, b, hab, _, hi⟩ := hc
    exact petersen_iso_equality hs.1 (by omega) hab hi
  · rcases hc with ⟨a, b, hab, _, hi⟩ | hi
    · exact petersen_iso_equality (by omega) (by omega) (by omega) hi
    · exact f2_iso_equality (by omega) hi
  · rcases hc with ⟨a, b, hab, _, hi⟩ | hi | hi | hi
    · exact petersen_iso_equality (by omega) (by omega) (by omega) hi
    · exact f0p_iso_equality (by omega) hi
    · exact f2_leaf_iso_equality (by omega) hi
    · exact f2_leaf_iso_equality (by omega) hi
  · exact f2_iso_equality (by omega) hc
  · rcases hc with hi | hi | hi
    · exact f0p_iso_equality (by omega) hi
    · exact f2_leaf_iso_equality (by omega) hi
    · exact f2_leaf_iso_equality (by omega) hi

/-- The complete numerical upper bound from a leaf-stripping core witness.
The three alternatives correspond to the fixed table, F₂, and F'₀ respectively. -/
theorem bound_of_stripped_core {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (Q : SimpleGraph W)
    (hn : 10 ≤ Fintype.card V) (hh : Fintype.card W ≤ Fintype.card V)
    (he : edgeCount G = edgeCount Q + (Fintype.card V - Fintype.card W))
    (hc : 2 * edgeCount Q ≤ 2 * Fintype.card W + 10 ∨
      (Fintype.card W % 2 = 1 ∧ 2 * edgeCount Q + 5 = 3 * Fintype.card W) ∨
      2 * edgeCount Q + 6 = 3 * Fintype.card W) :
    2 * edgeCount G ≤ edgeExtremal (Fintype.card V) :=
  bound_of_core_counts hn hh he hc

/-- The table refinement supplies precisely the arithmetic alternatives used above. -/
lemma family_core_alternatives {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hf : InChenXuFamily G) :
    2 * edgeCount G ≤ 2 * Fintype.card V + 10 ∨
      (Fintype.card V % 2 = 1 ∧ 2 * edgeCount G + 5 = 3 * Fintype.card V) ∨
      2 * edgeCount G + 6 = 3 * Fintype.card V := by
  rcases chenXu_table_refinement hf with ⟨_, hn, he⟩ | ⟨t, _, hn, he⟩ |
    ⟨t, _, hn, he⟩ | he
  · left; omega
  · right; left; constructor <;> omega
  · right; right; omega
  · left; omega

/-- Numerical Theorem 5.6 for a stripped Chen–Xu core. -/
theorem bound_of_stripped_family {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (Q : SimpleGraph W)
    (hn : 10 ≤ Fintype.card V) (hh : Fintype.card W ≤ Fintype.card V)
    (he : edgeCount G = edgeCount Q + (Fintype.card V - Fintype.card W))
    (hf : InChenXuFamily Q) :
    2 * edgeCount G ≤ edgeExtremal (Fintype.card V) :=
  bound_of_stripped_core G Q hn hh he (family_core_alternatives hf)

/-- Equality reduces the stripped core to exactly the three named possibilities,
including the precise number of stripped vertices. Reconstruction is deliberately
not claimed by this numerical lemma. -/
theorem equality_core_cases {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (Q : SimpleGraph W)
    (hn : 10 ≤ Fintype.card V) (hh : Fintype.card W ≤ Fintype.card V)
    (he : edgeCount G = edgeCount Q + (Fintype.card V - Fintype.card W))
    (hf : InChenXuFamily Q)
    (heq : 2 * edgeCount G = edgeExtremal (Fintype.card V)) :
    (Nonempty (Q ≃g petersenGraph) ∧ Fintype.card W = 10 ∧ Fintype.card V ≤ 16) ∨
    (∃ t, Nonempty (Q ≃g f2Graph t) ∧ Fintype.card W = 5 + 2*t ∧
      ((15 ≤ Fintype.card V ∧ Fintype.card V % 2 = 1 ∧ Fintype.card V = Fintype.card W) ∨
       (16 ≤ Fintype.card V ∧ Fintype.card V % 2 = 0 ∧ Fintype.card V = Fintype.card W + 1))) ∨
    (∃ t, Nonempty (Q ≃g f0pGraph t) ∧ Fintype.card W = 6 + 2*t ∧
      16 ≤ Fintype.card V ∧ Fintype.card V = Fintype.card W) := by
  rcases chenXu_table_refinement hf with ⟨hi, hnQ, heQ⟩ | ⟨t, hi, hnQ, heQ⟩ |
    ⟨t, hi, hnQ, heQ⟩ | heQ
  · left
    refine ⟨hi, hnQ, ?_⟩
    apply (petersen_core_equality_iff hn (by omega)).mp heq
  · right; left
    refine ⟨t, hi, hnQ, ?_⟩
    exact (f2_core_equality_iff hn hh he (by omega) (by omega)).mp heq
  · right; right
    obtain ⟨hn', hnW⟩ := (f0p_core_equality_iff hn hh he (by omega) (by omega)).mp heq
    exact ⟨t, hi, hnQ, hn', hnW⟩
  · have hlt := strict_of_other_core_counts hn hh he heQ
    omega

end SectionFiveExtremal
end InducedPaths
