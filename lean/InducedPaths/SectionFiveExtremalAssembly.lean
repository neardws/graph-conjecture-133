module

public import InducedPaths.SectionFiveExtremal
public import InducedPaths.SectionFivePetersenLeaves
public import InducedPaths.SectionFiveF2Leaves
public import InducedPaths.ChenXuForest

open SimpleGraph
@[expose] public section
namespace InducedPaths
namespace SectionFiveExtremal
open SectionFiveReconstruction

lemma canonical_of_petersen {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hn : 10 ≤ Fintype.card V) (hm : Fintype.card V ≤ 16)
    (hc : ∃ a b, a + b + 10 = Fintype.card V ∧ (b = 0 ∨ 1 ≤ a ∧ a ≤ b) ∧
      Nonempty (G ≃g petersenWithLeaves a b)) : Canonical G := by
  obtain ⟨a, b, hab, hord, hi⟩ := hc
  unfold Canonical
  dsimp only
  split_ifs <;> try omega
  · exact ⟨a, b, by omega, hord, hi⟩
  · exact Or.inl ⟨a, b, by omega, hord, hi⟩
  · exact Or.inl ⟨a, b, by omega, hord, hi⟩

lemma canonical_of_f2 {V : Type*} [Fintype V] {G : SimpleGraph V} {t : ℕ}
    (hn : 15 ≤ Fintype.card V) (hcard : Fintype.card V = 5 + 2*t)
    (hi : Nonempty (G ≃g f2Graph t)) : Canonical G := by
  have ho : Fintype.card V % 2 = 1 := by omega
  unfold Canonical
  dsimp only
  split_ifs <;> try omega
  · have ht : t = 5 := by omega
    subst t; exact Or.inr hi
  · have ht : (Fintype.card V - 5) / 2 = t := by omega
    rw [ht]
    exact hi

lemma canonical_of_f0p {V : Type*} [Fintype V] {G : SimpleGraph V} {t : ℕ}
    (hn : 16 ≤ Fintype.card V) (hcard : Fintype.card V = 6 + 2*t)
    (hi : Nonempty (G ≃g f0pGraph t)) : Canonical G := by
  have ho : Fintype.card V % 2 = 0 := by omega
  unfold Canonical
  dsimp only
  split_ifs <;> try omega
  · have ht : t = 5 := by omega
    subst t; exact Or.inr (Or.inl hi)
  · have ht : (Fintype.card V - 6) / 2 = t := by omega
    apply Or.inl
    rw [ht]
    exact hi

lemma canonical_of_f2_leaf {V : Type*} [Fintype V] {G : SimpleGraph V} {t : ℕ}
    (hn : 16 ≤ Fintype.card V) (hcard : Fintype.card V = 6 + 2*t)
    (hi : Nonempty (G ≃g f2HubLeaf t) ∨ Nonempty (G ≃g f2MidLeaf t)) : Canonical G := by
  have ho : Fintype.card V % 2 = 0 := by omega
  unfold Canonical
  dsimp only
  split_ifs <;> try omega
  · have ht : t = 5 := by omega
    subst t
    exact Or.inr (Or.inr hi)
  · have ht : (Fintype.card V - 6) / 2 = t := by omega
    apply Or.inr
    rw [ht]
    exact hi

/-- Exact reverse equality from a literal stripped Chen–Xu core. -/
theorem canonical_of_stripped_family {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Q : Set V) [Fintype Q]
    (hconn : G.Connected) (htri : G.CliqueFree 3) (hp : IsPkFree G 7)
    (hs : ChenXuLeafStrips G Set.univ Q)
    (hn : 10 ≤ Fintype.card V) (hh : Fintype.card Q ≤ Fintype.card V)
    (he : edgeCount G = edgeCount (G.induce Q) + (Fintype.card V - Fintype.card Q))
    (hf : InChenXuFamily (G.induce Q))
    (heq : 2 * edgeCount G = edgeExtremal (Fintype.card V)) : Canonical G := by
  classical
  haveI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  rcases equality_core_cases G (G.induce Q) hn hh
    (by simpa only [edgeCount, edgeFinset_card, ← Nat.card_eq_fintype_card] using he)
    hf (by simpa only [edgeCount, edgeFinset_card, ← Nat.card_eq_fintype_card] using heq) with
    ⟨⟨e⟩, hQ, hm⟩ | ⟨t, ⟨e⟩, hQ, hcases⟩ | ⟨t, ⟨e⟩, hQ, hn', hfull⟩
  · apply canonical_of_petersen hn hm
    have hdeg := chenXu_petersen_outside_degree_one hconn hs htri hp e
    have hind := chenXu_petersen_exterior_independent hconn hs htri hp e
    have hroot : ∀ x, x ∉ Q → ∃ u : Q, G.Adj x u.val := by
      intro x hx
      obtain ⟨y, hxy, _⟩ := degree_eq_one_iff_existsUnique_adj.mp (hdeg x hx)
      have hyQ : y ∈ Q := by
        by_contra hy
        exact hind ⟨x, hx⟩ ⟨y, hy⟩ hxy
      exact ⟨⟨y, hyQ⟩, hxy⟩
    exact petersen_leaves_canonical G Q e htri hp hdeg hroot
  · rcases hcases with ⟨hn', ho, hfull⟩ | ⟨hn', ho, hone⟩
    · have i := (isoInduceOfCardEq G Q hfull.symm).trans e
      exact canonical_of_f2 hn' (by omega) ⟨i⟩
    · apply canonical_of_f2_leaf (t := t) hn' (by omega)
      apply f2_one_exterior_canonical G Q (t := t) (by omega) hconn hp (by omega)
      · exact fun x hx => hs.outside_neighbors x (Set.mem_univ _) hx
      · exact ⟨e⟩
  · have i := (isoInduceOfCardEq G Q hfull.symm).trans e
    exact canonical_of_f0p hn' (by omega) ⟨i⟩

/-- Exact standalone Theorem 5.6, with the literal public equality predicate copy. -/
theorem theorem_5_6_exact {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (htri : G.CliqueFree 3) (hC : StrongC4Free G) (hp : IsPkFree G 7)
    (hn : 10 ≤ Fintype.card V) :
    2 * edgeCount G ≤ edgeExtremal (Fintype.card V) ∧
      (2 * edgeCount G = edgeExtremal (Fintype.card V) ↔ Canonical G) := by
  classical
  obtain ⟨Q, _, hs, _, _, _, _, _, hclass, he, _⟩ :=
    chenXu_tree_core_stripping hconn htri hC hp
  have hh : Fintype.card Q ≤ Fintype.card V := Fintype.card_subtype_le _
  have he' : edgeCount G = edgeCount (G.induce Q) +
      (Fintype.card V - Fintype.card Q) := by
    simpa only [Nat.card_eq_fintype_card] using he
  have hbound : 2 * edgeCount G ≤ edgeExtremal (Fintype.card V) := by
    rcases hclass with h1 | h2 | hf
    · obtain ⟨e⟩ := h1
      have hQ := Fintype.card_congr e.toEquiv
      have heQ : edgeCount (G.induce Q) = 0 := by
        have he := e.card_edgeFinset_eq
        have hz : edgeCount (completeGraph (Fin 1)) = 0 := by decide
        exact he.trans hz
      apply bound_of_core_counts hn hh he'
      left; simp only [Fintype.card_fin] at hQ; omega
    · obtain ⟨e⟩ := h2
      have hQ := Fintype.card_congr e.toEquiv
      have heQ : edgeCount (G.induce Q) = 1 := by
        have he := e.card_edgeFinset_eq
        have hz : edgeCount k2Graph = 1 := by decide
        exact he.trans hz
      apply bound_of_core_counts hn hh he'
      left; simp only [Fintype.card_fin] at hQ; omega
    · have hb := bound_of_stripped_family G (G.induce Q) hn hh
        (by simpa only [edgeCount, edgeFinset_card, ← Nat.card_eq_fintype_card] using he') hf
      simpa only [edgeCount, edgeFinset_card, ← Nat.card_eq_fintype_card] using hb
  refine ⟨hbound, ?_, ?_⟩
  · intro heq
    rcases hclass with h1 | h2 | hf
    · obtain ⟨e⟩ := h1
      have hQ := Fintype.card_congr e.toEquiv
      have heQ : edgeCount (G.induce Q) = 0 := by
        have he := e.card_edgeFinset_eq
        have hz : edgeCount (completeGraph (Fin 1)) = 0 := by decide
        exact he.trans hz
      have hstrict := strict_of_other_core_counts hn hh he' (show
        2 * edgeCount (G.induce Q) ≤ 2 * Fintype.card Q + 8 by omega)
      omega
    · obtain ⟨e⟩ := h2
      have hQ := Fintype.card_congr e.toEquiv
      have heQ : edgeCount (G.induce Q) = 1 := by
        have he := e.card_edgeFinset_eq
        have hz : edgeCount k2Graph = 1 := by decide
        exact he.trans hz
      have hstrict := strict_of_other_core_counts hn hh he' (show
        2 * edgeCount (G.induce Q) ≤ 2 * Fintype.card Q + 8 by omega)
      omega
    · exact canonical_of_stripped_family G Q hconn htri hp hs hn hh he' hf heq
  · intro hc
    simpa only [edgeCount, edgeFinset_card, ← Nat.card_eq_fintype_card] using canonical_equality hc

end SectionFiveExtremal
end InducedPaths
