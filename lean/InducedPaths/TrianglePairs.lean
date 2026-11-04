/-
Extracting distinct triangles from the numerical hypothesis of Lemma 5.9.
-/
module

public import InducedPaths.Basic

open Finset SimpleGraph

@[expose] public section

namespace InducedPaths

/-- The triangle-count hypothesis gives two distinct actual triangle vertex sets. -/
theorem exists_distinct_triangles {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (h : 2 ≤ triangleCount G) :
    ∃ s t : Finset V, G.IsNClique 3 s ∧ G.IsNClique 3 t ∧ s ≠ t := by
  have hc : 1 < (G.cliqueFinset 3).card := by
    change 2 ≤ (G.cliqueFinset 3).card at h
    omega
  obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp hc
  exact ⟨s, t, (G.mem_cliqueFinset_iff).mp hs, (G.mem_cliqueFinset_iff).mp ht, hst⟩

/-- Distinct triangles in a strong `C₄`-free graph have at most one vertex in
common. A shared edge would have the two third vertices as common neighbours. -/
theorem triangle_inter_card_le_one {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (hC : StrongC4Free G) {s t : Finset V}
    (hs : G.IsNClique 3 s) (ht : G.IsNClique 3 t) (hne : s ≠ t) :
    (s ∩ t).card ≤ 1 := by
  by_contra h
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (s ∩ t).card)
  have has : a ∈ s := (mem_inter.mp ha).1
  have hat : a ∈ t := (mem_inter.mp ha).2
  have hbs : b ∈ s := (mem_inter.mp hb).1
  have hbt : b ∈ t := (mem_inter.mp hb).2
  have hsub : s ⊆ t := by
    intro x hx
    by_cases hxa : x = a
    · exact hxa ▸ hat
    by_cases hxb : x = b
    · exact hxb ▸ hbt
    have htcard : t.card = 3 := ht.card_eq
    have hex : ∃ y ∈ t, y ≠ a ∧ y ≠ b := by
      by_contra hn
      have htss : t ⊆ {a, b} := by
        intro y hy
        by_cases hya : y = a
        · simp [hya]
        by_cases hyb : y = b
        · simp [hyb]
        exact (hn ⟨y, hy, hya, hyb⟩).elim
      have hh := Finset.card_le_card htss
      have htwo : ({a, b} : Finset V).card ≤ 2 := by exact (Finset.card_insert_le a {b}).trans (by simp)
      omega
    obtain ⟨y, hy, hya, hyb⟩ := hex
    have hxy : x = y := commonNeighbors_subsingleton hC hab
      ⟨hs.isClique has hx (Ne.symm hxa), hs.isClique hbs hx (Ne.symm hxb)⟩
      ⟨ht.isClique hat hy (Ne.symm hya), ht.isClique hbt hy (Ne.symm hyb)⟩
    exact hxy ▸ hy
  have heq : s = t := Finset.eq_of_subset_of_card_le hsub (by rw [hs.card_eq, ht.card_eq])
  exact hne heq

end InducedPaths
