module

public import InducedPaths.Graphs
public import Mathlib.Tactic

@[expose] public section
namespace InducedPaths
namespace SectionFiveExtremal

/-- The deficit envelope at Petersen orders. -/
lemma edgeExtremal_small {n : ℕ} (hn : 10 ≤ n) (hm : n ≤ 16) :
    edgeExtremal n = 2 * n + 10 := by
  have he : Even n ↔ n % 2 = 0 := Nat.even_iff
  unfold edgeExtremal
  split_ifs with heven
  · have : n % 2 = 0 := Nat.even_iff.mp heven
    omega
  · have : n % 2 ≠ 0 := by simpa only [Nat.even_iff] using heven
    omega

lemma edgeExtremal_odd {n : ℕ} (hn : 15 ≤ n) (ho : n % 2 = 1) :
    edgeExtremal n = 3 * n - 5 := by
  have he : ¬ Even n := by rw [Nat.even_iff]; omega
  simp only [edgeExtremal, he, if_false]
  omega

lemma edgeExtremal_even {n : ℕ} (hn : 16 ≤ n) (ho : n % 2 = 0) :
    edgeExtremal n = 3 * n - 6 := by
  have he : Even n := Nat.even_iff.mpr ho
  simp only [edgeExtremal, he, if_true]
  omega

/-- Arithmetic upper-bound reduction, stated using untruncated edge counts.
The structural worker need only provide one of these three core alternatives. -/
lemma bound_of_core_counts {n h e q : ℕ} (hn : 10 ≤ n) (hh : h ≤ n)
    (he : e = q + (n - h))
    (hc : 2 * q ≤ 2 * h + 10 ∨
      (h % 2 = 1 ∧ 2 * q + 5 = 3 * h) ∨ 2 * q + 6 = 3 * h) :
    2 * e ≤ edgeExtremal n := by
  have hp : n % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases hs : n ≤ 16
  · rw [edgeExtremal_small hn hs]
    rcases hc with hc | ⟨ho, hc⟩ | hc <;> omega
  · by_cases ho : n % 2 = 1
    · rw [edgeExtremal_odd (by omega) ho]
      rcases hc with hc | ⟨hhodd, hc⟩ | hc <;> omega
    · rw [edgeExtremal_even (by omega) (by omega)]
      rcases hc with hc | ⟨hhodd, hc⟩ | hc <;> omega

/-- Every nonextremal fixed row is strictly below the envelope, even after stripping. -/
lemma strict_of_other_core_counts {n h e q : ℕ} (hn : 10 ≤ n) (hh : h ≤ n)
    (he : e = q + (n - h)) (hc : 2 * q ≤ 2 * h + 8) :
    2 * e < edgeExtremal n := by
  have hp : n % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases hs : n ≤ 16
  · rw [edgeExtremal_small hn hs]; omega
  · by_cases ho : n % 2 = 1
    · rw [edgeExtremal_odd (by omega) ho]; omega
    · rw [edgeExtremal_even (by omega) (by omega)]; omega

/-- Equality for a Petersen core restricts the final order to 10 through 16. -/
lemma petersen_core_equality_iff {n e : ℕ} (hn : 10 ≤ n) (he : e = 15 + (n - 10)) :
    2 * e = edgeExtremal n ↔ n ≤ 16 := by
  constructor
  · intro heq
    by_contra hs
    by_cases ho : n % 2 = 1
    · rw [edgeExtremal_odd (by omega) ho] at heq; omega
    · have hp : n % 2 < 2 := Nat.mod_lt _ (by omega)
      rw [edgeExtremal_even (by omega) (by omega)] at heq; omega
  · intro hs
    rw [edgeExtremal_small hn hs]; omega

/-- Equality for an F₂ core allows no attachment at odd orders and exactly one at even orders. -/
lemma f2_core_equality_iff {n h e q : ℕ} (hn : 10 ≤ n) (hh : h ≤ n)
    (he : e = q + (n - h)) (hc : 2 * q + 5 = 3 * h) (ho : h % 2 = 1) :
    2 * e = edgeExtremal n ↔
      (15 ≤ n ∧ n % 2 = 1 ∧ n = h) ∨
      (16 ≤ n ∧ n % 2 = 0 ∧ n = h + 1) := by
  have hp : n % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases hs : n ≤ 16
  · rw [edgeExtremal_small hn hs]
    omega
  · by_cases hno : n % 2 = 1
    · rw [edgeExtremal_odd (by omega) hno]; omega
    · rw [edgeExtremal_even (by omega) (by omega)]; omega

/-- Equality for an F'₀ core permits no attached vertex. -/
lemma f0p_core_equality_iff {n h e q : ℕ} (hn : 10 ≤ n) (hh : h ≤ n)
    (he : e = q + (n - h)) (hc : 2 * q + 6 = 3 * h) (ho : h % 2 = 0) :
    2 * e = edgeExtremal n ↔ 16 ≤ n ∧ n = h := by
  have hp : n % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases hs : n ≤ 16
  · rw [edgeExtremal_small hn hs]; omega
  · by_cases hno : n % 2 = 1
    · rw [edgeExtremal_odd (by omega) hno]; omega
    · rw [edgeExtremal_even (by omega) (by omega)]; omega

end SectionFiveExtremal
end InducedPaths
