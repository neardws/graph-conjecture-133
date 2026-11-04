/-
Arithmetic assembly for Theorem 3.6. These lemmas do not assume or assert the
missing structural classification of the admissible graphs.
-/
module

public import InducedPaths.IsoLoss
public import InducedPaths.CanonicalMass
public import Mathlib.Tactic

open SimpleGraph

@[expose] public section
namespace InducedPaths

/-- The proposed density envelope never exceeds three. -/
theorem extremalDensity_le_three {n : ℕ} (hn : 2 ≤ n) :
    extremalDensity n ≤ 3 := by
  unfold extremalDensity
  split <;> norm_num at *
  split
  · have hnq : (11 : ℚ) ≤ n := by exact_mod_cast ‹11 ≤ n›
    have hpos : (0 : ℚ) < n := by positivity
    have : (2 : ℚ) / n ≤ 1 := (div_le_iff₀ hpos).mpr (by linarith)
    linarith
  · norm_num

/-- Only order ten can attain density three in the proposed envelope. -/
theorem extremalDensity_eq_three_iff {n : ℕ} (hn : 2 ≤ n) :
    extremalDensity n = 3 ↔ n = 10 := by
  unfold extremalDensity
  split <;> norm_num at *
  split
  · have hnq : (11 : ℚ) ≤ n := by exact_mod_cast ‹11 ≤ n›
    have hpos : (0 : ℚ) < n := by positivity
    have hlt : (2 : ℚ) + 2 / n < 3 := by
      have : (2 : ℚ) / n < 1 := (div_lt_iff₀ hpos).mpr (by linarith)
      linarith
    constructor
    · intro he; linarith
    · intro he; omega
  · constructor
    · norm_num
    · intro he; omega

/-- A density bound yields the integral mass bound without a rounding assumption. -/
theorem mass_le_three_card_of_density_bound {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V)
    (hbound : ell G ≤ extremalDensity (Fintype.card V)) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V := by
  have hpos : (0 : ℚ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have h := hbound.trans (extremalDensity_le_three hn)
  rw [ell, div_le_iff₀ hpos] at h
  exact_mod_cast h

/-- Equality in the mass bound forces order ten and equality in the density bound. -/
theorem mass_eq_three_card_forces_order_ten {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V)
    (hbound : ell G ≤ extremalDensity (Fintype.card V))
    (heq : neighbourhoodIndependenceSum G = 3 * Fintype.card V) :
    Fintype.card V = 10 ∧ ell G = extremalDensity (Fintype.card V) := by
  have hpos : (0 : ℚ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hell : ell G = 3 := by
    rw [ell, heq, Nat.cast_mul, Nat.cast_ofNat]
    exact mul_div_cancel_right₀ _ (ne_of_gt hpos)
  have hd : extremalDensity (Fintype.card V) = 3 :=
    le_antisymm (extremalDensity_le_three hn) (by simpa [hell] using hbound)
  exact ⟨(extremalDensity_eq_three_iff hn).mp hd, hell.trans hd.symm⟩

/-- Once the density classification is established, the Petersen-only equality
clause needs no additional structural argument. -/
theorem mass_eq_three_card_iff_of_density_classification {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hn : 2 ≤ Fintype.card V)
    (hbound : ell G ≤ extremalDensity (Fintype.card V))
    (hclass : Fintype.card V = 10 →
      ell G = extremalDensity (Fintype.card V) → Nonempty (G ≃g petersenGraph)) :
    neighbourhoodIndependenceSum G = 3 * Fintype.card V ↔
      Nonempty (G ≃g petersenGraph) := by
  constructor
  · intro he
    obtain ⟨hc, hd⟩ := mass_eq_three_card_forces_order_ten G hn hbound he
    exact hclass hc hd
  · exact mass_eq_three_card_of_iso_petersen

/-- At order at least seven, the five-cycle branch is strictly below the
extremal envelope. This also excludes its equality cases. -/
theorem density_lt_extremal_of_mass_le_two_card_add_one {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hn : 7 ≤ Fintype.card V)
    (hS : neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V + 1) :
    ell G < extremalDensity (Fintype.card V) := by
  have hnq : (7 : ℚ) ≤ Fintype.card V := by exact_mod_cast hn
  have hpos : (0 : ℚ) < Fintype.card V := by linarith
  have hSq : (neighbourhoodIndependenceSum G : ℚ) ≤ 2 * (Fintype.card V : ℚ) + 1 := by
    exact_mod_cast hS
  rw [ell, div_lt_iff₀ hpos]
  unfold extremalDensity
  split <;> norm_num at *
  all_goals try omega
  all_goals try simp_all only [Nat.cast_ofNat]
  all_goals try norm_num at *
  all_goals try linarith
  split
  · field_simp
    linarith
  · omega

/-- The chordal mass bound is strictly below the extremal envelope from
order five onward. -/
theorem density_lt_extremal_of_mass_le_two_card_sub_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hn : 5 ≤ Fintype.card V)
    (hS : neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V - 2) :
    ell G < extremalDensity (Fintype.card V) := by
  have hnq : (5 : ℚ) ≤ Fintype.card V := by exact_mod_cast hn
  have hpos : (0 : ℚ) < Fintype.card V := by linarith
  have hSn : neighbourhoodIndependenceSum G + 2 ≤ 2 * Fintype.card V := by omega
  have hSq : (neighbourhoodIndependenceSum G : ℚ) + 2 ≤ 2 * (Fintype.card V : ℚ) := by
    exact_mod_cast hSn
  rw [ell, div_lt_iff₀ hpos]
  unfold extremalDensity
  split <;> norm_num at *
  all_goals try omega
  all_goals try simp_all only [Nat.cast_ofNat]
  all_goals try norm_num at *
  all_goals try linarith
  split
  · field_simp
    linarith
  · omega

/-- The elementary tree/chordal bound lies below the envelope at every
admissible order, including two, three and four. -/
theorem density_le_extremal_of_mass_le_two_card_sub_two {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hn : 2 ≤ Fintype.card V)
    (hS : neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V - 2) :
    ell G ≤ extremalDensity (Fintype.card V) := by
  by_cases h5 : 5 ≤ Fintype.card V
  · exact (density_lt_extremal_of_mass_le_two_card_sub_two G h5 hS).le
  have hpos : (0 : ℚ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hSn : neighbourhoodIndependenceSum G + 2 ≤ 2 * Fintype.card V := by omega
  have hSq : (neighbourhoodIndependenceSum G : ℚ) + 2 ≤ 2 * (Fintype.card V : ℚ) := by
    exact_mod_cast hSn
  rw [ell, div_le_iff₀ hpos]
  have hc : Fintype.card V = 2 ∨ Fintype.card V = 3 ∨ Fintype.card V = 4 := by omega
  rcases hc with hc | hc | hc <;> simp [hc, extremalDensity] at * <;> linarith

end InducedPaths
