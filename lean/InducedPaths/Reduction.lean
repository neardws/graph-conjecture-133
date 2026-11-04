/-
Section 6, Remark 5.12, and the arithmetic consequences that do not need a new idea.
`GenK` and `Rad` stay open. Corollary 6.1 is proved from Theorem 5.11 and Erdős–Saks–Sós.
-/
module

public import InducedPaths.Statements
public import InducedPaths.Theta
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

open scoped SimpleGraph
open Filter Topology

@[expose] public section

namespace InducedPaths

variable {V : Type*} {G : SimpleGraph V}

/-- Remark 5.12. The case `c_{C₄} = 0` is the geodesic `p ≥ r + 1`.
The case `c_{C₄} = 1` uses Theorem 5.11, Theorem 5.10, Corollary 4.4, and
`erdos_saks_sos`. Those four inputs are still `sorry` or an axiom. -/
theorem remark_5_12 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hn : 2 ≤ Fintype.card V) (hell : ell G < 5) :
    (inducedPathOrder G : ℚ) ≥
      (radiusNat G : ℚ) + Nat.floor (ell G ^ cC4 G) := by
  by_cases hC : StrongC4Free G
  · by_cases hle : ell G ≤ 4
    · have h := theorem_5_11 (G := G) hle hn hconn
      have hc : cC4 G = 1 := by simp [cC4, hC]
      have hnonneg : 0 ≤ ell G := by
        have : Nonempty V := hconn.nonempty
        have hn0 : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
        rw [ell]
        exact div_nonneg (Nat.cast_nonneg _) hn0.le
      have hfloor : (Nat.floor (ell G ^ cC4 G) : ℚ) ≤ ell G ^ cC4 G := by
        rw [hc, pow_one]
        exact Nat.floor_le hnonneg
      have hr : (radiusNat G : ℚ) + Nat.floor (ell G ^ cC4 G) ≤
          (radiusNat G : ℚ) + ell G ^ cC4 G := by
        linarith
      exact hr.trans (by simpa [hc, pow_one] using h)
    · have hgt : 4 < ell G := lt_of_not_ge hle
      have hc : cC4 G = 1 := by simp [cC4, hC]
      have hfloor : Nat.floor (ell G ^ cC4 G) = 4 := by
        rw [hc, pow_one]
        refine (Nat.floor_eq_iff (by linarith : (0 : ℚ) ≤ ell G)).mpr ?_
        constructor
        · exact_mod_cast (show (4 : ℚ) ≤ ell G by linarith)
        · rw [show ((4 : ℕ) : ℚ) + 1 = 5 by norm_num]
          exact hell
      by_contra hfail
      have hp_lt : (inducedPathOrder G : ℚ) < (radiusNat G : ℚ) + 4 := by
        simpa [hfloor] using lt_of_not_ge hfail
      have hp_le : inducedPathOrder G ≤ radiusNat G + 3 := by
        have : (inducedPathOrder G : ℚ) < ((radiusNat G + 4 : ℕ) : ℚ) := by
          simpa [Nat.cast_add] using hp_lt
        exact Nat.lt_succ_iff.mp (Nat.cast_lt.mp (by simpa [Nat.add_assoc, Nat.cast_add] using this))
      have hess := erdos_saks_sos G hconn
      have hr4 : radiusNat G ≤ 4 := by
        have : 2 * radiusNat G ≤ radiusNat G + 4 := by
          have : inducedPathOrder G + 1 ≤ radiusNat G + 4 := by omega
          omega
        omega
      by_cases hr3 : radiusNat G ≤ 3
      · have hp6 : inducedPathOrder G ≤ 6 := by omega
        have hfree : IsPkFree G 7 := by
          rw [isPkFree_iff_inducedPathOrder_lt]
          omega
        have hS := (theorem_5_10 hconn hC hfree).1
        have : Nonempty V := hconn.nonempty
        have hnQ : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
        have hell3 : ell G ≤ 3 := by
          rw [ell, div_le_iff₀ hnQ]
          exact_mod_cast hS
        linarith
      · have hr : radiusNat G = 4 := by omega
        have hp : inducedPathOrder G = 7 := by
          have hge : 7 ≤ inducedPathOrder G := by
            have : 8 ≤ inducedPathOrder G + 1 := by simpa [hr] using hess
            omega
          omega
        have hell2 := (corollary_4_4 hconn hC hr hp).2
        linarith
  · have hc : cC4 G = 0 := by simp [cC4, hC]
    have hgeo := inducedPathOrder_ge_radius_succ (G := G) hconn
    have hfloor : Nat.floor (ell G ^ cC4 G) = 1 := by
      rw [hc, pow_zero]
      exact Nat.floor_one
    have : (radiusNat G : ℚ) + 1 ≤ inducedPathOrder G := by exact_mod_cast hgeo
    simpa [hfloor] using this

/-- Proposition 6.2, the numerical claims for `θₖ`. -/
theorem proposition_6_2 (k : ℕ) (hk : 3 ≤ k) :
    StrongC4Free (thetaGraph k) ∧
      Fintype.card (ThetaV k) = 2 * k + 2 ∧
      radiusNat (thetaGraph k) = 3 ∧
      inducedPathOrder (thetaGraph k) = 6 ∧
      neighbourhoodIndependenceSum (thetaGraph k) = 6 * k ∧
      neighbourhoodIndependenceSum (thetaGraph k) =
        3 * Fintype.card (ThetaV k) - 6 :=
  theta_proposition k hk

/-- The closed form `6k / (2k + 2) = 3 - 3 / (k + 1)` used in Proposition 6.2. -/
theorem theta_closed_form (k : ℕ) (hk : 0 < k) :
    (6 : ℚ) * k / (2 * k + 2) = 3 - 3 / (k + 1) := by
  have hk' : (k : ℚ) + 1 ≠ 0 := by positivity
  field_simp [hk']
  ring

/-- `(p - r - ℓ)(θₖ) = 3 / (k + 1) → 0`. -/
theorem theta_gap_tendsto :
    Tendsto (fun k : ℕ => (3 : ℚ) / ((k : ℚ) + 1)) atTop (nhds 0) := by
  simpa [div_eq_mul_inv] using
    (tendsto_const_nhds (x := (3 : ℚ))).mul tendsto_one_div_add_atTop_nhds_zero_nat

/-- Corollary 6.1. A connected strong `C₄`-free counterexample to REAL-133 has `ℓ > 4`,
and with `K = ⌈ℓ⌉ - 1` it violates `GEN_K` or `RAD(K + 1)`. Proved from Theorem 5.11
and `erdos_saks_sos`. -/
theorem corollary_6_1 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hn : 2 ≤ Fintype.card V)
    (hviolate : ¬ ((inducedPathOrder G : ℚ) ≥ (radiusNat G : ℚ) + ell G ^ cC4 G)) :
    let K := Nat.ceil (ell G) - 1
    4 < ell G ∧ 4 ≤ K ∧
      ((radiusNat G ≤ K ∧ inducedPathOrder G ≤ radiusNat G + K ∧
          inducedPathOrder G ≤ 2 * K ∧
          K * Fintype.card V < neighbourhoodIndependenceSum G) ∨
        (radiusNat G = K + 1 ∧ 5 ≤ K + 1 ∧
          inducedPathOrder G = 2 * radiusNat G - 1 ∧
          ((radiusNat G - 1 : ℕ) : ℚ) < ell G)) := by
  set K := Nat.ceil (ell G) - 1 with hK
  have hc : cC4 G = 1 := by simp [cC4, hC]
  have hlt : (inducedPathOrder G : ℚ) < (radiusNat G : ℚ) + ell G := by
    simpa [hc, pow_one] using lt_of_not_ge hviolate
  have hgt4 : 4 < ell G := by
    by_contra hle
    exact hviolate (theorem_5_11 (G := G) (le_of_not_gt hle) hn hconn)
  have h5 : 5 ≤ Nat.ceil (ell G) := (Nat.add_one_le_ceil_iff (n := 4)).mpr hgt4
  have hK4 : 4 ≤ K := by omega
  have hceil : Nat.ceil (ell G) = K + 1 := by omega
  have hbounds :=
    (Nat.ceil_eq_iff (n := K + 1) (a := ell G) (by omega)).mp hceil
  have hKlt : (K : ℚ) < ell G := by simpa using hbounds.1
  have hell_le : ell G ≤ (K + 1 : ℚ) := by simpa using hbounds.2
  have hp_le : inducedPathOrder G ≤ radiusNat G + K := by
    have : (inducedPathOrder G : ℚ) < (radiusNat G : ℚ) + (K + 1 : ℚ) := by linarith
    have : (inducedPathOrder G : ℚ) < ((radiusNat G + (K + 1) : ℕ) : ℚ) := by
      simpa [Nat.cast_add] using this
    exact Nat.lt_succ_iff.mp <| Nat.cast_lt.mp <| by
      simpa [Nat.add_assoc] using this
  have hess := erdos_saks_sos G hconn
  have hr_le : radiusNat G ≤ K + 1 := by
    have : inducedPathOrder G + 1 ≤ radiusNat G + K + 1 := by omega
    omega
  have : Nonempty V := hconn.nonempty
  have hn0 : 0 < Fintype.card V := Fintype.card_pos
  have hS : K * Fintype.card V < neighbourhoodIndependenceSum G := by
    have hnQ : (0 : ℚ) < Fintype.card V := by exact_mod_cast hn0
    have : (K : ℚ) * Fintype.card V < neighbourhoodIndependenceSum G := by
      have : (K : ℚ) < neighbourhoodIndependenceSum G / Fintype.card V := by
        simpa [ell] using hKlt
      rwa [lt_div_iff₀ hnQ] at this
    exact_mod_cast this
  refine ⟨hgt4, hK4, ?_⟩
  by_cases hrK : radiusNat G ≤ K
  · left
    refine ⟨hrK, hp_le, ?_, hS⟩
    omega
  · right
    have hr : radiusNat G = K + 1 := by omega
    refine ⟨hr, by omega, ?_, ?_⟩
    · have hge : 2 * radiusNat G ≤ inducedPathOrder G + 1 := hess
      have hle2 : inducedPathOrder G ≤ 2 * radiusNat G - 1 := by
        have : inducedPathOrder G ≤ (K + 1) + K := by simpa [hr] using hp_le
        omega
      omega
    · have : radiusNat G - 1 = K := by omega
      have : ((radiusNat G - 1 : ℕ) : ℚ) = (K : ℚ) := by exact_mod_cast this
      linarith

/-- Corollary 6.3, the strict inequality. The bound uses Theorem 5.10, which is still
`sorry`. The Petersen order in the equality case is `petersen_inducedPathOrder`. -/
theorem corollary_6_3 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : inducedPathOrder G = 6) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V - 1 ∧ ell G < 3 := by
  have hfree : IsPkFree G 7 := by
    rw [isPkFree_iff_inducedPathOrder_lt]
    omega
  obtain ⟨hle, heq⟩ := theorem_5_10 hconn hC hfree
  have : Nonempty V := hconn.nonempty
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have hS : neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V - 1 := by
    by_cases hs : neighbourhoodIndependenceSum G = 3 * Fintype.card V
    · obtain ⟨e⟩ := heq.mp hs
      have : inducedPathOrder G = 5 := by
        rw [inducedPathOrder_iso e]
        exact petersen_inducedPathOrder
      omega
    · omega
  refine ⟨hS, ?_⟩
  have hnQ : (0 : ℚ) < Fintype.card V := by exact_mod_cast hn
  rw [ell, div_lt_iff₀ hnQ]
  have hnum : (neighbourhoodIndependenceSum G : ℚ) ≤ ((3 * Fintype.card V - 1 : ℕ) : ℚ) := by
    exact_mod_cast hS
  have hlt : ((3 * Fintype.card V - 1 : ℕ) : ℚ) < 3 * (Fintype.card V : ℚ) := by
    have : 3 * Fintype.card V - 1 < 3 * Fintype.card V :=
      Nat.sub_lt (by omega : 0 < 3 * Fintype.card V) (by decide)
    exact_mod_cast this
  exact lt_of_le_of_lt hnum hlt

end InducedPaths
