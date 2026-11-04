module

public import InducedPaths.C6NamedAssembly
public import InducedPaths.ExtremalArithmetic

open scoped SimpleGraph
open SimpleGraph

@[expose] public section
namespace InducedPaths

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The named extremizers belonging to the induced-hexagon branch. -/
def IsHexExtremal (G : SimpleGraph V) : Prop :=
  match Fintype.card V with
  | 6 => Nonempty (G ≃g cycleGraph 6)
  | 7 => Nonempty (G ≃g gammaGraph 0)
  | 8 => Nonempty (G ≃g h8Graph)
  | 9 => Nonempty (G ≃g petersenMinus)
  | 10 => Nonempty (G ≃g petersenGraph)
  | n => if 11 ≤ n then Nonempty (G ≃g gammaGraph (n - 7)) else False

theorem extremalDensity_of_ge_eleven {n : ℕ} (hn : 11 ≤ n) :
    extremalDensity n = 2 + (2 : ℚ) / n := by
  unfold extremalDensity
  split <;> try omega
  rename_i h
  simp only [ite_eq_left hn]

/-- Named hexagonal examples attain the envelope, without any admissibility
hypothesis or appeal to the global classification. -/
theorem IsHexExtremal.density_eq (he : IsHexExtremal G) :
    ell G = extremalDensity (Fintype.card V) := by
  by_cases hn : 11 ≤ Fintype.card V
  · have he' : Nonempty (G ≃g gammaGraph (Fintype.card V - 7)) := by
      unfold IsHexExtremal at he
      split at he <;> try omega
      simpa [hn] using he
    obtain ⟨e⟩ := he'
    have hm := neighbourhoodIndependenceSum_iso e
    rw [gamma_mass] at hm
    have hs : 16 + 2 * (Fintype.card V - 7) = 2 * Fintype.card V + 2 := by omega
    rw [hs] at hm
    have hp : (0 : ℚ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
    rw [ell, hm, extremalDensity_of_ge_eleven hn]
    push_cast
    field_simp
  · have hc : Fintype.card V ≤ 10 := by omega
    interval_cases h : Fintype.card V <;>
      simp only [IsHexExtremal, h] at he
    all_goals try { norm_num at he }
    all_goals obtain ⟨e⟩ := he
    all_goals rw [ell, neighbourhoodIndependenceSum_iso e]
    all_goals norm_num [h, extremalDensity, cycle6_mass, gamma_mass, h8_mass,
      petersenMinus_mass, petersen_mass]

/-- Arithmetic for the one-apex mass bound. At orders eight through ten it
is strictly below the envelope; at seven and from eleven on it is sharp. -/
private theorem hexOne_density_arithmetic (hn : 7 ≤ Fintype.card V)
    (hm : neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V + 2) :
    ell G ≤ extremalDensity (Fintype.card V) ∧
    (ell G = extremalDensity (Fintype.card V) →
      neighbourhoodIndependenceSum G = 2 * Fintype.card V + 2 ∧
      (Fintype.card V = 7 ∨ 11 ≤ Fintype.card V)) := by
  have hp : (0 : ℚ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have hmq : (neighbourhoodIndependenceSum G : ℚ) ≤ 2 * (Fintype.card V : ℚ) + 2 := by
    exact_mod_cast hm
  by_cases hl : 11 ≤ Fintype.card V
  · rw [extremalDensity_of_ge_eleven hl]
    have hb : ell G ≤ 2 + 2 / (Fintype.card V : ℚ) := by
      rw [ell, div_le_iff₀ hp]
      field_simp
      linarith
    refine ⟨hb, fun he => ⟨?_, Or.inr hl⟩⟩
    rw [ell, div_eq_iff hp.ne'] at he
    have hEq : (neighbourhoodIndependenceSum G : ℚ) = 2 * (Fintype.card V : ℚ) + 2 := by
      field_simp at he
      linarith
    exact_mod_cast hEq
  · have hc : Fintype.card V = 7 ∨ Fintype.card V = 8 ∨
        Fintype.card V = 9 ∨ Fintype.card V = 10 := by omega
    rcases hc with hc | hc | hc | hc
    all_goals rw [hc] at hm hmq ⊢
    all_goals simp only [ell, hc]
    all_goals norm_num [extremalDensity]
    all_goals norm_num only [Nat.cast_ofNat, mul_add, mul_one] at hmq
    all_goals constructor
    all_goals try linarith
    all_goals intro he
    exact_mod_cast (by linarith : (neighbourhoodIndependenceSum G : ℚ) = 16)

private theorem hexOne_extremal (hn : 7 ≤ Fintype.card V)
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a : hexFirst c) (ha : ∀ b : hexFirst c, b = a) :
    ell G ≤ extremalDensity (Fintype.card V) ∧
    (ell G = extremalDensity (Fintype.card V) → IsHexExtremal G) := by
  classical
  obtain ⟨hm, hi⟩ := hexOne_mass_le hconn hC hp c a ha
  obtain ⟨hb, he⟩ := hexOne_density_arithmetic hn hm
  refine ⟨hb, fun hd => ?_⟩
  obtain ⟨hm, h7 | hl⟩ := he hd
  · have hk : Nat.card (hexFirst c) = 1 := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_eq_one_iff.mpr ⟨a, ha⟩
    have hh : Nat.card (hexSecond c) = 0 := by
      have hc := hexLayer_card c
      omega
    have hj := hi hm
    rw [hh] at hj
    simpa only [IsHexExtremal, h7] using hj
  · have hi' := (hexLarge_mass hconn hC hp c hl).2 hm
    unfold IsHexExtremal
    split <;> try omega
    simpa [hl] using hi'

/-- The order-six induced-hexagon branch is the hexagon itself. -/
theorem hex_six_extremal (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G) (hn : Fintype.card V = 6) :
    IsHexExtremal G := by
  classical
  have hc := hexLayer_card c
  have hz : Nat.card (hexFirst c) = 0 := by omega
  have hi : IsEmpty (hexFirst c) := by
    apply Fintype.card_eq_zero_iff.mp
    simpa only [Nat.card_eq_fintype_card] using hz
  exact (by simpa only [IsHexExtremal, hn] using
    (show Nonempty (G ≃g cycleGraph 6) from ⟨(hexNoFirst_iso hconn hC hp c hi).symm⟩))

/-- Sharp density and named equality classification in the induced-six-cycle
branch, independently of the global theorem's statement module.

The multi-apex rows all attain their order-specific envelope, and their actual
layer isomorphisms identify the named examples. In the one-apex branch equality
forces the second layer to be independent, giving the Gamma family. -/
theorem hex_extremal_density (hn : 7 ≤ Fintype.card V)
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) :
    ell G ≤ extremalDensity (Fintype.card V) ∧
    (ell G = extremalDensity (Fintype.card V) ↔ IsHexExtremal G) := by
  classical
  have hf : ell G ≤ extremalDensity (Fintype.card V) ∧
      (ell G = extremalDensity (Fintype.card V) → IsHexExtremal G) := by
    by_cases ht : 1 < Fintype.card (hexFirst c)
    · obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp ht
      rcases hexMulti_mass_table hconn hC hp c a b hab with h | h | h | h
      · obtain ⟨hk, hh, hc, hm⟩ := h
        have hi := hexTwo_zero_iso_h8 hconn hC hp c a b hab hk hh
        have he : IsHexExtremal G := by simpa only [IsHexExtremal, hc] using hi
        exact ⟨he.density_eq.le, fun _ => he⟩
      · obtain ⟨hk, hh, hc, hm⟩ := h
        have hi := hexTwo_one_iso_petersenMinus hconn hC hp c a b hab hk hh
        have he : IsHexExtremal G := by simpa only [IsHexExtremal, hc] using hi
        exact ⟨he.density_eq.le, fun _ => he⟩
      · obtain ⟨hk, hh, hc, hm⟩ := h
        have hi := hexThree_zero_iso_petersenMinus hconn hC hp c a b hab hk hh
        have he : IsHexExtremal G := by simpa only [IsHexExtremal, hc] using hi
        exact ⟨he.density_eq.le, fun _ => he⟩
      · obtain ⟨hk, hh, hc, hm⟩ := h
        have hi : Nonempty (G ≃g petersenGraph) := ⟨hexFull_iso hconn hC hp c hk hh⟩
        have he : IsHexExtremal G := by simpa only [IsHexExtremal, hc] using hi
        exact ⟨he.density_eq.le, fun _ => he⟩
    · by_cases ho : Fintype.card (hexFirst c) = 1
      · obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp ho
        exact hexOne_extremal hn hconn hC hp c a ha
      · have hz : Fintype.card (hexFirst c) = 0 := by omega
        have hi : IsEmpty (hexFirst c) := Fintype.card_eq_zero_iff.mp hz
        have e := hexNoFirst_iso hconn hC hp c hi
        have hc := Fintype.card_congr e.toEquiv
        simp only [Fintype.card_fin] at hc
        omega
  exact ⟨hf.1, hf.2, IsHexExtremal.density_eq⟩

/-- Including order six, all graphs in the induced-hexagon branch satisfy
its sharp named classification. -/
theorem hex_extremal_density_of_ge_six (hn : 6 ≤ Fintype.card V)
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) :
    ell G ≤ extremalDensity (Fintype.card V) ∧
    (ell G = extremalDensity (Fintype.card V) ↔ IsHexExtremal G) := by
  by_cases h7 : 7 ≤ Fintype.card V
  · exact hex_extremal_density h7 hconn hC hp c
  · have h6 : Fintype.card V = 6 := by omega
    have he := hex_six_extremal hconn hC hp c h6
    exact ⟨he.density_eq.le, fun _ => he, fun _ => he.density_eq⟩

/-- An embedded hexagon supplies the order hypothesis automatically. -/
theorem hex_extremal_density_of_cycle
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) :
    ell G ≤ extremalDensity (Fintype.card V) ∧
    (ell G = extremalDensity (Fintype.card V) ↔ IsHexExtremal G) := by
  have hn : 6 ≤ Fintype.card V := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective c c.injective
  exact hex_extremal_density_of_ge_six hn hconn hC hp c

end InducedPaths
