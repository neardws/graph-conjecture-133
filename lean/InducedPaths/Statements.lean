/- Public paper statements. The universal low-loss certificate is available
before Theorems 5.10, 5.11 and 5.5 are assembled, avoiding a dependency cycle.
Import this module (or InducedPaths) for the complete numbered interface. -/
module

public import InducedPaths.StatementsCore
public import InducedPaths.LemmaFiveNine
public import InducedPaths.GlobalInduction
public import InducedPaths.OneTriangleStrict
public import InducedPaths.BipartiteMass

open SimpleGraph

@[expose] public section
namespace InducedPaths
variable {V : Type*} {G : SimpleGraph V}

/-- Lemma 5.9, including actual seed embeddings, executable loss semantics,
normalized ambient extensions, and checked induced-path witnesses at every node. -/
theorem lemma_5_9 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 7) (htri : 2 ≤ triangleCount G) :
    ∃ v, deletionLoss G v ≤ 3 :=
  lemma_5_9_proof hconn hC hp htri

/-- Theorem 5.10. -/
theorem theorem_5_10 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 7) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V ∧
      (neighbourhoodIndependenceSum G = 3 * Fintype.card V ↔
        Nonempty (G ≃g petersenGraph)) := by
  apply SectionFiveGlobal.global_mass_iff_petersen (hlow := ?_) (hroot := ?_)
    (hend := ?_) G hconn hC hp
  · intro W _ _ H _ hc hC hp ht
    exact lemma_5_9 hc hC hp ht
  · intro W _ _ H _ hc hC r hr
    exact (lemma_5_3 hc hC hr).trans (Nat.sub_le _ _)
  · intro W _ _ H _ hc hC hp ht hcut _
    exact oneTriangle_strict_noCut hc hC hp ht.le (by omega) hcut

/-- Theorem 5.11, REAL-133 for `ℓ ≤ 4`. -/
theorem theorem_5_11 [Fintype V] [DecidableEq V] (hell : ell G ≤ 4)
    (hn : 2 ≤ Fintype.card V) (hconn : G.Connected) :
    (inducedPathOrder G : ℚ) ≥ (radiusNat G : ℚ) + ell G ^ cC4 G := by
  classical
  by_cases hC : StrongC4Free G
  · have hc : cC4 G = 1 := by simp [cC4, hC]
    rw [hc, pow_one]
    haveI : Nonempty V := hconn.nonempty
    have hnQ : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    have density_bound (k : ℕ)
        (hS : neighbourhoodIndependenceSum G ≤ k * Fintype.card V) :
        ell G ≤ k := by
      rw [ell, div_le_iff₀ hnQ]
      exact_mod_cast hS
    have hrpos : 1 ≤ radiusNat G := by
      by_contra h
      have hr0 : radiusNat G = 0 := by omega
      have hrE : G.radius = 0 := by
        rw [← ENat.natCast_toNat ((G.radius_ne_top_iff).2 hconn)]
        change (radiusNat G : ℕ∞) = 0
        simp [hr0]
      haveI : Subsingleton V := ((G.radius_eq_zero_iff).1 hrE).2
      have : Fintype.card V ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr inferInstance
      omega
    have hess := erdos_saks_sos G hconn
    by_cases hr1 : radiusNat G = 1
    · obtain ⟨u, _, _, _, h⟩ := lemma_3_1 hconn hC hr1
      exact h
    by_contra hfail
    have hlt : (inducedPathOrder G : ℚ) < (radiusNat G : ℚ) + ell G := lt_of_not_ge hfail
    have hp_le : inducedPathOrder G ≤ radiusNat G + 3 := by
      have : (inducedPathOrder G : ℚ) < ((radiusNat G + 4 : ℕ) : ℚ) := by
        push_cast
        linarith
      have : inducedPathOrder G < radiusNat G + 4 := Nat.cast_lt.mp this
      omega
    have hr_le : radiusNat G ≤ 4 := by omega
    interval_cases hr : radiusNat G
    · omega
    · have hpge := lemma_3_2 hconn hC (by omega : 2 ≤ radiusNat G)
      by_cases hp4 : inducedPathOrder G ≤ 4
      · have hfree : IsPkFree G 5 :=
          (isPkFree_iff_inducedPathOrder_lt G 5).2 (by omega)
        have he := density_bound 2 (lemma_3_3 hconn hC hfree).2
        have hpQ : (4 : ℚ) ≤ inducedPathOrder G := by exact_mod_cast hpge
        norm_num [hr] at hlt
        norm_num at he
        linarith
      · have hfree : IsPkFree G 6 :=
          (isPkFree_iff_inducedPathOrder_lt G 6).2 (by omega)
        have he := density_bound 3 (theorem_3_6 hconn hC hfree hn).2.2.1
        have hpQ : (5 : ℚ) ≤ inducedPathOrder G := by exact_mod_cast (show 5 ≤ inducedPathOrder G by omega)
        norm_num [hr] at hlt
        norm_num at he
        linarith
    · by_cases hp5 : inducedPathOrder G ≤ 5
      · have hfree : IsPkFree G 6 :=
          (isPkFree_iff_inducedPathOrder_lt G 6).2 (by omega)
        have he : ell G ≤ 2 := by
          rcases lemma_3_5 hconn hC hfree with ⟨v, hv⟩ | he
          swap
          · obtain ⟨e⟩ := he
            have hcard : Fintype.card V = 6 := by
              simpa using Fintype.card_congr e.toEquiv
            rw [ell, neighbourhoodIndependenceSum_iso e, cycle6_mass, hcard]
            norm_num
          · have : radiusNat G ≤ 2 :=
              ENat.toNat_le_of_le_natCast (G.radius_le_eccent.trans hv)
            omega
        have hpQ : (5 : ℚ) ≤ inducedPathOrder G := by exact_mod_cast (show 5 ≤ inducedPathOrder G by omega)
        norm_num [hr] at hlt
        norm_num at he
        linarith
      · have hfree : IsPkFree G 7 :=
          (isPkFree_iff_inducedPathOrder_lt G 7).2 (by omega)
        have he := density_bound 3 (theorem_5_10 hconn hC hfree).1
        have hpQ : (6 : ℚ) ≤ inducedPathOrder G := by exact_mod_cast (show 6 ≤ inducedPathOrder G by omega)
        norm_num [hr] at hlt
        norm_num at he
        linarith
    · have hp7 : inducedPathOrder G = 7 := by omega
      have he := (corollary_4_4 hconn hC hr hp7).2
      norm_num [hr, hp7] at hlt
      linarith
  · have hc : cC4 G = 0 := by simp [cC4, hC]
    have hgeo := inducedPathOrder_ge_radius_succ (G := G) hconn
    rw [hc, pow_zero]
    exact_mod_cast hgeo

/-- Theorem 5.5. -/
theorem theorem_5_5 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (htri : G.CliqueFree 3) (hC : StrongC4Free G) (hp : IsPkFree G 7) :
    2 * edgeCount G ≤ 3 * Fintype.card V ∧
      (2 * edgeCount G = 3 * Fintype.card V ↔ Nonempty (G ≃g petersenGraph)) ∧
      (inducedPathOrder G ≤ 6 → GenK 3) ∧
      (G.IsBipartite → inducedPathOrder G ≤ 6 →
        neighbourhoodIndependenceSum G + 1 ≤ 3 * Fintype.card V) := by
  obtain ⟨hb, he⟩ := triangleFree_edge_bound hconn htri hC hp
  refine ⟨hb, he, ?_, ?_⟩
  · intro _
    intro W _ _ H hc hC horder
    classical
    exact (theorem_5_10 hc hC
      ((isPkFree_iff_inducedPathOrder_lt H 7).2 (by omega))).1
  · intro hbip _
    exact bipartite_triangleFree_mass_strict hconn htri hC hp hbip


end InducedPaths
