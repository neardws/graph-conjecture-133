/- Parameterized global minimal-counterexample assembly, without StatementsCore. -/
module
public import InducedPaths.SectionFiveGlobal
public import InducedPaths.OneTriangleAssembly
open Finset SimpleGraph
@[expose] public section
namespace InducedPaths
namespace SectionFiveGlobal
universe u
set_option maxHeartbeats 4000000
open Classical

/-- The universal low-loss input is Lemma 5.9, passed explicitly to avoid its
certificate/StatementsCore dependency cycle. -/
def UniversalLowLoss : Prop := ∀ {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj], H.Connected → StrongC4Free H →
    IsPkFree H 7 → 2 ≤ triangleCount H → ∃ v, deletionLoss H v ≤ 3

/-- Root-side input, independent of global mass bounds. -/
def UniversalRootBound : Prop := ∀ {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj], H.Connected → StrongC4Free H → ∀ r,
    RootedNoP4 H r → neighbourhoodIndependenceSum H ≤ 2 * (Fintype.card W - 1)

/-- Strict unique-triangle endgame. The high-loss assumption is the genuine
minimal-counterexample invariant, not the desired global conclusion. -/
def StrictOneTriangleEndgame : Prop := ∀ {W : Type u} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj], H.Connected → StrongC4Free H →
    IsPkFree H 7 → triangleCount H = 1 → (∀ v, ¬ IsCutVertex H v) →
    (∀ v, 4 ≤ deletionLoss H v) → neighbourhoodIndependenceSum H < 3 * Fintype.card W

/-- One-vertex deletion cardinality, with no dependence on chosen finite instances. -/
theorem delete_card {W : Type u} [Fintype W] [DecidableEq W] (v : W) :
    Fintype.card ({v}ᶜ : Set W) + 1 = Fintype.card W := by
  classical
  have h : Fintype.card ({v}ᶜ : Set W) = Fintype.card W - 1 := by
    calc
      _ = Fintype.card {x : W // ¬ x = v} := Fintype.card_congr
        (Equiv.subtypeEquivRight (fun x => by simp))
      _ = _ := by rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have hp : 0 < Fintype.card W := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

/-- Low-loss elimination in a minimal triangular counterexample. A smaller
triangular deletion is strict by induction; a triangle-free deletion at the
threshold must be Petersen and is ruled out by its concrete extension lemma. -/
theorem low_loss_strict_of_induction {W : Type u} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (hc : H.Connected)
    (hC : StrongC4Free H) (hp : IsPkFree H 7) (htri : 0 < triangleCount H)
    (hcut : ∀ v, ¬ IsCutVertex H v)
    (ih : ∀ (X : Set W) [Fintype X], Fintype.card X < Fintype.card W → (H.induce X).Connected →
      neighbourhoodIndependenceSum (H.induce X) ≤ 3 * Fintype.card X ∧
      (0 < triangleCount (H.induce X) →
        neighbourhoodIndependenceSum (H.induce X) < 3 * Fintype.card X))
    {v : W} (hl : deletionLoss H v ≤ 3) :
    neighbourhoodIndependenceSum H < 3 * Fintype.card W := by
  classical
  have hcard := delete_card v
  have hsmall : Fintype.card ({v}ᶜ : Set W) < Fintype.card W := by omega
  have hn : Nonempty ({v}ᶜ : Set W) := by
    by_contra hn
    letI : IsEmpty ({v}ᶜ : Set W) := ⟨fun x => hn ⟨x⟩⟩
    have hz : Fintype.card ({v}ᶜ : Set W) = 0 := Fintype.card_eq_zero
    have hT := triangleCount_induce_compl_add (G := H) v
    have hd : H.degree v = 0 := by
      rw [← H.card_neighborSet_eq_degree]
      apply Fintype.card_eq_zero_iff.mpr
      refine ⟨fun x => ?_⟩
      exact hn ⟨⟨x.val, by simpa using x.property.ne.symm⟩⟩
    have htv := two_mul_trianglesAt_le_degree hC v
    have ht0 : triangleCount (H.induce {v}ᶜ) = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro s hs
      have hsc := (mem_cliqueFinset_iff.mp hs).card_eq
      have hle := Finset.card_le_univ s
      omega
    change triangleCount (H.induce {v}ᶜ) = 0 at ht0
    change H.degree v = 0 at hd
    omega
  letI := hn
  have hdconn : (H.induce {v}ᶜ).Connected := by
    have hpre := hcut v
    simp only [IsCutVertex, not_not] at hpre
    exact ⟨hpre⟩
  have hi := ih ({v}ᶜ) hsmall hdconn
  have hl' : neighbourhoodIndependenceSum H ≤
      neighbourhoodIndependenceSum (H.induce {v}ᶜ) + 3 := by
    unfold deletionLoss at hl
    omega
  by_cases ht : 0 < triangleCount (H.induce {v}ᶜ)
  · have hs := hi.2 ht
    omega
  · have ht0 : triangleCount (H.induce {v}ᶜ) = 0 := by omega
    have hf := triangleFree_mass_bound hdconn
      (oneTriangle_cliqueFree_iff_triangleCount_zero.mpr ht0)
      (strongC4Free_induce (s := {v}ᶜ) hC) (oneTriangle_isPkFree_induce hp _)
    by_cases heq : neighbourhoodIndependenceSum (H.induce {v}ᶜ) =
        3 * Fintype.card ({v}ᶜ : Set W)
    · obtain ⟨e⟩ := hf.2.mp heq
      have htv := triangleCount_induce_compl_add (G := H) v
      exact mass_lt_of_delete_petersen hC v (by omega) e
    · omega

/-- Strong induction assembling the global theorem from independently meaningful
low-loss, rooted-side, and unique-triangle endgame inputs. No numbered global
theorem is used in any dependency. -/
theorem global_mass_parameterized (hlow : UniversalLowLoss.{u})
    (hroot : UniversalRootBound.{u}) (hend : StrictOneTriangleEndgame.{u})
    {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hc : H.Connected) (hC : StrongC4Free H) (hp : IsPkFree H 7) :
    neighbourhoodIndependenceSum H ≤ 3 * Fintype.card W ∧
      (0 < triangleCount H → neighbourhoodIndependenceSum H < 3 * Fintype.card W) := by
  classical
  generalize hn : Fintype.card W = n
  induction n using Nat.strong_induction_on generalizing W with
  | h n ih =>
    have hproper : ∀ (X : Set W) [Fintype X], Fintype.card X < Fintype.card W →
        (H.induce X).Connected →
        neighbourhoodIndependenceSum (H.induce X) ≤ 3 * Fintype.card X ∧
        (0 < triangleCount (H.induce X) →
          neighbourhoodIndependenceSum (H.induce X) < 3 * Fintype.card X) := by
      intro X instX hx hcx
      exact ih (Fintype.card X) (by omega) (H.induce X) hcx
        (strongC4Free_induce hC) (oneTriangle_isPkFree_induce hp X) rfl
    by_cases ht : triangleCount H = 0
    · have hf := triangleFree_mass_bound hc
        (oneTriangle_cliqueFree_iff_triangleCount_zero.mpr ht) hC hp
      constructor
      · simpa [hn] using hf.1
      · omega
    have hpos : 0 < triangleCount H := by omega
    suffices hs : neighbourhoodIndependenceSum H < 3 * Fintype.card W by
      simpa [hn] using (And.intro hs.le (fun (_ : 0 < triangleCount H) => hs))
    by_cases hcut : ∃ s, IsCutVertex H s
    · obtain ⟨s, hs⟩ := hcut
      exact cut_strict_mass hc hp hs
        (fun X r hcx hr => hroot (H.induce X) hcx (strongC4Free_induce hC) r hr)
        (fun X hx hcx => (hproper X hx hcx).1)
    have hnocut : ∀ v, ¬ IsCutVertex H v := by simpa using hcut
    by_cases hl : ∃ v, deletionLoss H v ≤ 3
    · obtain ⟨v, hv⟩ := hl
      exact low_loss_strict_of_induction hc hC hp hpos hnocut hproper hv
    have hlarge : ∀ v, 4 ≤ deletionLoss H v := by
      push Not at hl
      intro v
      have := hl v
      omega
    have hT : triangleCount H = 1 := by
      by_contra hn1
      have htwo : 2 ≤ triangleCount H := by omega
      obtain ⟨v, hv⟩ := hlow H hc hC hp htwo
      have := hlarge v
      omega
    exact hend H hc hC hp hT hnocut hlarge

/-- Exact bound and equality, with the certificate-dependent Lemma 5.9
explicitly parameterized and no dependency on a sorry-numbered theorem. -/
theorem global_mass_iff_petersen (hlow : UniversalLowLoss.{u})
    (hroot : UniversalRootBound.{u}) (hend : StrictOneTriangleEndgame.{u})
    {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
    (hc : H.Connected) (hC : StrongC4Free H) (hp : IsPkFree H 7) :
    neighbourhoodIndependenceSum H ≤ 3 * Fintype.card W ∧
      (neighbourhoodIndependenceSum H = 3 * Fintype.card W ↔ Nonempty (H ≃g petersenGraph)) := by
  classical
  have hg := global_mass_parameterized hlow hroot hend H hc hC hp
  refine ⟨hg.1, ?_⟩
  constructor
  · intro heq
    have ht : triangleCount H = 0 := by
      by_contra hn
      have hs := hg.2 (by omega)
      omega
    exact (triangleFree_mass_bound hc
      (oneTriangle_cliqueFree_iff_triangleCount_zero.mpr ht) hC hp).2.mp heq
  · rintro ⟨e⟩
    have hm := neighbourhoodIndependenceSum_iso e
    have hn := Fintype.card_congr e.toEquiv
    rw [petersen_mass] at hm
    rw [petersen_vertex_card] at hn
    omega

end SectionFiveGlobal
end InducedPaths
