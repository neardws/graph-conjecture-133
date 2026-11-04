/-
Statements of the preprint, in dependency order. Proofs are `sorry` except where noted.
Paper numbers refer to `paper/main.tex` at `c6d3eb76`.
-/
module

public import InducedPaths.Basic
public import InducedPaths.Certificate
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Card

open scoped SimpleGraph
open Finset SimpleGraph

set_option linter.style.haveILetI false

@[expose] public section

namespace InducedPaths

variable {V : Type*} {G : SimpleGraph V}

/-! ### Lemma 2.1 assembled -/

/-- Lemma 2.1. At most one common neighbour, `λ(v) = d(v) - t(v)`, `λ(v)` equals the
number of components of `G[N(v)]`, and `S(G) = 2e(G) - 3T(G)`. -/
theorem lemma_2_1 (hG : StrongC4Free G) [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    (∀ x y, x ≠ y → (G.commonNeighbors x y).Subsingleton) ∧
      (∀ v, lambda G v = G.degree v - trianglesAt G v) ∧
      (∀ v, Nat.card (G.induce (G.neighborSet v)).ConnectedComponent = lambda G v) ∧
      neighbourhoodIndependenceSum G = 2 * edgeCount G - 3 * triangleCount G := by
  refine ⟨?_, ?_, ?_, strongC4Free_S_identity hG⟩
  · intro x y hxy
    exact commonNeighbors_subsingleton hG hxy
  · intro v
    exact lambda_eq_degree_sub_trianglesAt hG v
  · intro v
    exact lambda_eq_ncard_components hG v

/-- Lemma 2.2, the numeric identity `2λ(v) - t(v) = 2d(v) - 3t(v)`. -/
theorem lemma_2_2_lambda (hG : StrongC4Free G) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (v : V) :
    2 * lambda G v - trianglesAt G v = 2 * G.degree v - 3 * trianglesAt G v := by
  have h := lambda_add_trianglesAt hG v
  omega

/-- Lemma 2.2. `L(v) = S(G) - S(G - v) = 2d(v) - 3t(v)`. -/
theorem lemma_2_2 (hG : StrongC4Free G) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (v : V) :
    deletionLoss G v = 2 * G.degree v - 3 * trianglesAt G v := by
  have hS := strongC4Free_S_identity hG
  have hC' : StrongC4Free (G.induce ({v}ᶜ : Set V)) :=
    strongC4Free_induce (s := ({v}ᶜ : Set V)) hG
  have hS' := strongC4Free_S_identity hC'
  have he := edgeCount_induce_compl_add (G := G) v
  have ht := triangleCount_induce_compl_add (G := G) v
  have h3 := three_mul_trianglesAt_le_two_degree hG v
  have h3' := three_mul_triangleCount_le_two_edge hC'
  have hmain : neighbourhoodIndependenceSum G =
      neighbourhoodIndependenceSum (G.induce ({v}ᶜ : Set V)) +
        (2 * G.degree v - 3 * trianglesAt G v) := by
    omega
  rw [deletionLoss, hmain]
  exact Nat.add_sub_cancel_left _ _

/-- Lemma 2.3. No `C₄`-free hypothesis. `A` and `B` are the two sides of `G - v`. -/
theorem lemma_2_3 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {v : V}
    (A B : Finset V) (hA : A.Nonempty) (hB : B.Nonempty) (hdisj : Disjoint A B)
    (hcover : (A ∪ B : Set V) = {w | w ≠ v})
    (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    neighbourhoodIndependenceSum G =
      neighbourhoodIndependenceSum (G.induce (insert v A : Set V)) +
        neighbourhoodIndependenceSum (G.induce (insert v B : Set V)) := by
  have _hAB : A.Nonempty ∧ B.Nonempty := ⟨hA, hB⟩
  have hvA : v ∉ A := by
    intro hv
    have hvmem : v ∈ (A ∪ B : Set V) := by simpa [Finset.mem_coe] using mem_union_left B hv
    rw [hcover] at hvmem
    exact hvmem rfl
  have hvB : v ∉ B := by
    intro hv
    have hvmem : v ∈ (A ∪ B : Set V) := by simpa [Finset.mem_coe] using mem_union_right A hv
    rw [hcover] at hvmem
    exact hvmem rfl
  have hvAB : v ∉ A ∪ B := by simp [hvA, hvB]
  have hmem : ∀ x, x ∈ A ∪ B ↔ x ≠ v := by
    intro x
    constructor
    · intro hx hxv
      exact hvAB (hxv ▸ hx)
    · intro hx
      have hxset : x ∈ (A ∪ B : Set V) := by
        rw [hcover]
        simpa using hx
      simpa [Finset.mem_coe] using hxset
  have hNA : ∀ a ∈ A, G.neighborSet a ⊆ (insert v A : Set V) := by
    intro a ha w hw
    have hadj : G.Adj a w := by simpa [mem_neighborSet] using hw
    by_cases hwv : w = v
    · subst hwv
      exact Set.mem_insert _ _
    · have hwAB : w ∈ A ∪ B := (hmem w).mpr hwv
      rcases mem_union.mp hwAB with hwA | hwB
      · exact Set.mem_insert_of_mem _ (by simpa [Finset.mem_coe] using hwA)
      · exact (hno a ha w hwB hadj).elim
  have hNB : ∀ b ∈ B, G.neighborSet b ⊆ (insert v B : Set V) := by
    intro b hb w hw
    have hadj : G.Adj b w := by simpa [mem_neighborSet] using hw
    by_cases hwv : w = v
    · subst hwv
      exact Set.mem_insert _ _
    · have hwAB : w ∈ A ∪ B := (hmem w).mpr hwv
      rcases mem_union.mp hwAB with hwA | hwB
      · exact (hno w hwA b hb hadj.symm).elim
      · exact Set.mem_insert_of_mem _ (by simpa [Finset.mem_coe] using hwB)
  let sA : Set V := (insert v A : Set V)
  let sB : Set V := (insert v B : Set V)
  haveI : DecidablePred (· ∈ sA) := fun _ => Classical.propDecidable _
  haveI : DecidablePred (· ∈ sB) := fun _ => Classical.propDecidable _
  have hvAs : v ∈ sA := by simp [sA]
  have hvBs : v ∈ sB := by simp [sB]
  let fA : V → ℕ := fun x =>
    if hx : x ∈ sA then lambda (G.induce sA) ⟨x, hx⟩ else 0
  let fB : V → ℕ := fun x =>
    if hx : x ∈ sB then lambda (G.induce sB) ⟨x, hx⟩ else 0
  have hsumA : neighbourhoodIndependenceSum (G.induce sA) = ∑ x ∈ insert v A, fA x := by
    rw [neighbourhoodIndependenceSum]
    have hpt : ∀ i : sA, lambda (G.induce sA) i = fA i := by
      intro i
      have hi : (i : V) ∈ sA := i.2
      have heq : (⟨(i : V), hi⟩ : sA) = i := Subtype.ext rfl
      simp only [fA]
      rw [dite_eq_left hi, heq]
    have : (∑ i : sA, lambda (G.induce sA) i) = ∑ i : sA, fA (i : V) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact hpt i
    rw [this, Finset.sum_set_coe]
    have hto : sA.toFinset = insert v A := by
      simp [sA]
    rw [hto]
  have hsumB : neighbourhoodIndependenceSum (G.induce sB) = ∑ x ∈ insert v B, fB x := by
    rw [neighbourhoodIndependenceSum]
    have hpt : ∀ i : sB, lambda (G.induce sB) i = fB i := by
      intro i
      have hi : (i : V) ∈ sB := i.2
      have heq : (⟨(i : V), hi⟩ : sB) = i := Subtype.ext rfl
      simp only [fB]
      rw [dite_eq_left hi, heq]
    have : (∑ i : sB, lambda (G.induce sB) i) = ∑ i : sB, fB (i : V) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact hpt i
    rw [this, Finset.sum_set_coe]
    have hto : sB.toFinset = insert v B := by
      simp [sB]
    rw [hto]
  have hfv : fA v = lambda (G.induce sA) ⟨v, hvAs⟩ := by simp only [fA]; rw [dite_eq_left hvAs]
  have hgv : fB v = lambda (G.induce sB) ⟨v, hvBs⟩ := by simp only [fB]; rw [dite_eq_left hvBs]
  have hfA : ∀ a ∈ A, fA a = lambda G a := by
    intro a ha
    have ha' : a ∈ sA := Set.mem_insert_of_mem _ (by simpa [Finset.mem_coe] using ha)
    have hfa : fA a = lambda (G.induce sA) ⟨a, ha'⟩ := by simp only [fA]; rw [dite_eq_left ha']
    rw [hfa, lambda_induce_eq ha' (hNA a ha)]
  have hfB : ∀ b ∈ B, fB b = lambda G b := by
    intro b hb
    have hb' : b ∈ sB := Set.mem_insert_of_mem _ (by simpa [Finset.mem_coe] using hb)
    have hfb : fB b = lambda (G.induce sB) ⟨b, hb'⟩ := by simp only [fB]; rw [dite_eq_left hb']
    rw [hfb, lambda_induce_eq hb' (hNB b hb)]
  have hS1 : neighbourhoodIndependenceSum (G.induce sA) =
      lambda (G.induce sA) ⟨v, hvAs⟩ + ∑ a ∈ A, lambda G a := by
    rw [hsumA, sum_insert hvA, hfv]
    exact congrArg _ (sum_congr rfl hfA)
  have hS2 : neighbourhoodIndependenceSum (G.induce sB) =
      lambda (G.induce sB) ⟨v, hvBs⟩ + ∑ b ∈ B, lambda G b := by
    rw [hsumB, sum_insert hvB, hgv]
    exact congrArg _ (sum_congr rfl hfB)
  have hinterA : G.neighborSet v ∩ sA = G.neighborSet v ∩ (A : Set V) := by
    ext x
    constructor
    · rintro ⟨hx, hmem⟩
      rcases Set.mem_insert_iff.mp hmem with rfl | hxA
      · simp [mem_neighborSet] at hx
      · exact ⟨hx, hxA⟩
    · rintro ⟨hx, hxA⟩
      exact ⟨hx, Set.mem_insert_of_mem _ hxA⟩
  have hinterB : G.neighborSet v ∩ sB = G.neighborSet v ∩ (B : Set V) := by
    ext x
    constructor
    · rintro ⟨hx, hmem⟩
      rcases Set.mem_insert_iff.mp hmem with rfl | hxB
      · simp [mem_neighborSet] at hx
      · exact ⟨hx, hxB⟩
    · rintro ⟨hx, hxB⟩
      exact ⟨hx, Set.mem_insert_of_mem _ hxB⟩
  have hlamvA : lambda (G.induce sA) ⟨v, hvAs⟩ =
      alphaIn G (G.neighborSet v ∩ (A : Set V)) := by
    rw [lambda_eq_alphaIn_neighbor_inter hvAs]
    exact alphaIn_congr hinterA
  have hlamvB : lambda (G.induce sB) ⟨v, hvBs⟩ =
      alphaIn G (G.neighborSet v ∩ (B : Set V)) := by
    rw [lambda_eq_alphaIn_neighbor_inter hvBs]
    exact alphaIn_congr hinterB
  have hNsplit : G.neighborSet v =
      (G.neighborSet v ∩ (A : Set V)) ∪ (G.neighborSet v ∩ (B : Set V)) := by
    ext x
    constructor
    · intro hx
      have hxne : x ≠ v := by
        intro hxv
        subst hxv
        simp [mem_neighborSet] at hx
      rcases mem_union.mp ((hmem x).mpr hxne) with hxA | hxB
      · exact Or.inl ⟨hx, by simpa [Finset.mem_coe] using hxA⟩
      · exact Or.inr ⟨hx, by simpa [Finset.mem_coe] using hxB⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hdisjN : Disjoint (G.neighborSet v ∩ (A : Set V)) (G.neighborSet v ∩ (B : Set V)) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro ⟨⟨_, ha⟩, _, hb⟩
    exact Finset.disjoint_left.mp hdisj (by simpa [Finset.mem_coe] using ha)
      (by simpa [Finset.mem_coe] using hb)
  have hnoN : ∀ ⦃a b : V⦄, a ∈ G.neighborSet v ∩ (A : Set V) →
      b ∈ G.neighborSet v ∩ (B : Set V) → ¬ G.Adj a b := by
    intro a b ha hb
    exact hno a (by simpa [Finset.mem_coe] using ha.2) b (by simpa [Finset.mem_coe] using hb.2)
  have hadd : lambda G v =
      lambda (G.induce sA) ⟨v, hvAs⟩ + lambda (G.induce sB) ⟨v, hvBs⟩ := by
    rw [hlamvA, hlamvB, lambda]
    conv_lhs => rw [hNsplit]
    exact alphaIn_union_no_cross hdisjN hnoN
  have huniv : (univ : Finset V) = insert v (A ∪ B) := by
    ext x
    simp only [mem_univ, true_iff, mem_insert]
    by_cases hx : x = v
    · exact Or.inl hx
    · exact Or.inr ((hmem x).mpr hx)
  have hSG : neighbourhoodIndependenceSum G =
      lambda G v + (∑ a ∈ A, lambda G a + ∑ b ∈ B, lambda G b) := by
    rw [neighbourhoodIndependenceSum, huniv, sum_insert hvAB, sum_union hdisj]
  calc neighbourhoodIndependenceSum G
      = lambda G v + (∑ a ∈ A, lambda G a + ∑ b ∈ B, lambda G b) := hSG
    _ = lambda (G.induce sA) ⟨v, hvAs⟩ + lambda (G.induce sB) ⟨v, hvBs⟩ +
          (∑ a ∈ A, lambda G a + ∑ b ∈ B, lambda G b) := by rw [hadd]
    _ = (lambda (G.induce sA) ⟨v, hvAs⟩ + ∑ a ∈ A, lambda G a) +
          (lambda (G.induce sB) ⟨v, hvBs⟩ + ∑ b ∈ B, lambda G b) := by ac_rfl
    _ = neighbourhoodIndependenceSum (G.induce sA) +
          neighbourhoodIndependenceSum (G.induce sB) := by rw [← hS1, ← hS2]

/-- Lemma 2.7. A connected strong `C₄`-free `P₄`-free graph on at least two vertices
has a universal vertex. -/
theorem lemma_2_7 [Fintype V] [DecidableEq V] (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 4) (hcard : 2 ≤ Fintype.card V) :
    ∃ u, ∀ v, v = u ∨ G.Adj u v := by
  have hcompl : ¬ Gᶜ.Connected := (seinsche G hcard hp).resolve_left (fun h => h hconn)
  haveI : Nonempty V := hconn.nonempty
  have hpre : ¬ Gᶜ.Preconnected := by
    intro hpre
    exact hcompl ⟨hpre⟩
  obtain ⟨x, y, hxy⟩ : ∃ x y, ¬ Gᶜ.Reachable x y := by
    rw [Preconnected] at hpre
    push Not at hpre
    exact hpre
  let comp : Set V := {z | Gᶜ.Reachable x z}
  have hxC : x ∈ comp := Reachable.refl (G := Gᶜ) x
  have hyC : y ∉ comp := hxy
  have hcross {p q : V} (hp : p ∈ comp) (hq : q ∉ comp) : G.Adj p q := by
    have hne : p ≠ q := by
      intro h
      exact hq (h ▸ hp)
    by_contra hnot
    have hreach : Gᶜ.Reachable x q :=
      hp.trans (((compl_adj G p q).mpr ⟨hne, hnot⟩).reachable)
    exact hq hreach
  have hnotboth : ¬ (1 < comp.ncard ∧ 1 < compᶜ.ncard) := by
    intro ⟨h1, h2⟩
    obtain ⟨p, hp, p', hp', hpp⟩ := (Set.one_lt_ncard (s := comp)).mp h1
    obtain ⟨q, hq, q', hq', hqq⟩ := (Set.one_lt_ncard (s := compᶜ)).mp h2
    exact hC (fourCycle_isContained
      (hcross hp hq)
      ((hcross hp' hq).symm)
      (hcross hp' hq')
      ((hcross hp hq').symm)
      hpp hqq)
  have hpos : 0 < comp.ncard := (Set.ncard_pos).mpr ⟨x, hxC⟩
  have hpos' : 0 < compᶜ.ncard := (Set.ncard_pos).mpr ⟨y, hyC⟩
  by_cases h1 : comp.ncard = 1
  · obtain ⟨u, hu⟩ := Set.ncard_eq_one.mp h1
    refine ⟨u, fun v => ?_⟩
    by_cases hv : v = u
    · exact Or.inl hv
    · have huC : u ∈ comp := by simp [hu]
      have hvC : v ∉ comp := by
        intro hvC
        have : v ∈ ({u} : Set V) := by simpa [hu] using hvC
        exact hv (by simpa using this)
      exact Or.inr (hcross huC hvC)
  · by_cases h2 : compᶜ.ncard = 1
    · obtain ⟨u, hu⟩ := Set.ncard_eq_one.mp h2
      refine ⟨u, fun v => ?_⟩
      by_cases hv : v = u
      · exact Or.inl hv
      · have hvC : v ∈ comp := by
          have hvnot : v ∉ compᶜ := by
            rw [hu]
            simpa using hv
          simpa using hvnot
        have huC : u ∉ comp := by
          rw [← Set.mem_compl_iff, hu]
          exact Set.mem_singleton u
        exact Or.inr ((hcross hvC huC).symm)
    · exact False.elim (hnotboth ⟨by omega, by omega⟩)

/-- Lemma 2.10. Proved in the preprint; not an external axiom. -/
theorem lemma_2_10 [Fintype V] [DecidableEq V] (hconn : G.Connected)
    (htri : G.CliqueFree 3) (hC : StrongC4Free G) (hp : IsPkFree G 7)
    (hcut : ∀ v, ¬ IsCutVertex G v) : ¬ HasCliqueCutset G := by
  -- missing: a clique cutset in a triangle-free strong `C₄`-free graph produces an induced `P₇`
  sorry

/-- A connected finite graph satisfies `p ≥ r + 1` by a geodesic. Used for `c_{C₄} = 0`. -/
theorem inducedPathOrder_ge_radius_succ [Fintype V] [DecidableEq V] (hconn : G.Connected) :
    radiusNat G + 1 ≤ inducedPathOrder G := by
  haveI : Nonempty V := hconn.nonempty
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_radius_of_finite
  have hreach : G.Reachable u v := hconn u v
  have hdist : G.dist u v = radiusNat G := by
    apply Nat.cast_injective (R := ℕ∞)
    rw [hreach.coe_dist_eq_edist, huv, radiusNat, ENat.natCast_toNat]
    exact (G.radius_ne_top_iff).2 hconn
  obtain ⟨p, _, hlen⟩ := hreach.exists_path_of_dist
  have hcont := pathGraph_isIndContained_of_length_eq_dist p hlen
  have hle := le_csSup (inducedPathOrder_bddAbove G) hcont
  rw [hlen, hdist] at hle
  exact hle

/-! ### Section 3 -/

/-- Lemma 3.1. `m` is the number of edges of `G[N(u)]` for a dominating vertex `u`. -/
theorem lemma_3_1 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hr : radiusNat G = 1) :
    ∃ u, (∀ v, v = u ∨ G.Adj u v) ∧
      neighbourhoodIndependenceSum G =
        2 * (Fintype.card V - 1) - edgeCount (G.induce (G.neighborSet u)) ∧
      ell G < 2 ∧
      (inducedPathOrder G : ℚ) ≥ (radiusNat G : ℚ) + ell G := by
  haveI : Nonempty V := hconn.nonempty
  have hneTop : G.radius ≠ ⊤ := (G.radius_ne_top_iff).2 hconn
  have hrE : G.radius = 1 := by
    rw [← ENat.natCast_toNat hneTop]
    exact_mod_cast hr
  obtain ⟨u, hu⟩ := G.exists_eccent_eq_radius
  have hec : G.eccent u ≤ 1 := by rw [hu, hrE]
  have hdom : ∀ v, v = u ∨ G.Adj u v := by
    intro v
    by_cases hv : v = u
    · exact Or.inl hv
    · exact Or.inr (((eccent_le_one_iff u).mp hec) v (Ne.symm hv))
  have hdeg : G.degree u = Fintype.card V - 1 := by
    rw [← card_neighborFinset_eq_degree]
    have hnbr : G.neighborFinset u = Finset.univ.erase u := by
      ext w
      simp only [mem_neighborFinset, mem_erase, mem_univ, and_true]
      constructor
      · exact fun h => h.ne.symm
      · intro hne
        exact (hdom w).resolve_left hne
    rw [hnbr, card_erase_of_mem (mem_univ _), card_univ]
  have hm : trianglesAt G u = edgeCount (G.induce (G.neighborSet u)) := by
    simpa [edgeCount] using (trianglesAt_eq_neighborEdges (G := G) u)
  have hlu : lambda G u =
      Fintype.card V - 1 - edgeCount (G.induce (G.neighborSet u)) := by
    rw [lambda_eq_degree_sub_trianglesAt hC u, hdeg, hm]
  have hlam : ∀ v ∈ univ.erase u, lambda G v = 1 := by
    intro v hv
    exact lambda_eq_one_of_universal hC hdom (mem_erase.mp hv).1
  have hS : neighbourhoodIndependenceSum G =
      2 * (Fintype.card V - 1) - edgeCount (G.induce (G.neighborSet u)) := by
    have hsplit :=
      (Finset.add_sum_erase univ (fun v => lambda G v) (mem_univ u)).symm
    rw [neighbourhoodIndependenceSum, hsplit]
    have hrest : ∑ v ∈ univ.erase u, lambda G v = Fintype.card V - 1 := by
      rw [sum_congr rfl hlam]
      simp [sum_const, card_erase_of_mem (mem_univ u), card_univ]
    rw [hrest, hlu]
    have hmle : edgeCount (G.induce (G.neighborSet u)) ≤ Fintype.card V - 1 := by
      rw [← hm, ← hdeg]
      have := lambda_add_trianglesAt hC u
      omega
    omega
  have hell : ell G < 2 := by
    have hSle : neighbourhoodIndependenceSum G ≤ 2 * (Fintype.card V - 1) := by
      have := hS
      omega
    have hn1 : 1 ≤ Fintype.card V := by
      have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr hconn.nonempty
      omega
    rw [ell, div_lt_iff₀ (by exact_mod_cast hn1)]
    calc (neighbourhoodIndependenceSum G : ℚ)
        ≤ (2 * (Fintype.card V - 1) : ℕ) := by exact_mod_cast hSle
      _ = 2 * ((Fintype.card V : ℚ) - 1) := by
          rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hn1, Nat.cast_one]
      _ < 2 * (Fintype.card V : ℚ) := by
          have : (0 : ℚ) < Fintype.card V := by exact_mod_cast hn1
          linarith
  refine ⟨u, hdom, hS, hell, ?_⟩
  by_cases hcompl : ∀ a b : V, a ≠ b → G.Adj a b
  · have hn2 : 2 ≤ Fintype.card V := by
      have hne0 : G.radius ≠ 0 := by
        intro h0
        have : radiusNat G = 0 := by simp [radiusNat, h0]
        omega
      have hnot : ¬ Subsingleton V := fun hs =>
        hne0 ((G.radius_eq_zero_iff).2 ⟨hconn.nonempty, hs⟩)
      rw [subsingleton_iff] at hnot
      push Not at hnot
      obtain ⟨a, b, hne⟩ := hnot
      haveI : Nontrivial V := ⟨⟨a, b, hne⟩⟩
      exact Nat.succ_le_of_lt Fintype.one_lt_card
    have hn3 : Fintype.card V ≤ 3 := by
      by_contra hlt
      have h4 : 4 ≤ Fintype.card V := by omega
      obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := V) h4
      exact hC (fourCycle_isContained
        (hcompl (f 0) (f 1) (f.injective.ne (by decide : (0 : Fin 4) ≠ 1)))
        (hcompl (f 1) (f 2) (f.injective.ne (by decide : (1 : Fin 4) ≠ 2)))
        (hcompl (f 2) (f 3) (f.injective.ne (by decide : (2 : Fin 4) ≠ 3)))
        (hcompl (f 3) (f 0) (f.injective.ne (by decide : (3 : Fin 4) ≠ 0)))
        (f.injective.ne (by decide : (0 : Fin 4) ≠ 2))
        (f.injective.ne (by decide : (1 : Fin 4) ≠ 3)))
    have h2e := two_mul_edgeFinset_card_le
      (H := G.induce (G.neighborSet u)) (fun w => neighborhood_degree_le_one hC u w)
    have hcardN : Fintype.card (G.neighborSet u) = Fintype.card V - 1 := by
      rw [G.card_neighborSet_eq_degree u, hdeg]
    have hmval : edgeCount (G.induce (G.neighborSet u)) = Fintype.card V - 2 := by
      have hcard : Fintype.card V = 2 ∨ Fintype.card V = 3 := by omega
      rcases hcard with hcard | hcard
      · have hb : (G.induce (G.neighborSet u)).edgeFinset.card = 0 := by
          have h2 : 2 * (G.induce (G.neighborSet u)).edgeFinset.card ≤ 1 := by
            simpa [hcardN, hcard] using h2e
          omega
        rw [edgeCount, hb, hcard]
      · let H := G.induce (G.neighborSet u)
        have hnt : 1 < Fintype.card (G.neighborSet u) := by rw [hcardN, hcard]; omega
        obtain ⟨x, y, hxy⟩ := (Fintype.one_lt_card_iff).mp hnt
        have hadj : H.Adj x y := by
          rw [induce_adj]
          exact hcompl x.1 y.1 (Subtype.coe_ne_coe.mpr hxy)
        have hmem : s(x, y) ∈ H.edgeFinset := by simp [mem_edgeFinset, hadj]
        have hb : H.edgeFinset.card = 1 := by
          have hge : 1 ≤ H.edgeFinset.card :=
            Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨s(x, y), hmem⟩)
          have h2 : 2 * H.edgeFinset.card ≤ 2 := by
            simpa [hcardN, hcard] using h2e
          omega
        rw [edgeCount, hb, hcard]
    have hell1 : ell G = 1 := by
      rw [ell, hS, hmval]
      have hcard : Fintype.card V = 2 ∨ Fintype.card V = 3 := by omega
      rcases hcard with hcard | hcard <;> rw [hcard] <;> norm_num
    have hp := inducedPathOrder_ge_radius_succ hconn
    rw [hr] at hp
    rw [hell1, hr]
    exact_mod_cast hp
  · push Not at hcompl
    obtain ⟨x, y, hxy, hnot⟩ := hcompl
    have hdist : 2 ≤ G.dist x y := by
      have h0 : G.dist x y ≠ 0 := by
        intro h
        exact hxy ((dist_eq_zero_iff_eq_or_not_reachable.mp h).resolve_right
          (fun hnotreach => hnotreach (hconn x y)))
      have h1 : G.dist x y ≠ 1 := fun h => hnot (dist_eq_one_iff_adj.mp h)
      omega
    obtain ⟨p, _, hlen⟩ := (hconn x y).exists_path_of_dist
    have hcont := pathGraph_isIndContained_of_length_eq_dist p hlen
    have hp3 : 3 ≤ inducedPathOrder G := by
      have hle : G.dist x y + 1 ≤ inducedPathOrder G := by
        simpa [hlen, inducedPathOrder] using le_csSup (inducedPathOrder_bddAbove G) hcont
      omega
    have : (radiusNat G : ℚ) + ell G < (inducedPathOrder G : ℚ) := by
      have hr' : (radiusNat G : ℚ) = 1 := by exact_mod_cast hr
      have hp' : (3 : ℚ) ≤ inducedPathOrder G := by exact_mod_cast hp3
      linarith
    exact le_of_lt this

/-- Lemma 3.2. -/
theorem lemma_3_2 [Fintype V] [DecidableEq V] (hconn : G.Connected) (hC : StrongC4Free G)
    (hr : 2 ≤ radiusNat G) : 4 ≤ inducedPathOrder G := by
  by_contra hp
  have hfree : IsPkFree G 4 :=
    (isPkFree_iff_inducedPathOrder_lt G 4).2 (by omega)
  have hcard : 2 ≤ Fintype.card V := by
    have hne0 : G.radius ≠ 0 := by
      intro h0
      have : radiusNat G = 0 := by simp [radiusNat, h0]
      omega
    have hnot : ¬ Subsingleton V := fun hs =>
      hne0 ((G.radius_eq_zero_iff).2 ⟨hconn.nonempty, hs⟩)
    rw [subsingleton_iff] at hnot
    push Not at hnot
    obtain ⟨a, b, hne⟩ := hnot
    haveI : Nontrivial V := ⟨⟨a, b, hne⟩⟩
    exact Nat.succ_le_of_lt Fintype.one_lt_card
  obtain ⟨w, hw⟩ := lemma_2_7 hconn hC hfree hcard
  have hec : G.eccent w ≤ 1 :=
    (eccent_le_one_iff w).2 fun v hv => (hw v).resolve_left hv.symm
  have hrad : radiusNat G ≤ 1 :=
    ENat.toNat_le_of_le_natCast (G.radius_le_eccent.trans hec)
  omega

/-- Lemma 3.3. `h` is the number of vertices with `λ ≥ 3`. -/
theorem lemma_3_3 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 5) :
    neighbourhoodIndependenceSum G ≤
        2 * Fintype.card V -
          (Finset.univ.filter fun v => 3 ≤ lambda G v).card ∧
      neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V := by
  -- missing: the count of vertices with `λ ≥ 3` in a `P₅`-free neighbourhood
  sorry

/-- Lemma 3.4. Dominating induced `C₆`. -/
theorem lemma_3_4 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i)) :
    let W := {v | ∀ i, c i ≠ v}
    (∀ w ∈ W, ∃ i : Fin 6, ∀ j, G.Adj w (c j) ↔ j = i ∨ j = i + 3) ∧
      (W.Pairwise fun w w' =>
        ∀ i, ¬ (G.Adj w (c i) ∧ G.Adj w' (c i))) ∧
      W.Pairwise (¬ G.Adj · ·) ∧
      Nat.card W ≤ 3 ∧
      neighbourhoodIndependenceSum G = 12 + 4 * Nat.card W ∧
      neighbourhoodIndependenceSum G < 3 * Fintype.card V ∧
      (W.Nonempty → radiusNat G ≤ 2) := by
  -- missing: the trace of each vertex off a dominating induced `C₆`
  sorry

/-- Lemma 3.5. -/
theorem lemma_3_5 [Fintype V] [DecidableEq V] (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 6) :
    (∃ v, G.eccent v ≤ 2) ∨ Nonempty (G ≃g cycleGraph 6) := by
  -- missing: Lemma 3.4 when the Camby–Schaudt set is an induced `C₆`
  sorry

/-- Extremal graphs of Theorem 3.6, including the orders `2 ≤ n ≤ 6`. -/
def IsP6Extremal {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  match Fintype.card V with
  | 2 => Nonempty (G ≃g k2Graph)
  | 3 => Nonempty (G ≃g p3Graph)
  | 4 => Nonempty (G ≃g p4Graph) ∨ Nonempty (G ≃g clawGraph)
  | 5 => Nonempty (G ≃g cycleGraph 5)
  | 6 => Nonempty (G ≃g cycleGraph 6) ∨ Nonempty (G ≃g c5PlusLeaf)
  | 7 => Nonempty (G ≃g gammaGraph 0)
  | 8 => Nonempty (G ≃g h8Graph)
  | 9 => Nonempty (G ≃g petersenMinus)
  | 10 => Nonempty (G ≃g petersenGraph)
  | n => if 11 ≤ n then Nonempty (G ≃g gammaGraph (n - 7)) else False

/-- Theorem 3.6. `M(n)` is `extremalDensity`. Equality `S = 3n` holds only for Petersen. -/
theorem theorem_3_6 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (hn : 2 ≤ Fintype.card V) :
    ell G ≤ extremalDensity (Fintype.card V) ∧
      (ell G = extremalDensity (Fintype.card V) ↔ IsP6Extremal G) ∧
      neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V ∧
      (neighbourhoodIndependenceSum G = 3 * Fintype.card V ↔
        Nonempty (G ≃g petersenGraph)) := by
  -- missing: the extremal case analysis for `P₆`-free strong `C₄`-free graphs
  sorry

/-! ### Section 4 -/

/-- Lemma 4.1. An induced dominating `C₈` in radius at least 4 is the whole graph. -/
theorem lemma_4_1 [Fintype V] [DecidableEq V] (hconn : G.Connected) (hC : StrongC4Free G)
    (c : cycleGraph 8 ↪g G) (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i))
    (hr : 4 ≤ radiusNat G) : Nonempty (G ≃g cycleGraph 8) := by
  -- missing: an off-cycle vertex of a dominating induced `C₈` drops the radius below 4
  sorry

/-- Theorem 4.2. -/
theorem theorem_4_2 [Fintype V] [DecidableEq V] :
    (G.Connected ∧ StrongC4Free G ∧ radiusNat G = 4 ∧ inducedPathOrder G = 7) ↔
      Nonempty (G ≃g cycleGraph 8) ∨ IsRadiusFourExtension G := by
  -- missing: Lemma 4.1 and the classification of radius-4 extensions
  sorry

/-- Lemma 4.3. Off-cycle vertices of an induced path of order at least 3 are endpoints. -/
theorem lemma_4_3 {n : ℕ} (E : RadiusFourExtension G) (f : pathGraph n ↪g G) (hn : 3 ≤ n) :
    ∀ i : Fin n, (∀ j, E.cycleEmb j ≠ f i) → i.val = 0 ∨ i.val = n - 1 := by
  -- missing: an internal off-cycle vertex of an induced path creates a shorter route
  sorry

/-- Corollary 4.4, the mass formula. `C₈` is the case `b = m = 0` outside the extension. -/
theorem corollary_4_4_mass [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hr : radiusNat G = 4)
    (hp : inducedPathOrder G = 7) :
    (Nonempty (G ≃g cycleGraph 8) ∧
        neighbourhoodIndependenceSum G = 2 * Fintype.card V) ∨
      (∃ E : RadiusFourExtension G,
        neighbourhoodIndependenceSum G =
          2 * Fintype.card V - addedCount E - matchingCount E) := by
  -- missing: Theorem 4.2
  sorry

/-- Corollary 4.4, the inequalities. They follow from the mass formula. -/
theorem corollary_4_4 [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hr : radiusNat G = 4)
    (hp : inducedPathOrder G = 7) :
    neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V ∧ ell G ≤ 2 := by
  have hmass := corollary_4_4_mass hconn hC hr hp
  have hS : neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V := by
    rcases hmass with ⟨_, hS⟩ | ⟨_, hS⟩
    · exact le_of_eq hS
    · rw [hS]
      exact (Nat.sub_le _ _).trans (Nat.sub_le _ _)
  refine ⟨hS, ?_⟩
  have : Nonempty V := hconn.nonempty
  have hn : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
  rw [ell, div_le_iff₀ hn]
  have hcast : (neighbourhoodIndependenceSum G : ℚ) ≤ 2 * (Fintype.card V : ℚ) := by
    exact_mod_cast hS
  simpa [mul_comm] using hcast

/-- Corollary 4.5. `S = 2n` for `C₈`, and for a 6-cycle with at least one leaf at each vertex. -/
theorem corollary_4_5 [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hr : radiusNat G = 4)
    (hp : inducedPathOrder G = 7) :
    neighbourhoodIndependenceSum G = 2 * Fintype.card V ↔
      Nonempty (G ≃g cycleGraph 8) ∨
        ∃ E : RadiusFourExtension G, addedCount E = 0 ∧ matchingCount E = 0 ∧
          ∀ i, ∃ v ∈ E.attach i, ∀ w ∈ E.attach i, ¬ G.Adj v w := by
  -- missing: the mass formula in Corollary 4.4
  sorry

/-! ### Section 5 -/

/-- Lemma 5.2, the edge table for `𝔉`. Not an external axiom. -/
theorem lemma_5_2 [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : InChenXuFamily G) :
    (Nonempty (G ≃g petersenGraph) ∧ 2 * edgeCount G = 3 * Fintype.card V) ∨
      (¬ Nonempty (G ≃g petersenGraph) ∧
        2 * edgeCount G ≤ 3 * Fintype.card V - 3) := by
  -- missing: the edge count of each member of the Chen–Xu family
  sorry

/-- Lemma 5.3. No induced `P₄` starts at `s`, and `m = e(G[N(s)])`. -/
theorem lemma_5_3 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) {s : V}
    (hp : ∀ n (hn : 4 ≤ n) (f : pathGraph n ↪g G),
      f ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 4) hn⟩ ≠ s) :
    neighbourhoodIndependenceSum G ≤
      2 * (Fintype.card V - 1) - edgeCount (G.induce (G.neighborSet s)) := by
  -- missing: every other vertex lies on an induced path that starts at `s`
  sorry

/-- Lemma 5.4. Tree stripping down to a core `K₁`, `K₂`, or a member of `𝔉`. -/
theorem lemma_5_4 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (htri : G.CliqueFree 3) (hC : StrongC4Free G) (hp : IsPkFree G 7) :
    ∃ (Q : Set V) (_ : DecidablePred (· ∈ Q)),
      (G.induce Q).Connected ∧ (G.induce Q).CliqueFree 3 ∧ StrongC4Free (G.induce Q) ∧
        IsPkFree (G.induce Q) 7 ∧ ¬ HasCliqueCutset (G.induce Q) ∧
        (Nonempty ((G.induce Q) ≃g (completeGraph (Fin 1))) ∨
          Nonempty ((G.induce Q) ≃g k2Graph) ∨ InChenXuFamily (G.induce Q)) ∧
        edgeCount G = edgeCount (G.induce Q) + (Fintype.card V - Nat.card Q) ∧
        3 * Fintype.card V - 2 * edgeCount G =
          (3 * Nat.card Q - 2 * edgeCount (G.induce Q)) +
            (Fintype.card V - Nat.card Q) := by
  -- missing: deleting degree-1 vertices down to a `K₁`, `K₂`, or Chen–Xu core
  sorry

/-- Theorem 5.5. -/
theorem theorem_5_5 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (htri : G.CliqueFree 3) (hC : StrongC4Free G) (hp : IsPkFree G 7) :
    2 * edgeCount G ≤ 3 * Fintype.card V ∧
      (2 * edgeCount G = 3 * Fintype.card V ↔ Nonempty (G ≃g petersenGraph)) ∧
      (inducedPathOrder G ≤ 6 → GenK 3) ∧
      (G.IsBipartite → inducedPathOrder G ≤ 6 →
        neighbourhoodIndependenceSum G + 1 ≤ 3 * Fintype.card V) := by
  -- missing: Lemmas 5.2 and 5.4; `GEN₃` and the bipartite clause stay open
  sorry

/-- Canonical leaf placements and the extra `F₂` / `F'₀` models of Theorem 5.6. -/
def IsFnExtremal {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
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
  else
    False

/-- Distinct canonical Petersen leaf-pairs, and `F₂` not isomorphic to a leaf extension
of Petersen. The remaining pairwise checks among `F'₀`, `F₂`-leaves and Petersen leaves
are part of this `sorry`. -/
theorem theorem_5_6_noniso :
    (∀ a b a' b' : ℕ,
      a + b = a' + b' → (b = 0 ∨ 1 ≤ a ∧ a ≤ b) → (b' = 0 ∨ 1 ≤ a' ∧ a' ≤ b') →
        Nonempty (petersenWithLeaves a b ≃g petersenWithLeaves a' b') → a = a' ∧ b = b') ∧
      (∀ t, 0 < t → ∀ a b, ¬ Nonempty (f2Graph t ≃g petersenWithLeaves a b)) ∧
      (∀ t, 0 < t → ¬ Nonempty (f0pGraph t ≃g f2HubLeaf t)) ∧
      (∀ t, 0 < t → ¬ Nonempty (f0pGraph t ≃g f2MidLeaf t)) ∧
      (∀ t, 0 < t → ¬ Nonempty (f2HubLeaf t ≃g f2MidLeaf t)) := by
  -- missing: isomorphism invariants separating the leaf placements
  sorry

/-- Theorem 5.6. `f(n)` is `edgeExtremal`. -/
theorem theorem_5_6 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (htri : G.CliqueFree 3) (hC : StrongC4Free G) (hp : IsPkFree G 7)
    (hn : 10 ≤ Fintype.card V) :
    2 * edgeCount G ≤ edgeExtremal (Fintype.card V) ∧
      (2 * edgeCount G = edgeExtremal (Fintype.card V) ↔ IsFnExtremal G) := by
  -- missing: Theorem 5.5 and the extremal graphs of order at least 10
  sorry

/-- Theorem 5.7. At most one triangle. -/
theorem theorem_5_7 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 7) (htri : triangleCount G ≤ 1) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V := by
  -- missing: at most one triangle, then the deletion-loss bound
  sorry

/-- Lemma 5.8(1). A cross edge between two triangles that share a vertex spans a `C₄`.
`a ≠ d` keeps `a, c, d, u` distinct; without it the configuration can be a single triangle. -/
theorem lemma_5_8_share (hC : StrongC4Free G) {u a b c d : V}
    (hab : G.Adj u a) (_hbb : G.Adj a b) (_hbu : G.Adj b u) (huc : G.Adj u c) (hcd : G.Adj c d)
    (hdu : G.Adj d u) (_hne : a ≠ c) (had : a ≠ d) (_hb : b ≠ d) :
    ¬ G.Adj a c := by
  intro hac
  exact hC (fourCycle_isContained hac hcd hdu hab had huc.ne.symm)

/-- Lemma 5.8(2). Two disjoint triangles span at most one cross edge. -/
theorem lemma_5_8_disjoint (hC : StrongC4Free G) [DecidableRel G.Adj] {a b c x y z : V}
    (htri1 : G.Adj a b ∧ G.Adj b c ∧ G.Adj c a)
    (htri2 : G.Adj x y ∧ G.Adj y z ∧ G.Adj z x)
    (hdisj : ({a, b, c} : Set V) ∩ {x, y, z} = ∅) :
    (if G.Adj a x then 1 else 0) + (if G.Adj a y then 1 else 0) + (if G.Adj a z then 1 else 0) +
        (if G.Adj b x then 1 else 0) + (if G.Adj b y then 1 else 0) +
        (if G.Adj b z then 1 else 0) +
        (if G.Adj c x then 1 else 0) + (if G.Adj c y then 1 else 0) +
        (if G.Adj c z then 1 else 0) ≤
      1 := by
  let t1 : Fin 3 → V
    | 0 => a
    | 1 => b
    | 2 => c
  let t2 : Fin 3 → V
    | 0 => x
    | 1 => y
    | 2 => z
  have hT1 : ∀ i j : Fin 3, i ≠ j → G.Adj (t1 i) (t1 j) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [t1] at h ⊢
    · exact htri1.1
    · exact htri1.2.2.symm
    · exact htri1.1.symm
    · exact htri1.2.1
    · exact htri1.2.2
    · exact htri1.2.1.symm
  have hT2 : ∀ i j : Fin 3, i ≠ j → G.Adj (t2 i) (t2 j) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp [t2] at h ⊢
    · exact htri2.1
    · exact htri2.2.2.symm
    · exact htri2.1.symm
    · exact htri2.2.1
    · exact htri2.2.2
    · exact htri2.2.1.symm
  have ht1inj : Function.Injective t1 := by
    intro i j hij
    by_contra hne
    exact (hT1 i j hne).ne hij
  have ht2inj : Function.Injective t2 := by
    intro i j hij
    by_contra hne
    exact (hT2 i j hne).ne hij
  have ht1mem : ∀ i, t1 i ∈ ({a, b, c} : Set V) := by
    intro i
    fin_cases i <;> simp [t1]
  have ht2mem : ∀ j, t2 j ∈ ({x, y, z} : Set V) := by
    intro j
    fin_cases j <;> simp [t2]
  have hsep : ∀ i j, t1 i ≠ t2 j := by
    intro i j h
    have : t1 i ∈ ({a, b, c} : Set V) ∩ {x, y, z} := ⟨ht1mem i, h ▸ ht2mem j⟩
    simp [hdisj] at this
  let cross : Finset (Fin 3 × Fin 3) := univ.filter fun p => G.Adj (t1 p.1) (t2 p.2)
  have hle : cross.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro p hp q hq
    obtain ⟨i, j⟩ := p
    obtain ⟨i', j'⟩ := q
    by_contra hne
    have hp' : G.Adj (t1 i) (t2 j) := by simpa [cross] using hp
    have hq' : G.Adj (t1 i') (t2 j') := by simpa [cross] using hq
    by_cases hi : i = i'
    · have hj : j ≠ j' := by
        intro hj
        apply hne
        simp [hi, hj]
      let k : Fin 3 := ⟨3 - j.val - j'.val, by
        have hjv : j.val < 3 := j.isLt
        have hj' : j'.val < 3 := j'.isLt
        have hsum : j.val + j'.val ≤ 3 := by
          fin_cases j <;> fin_cases j' <;> simp at hj ⊢
        omega⟩
      have hk1 : k ≠ j := by
        intro hk
        fin_cases j <;> fin_cases j' <;> simp [k] at hk hj
      have hk2 : k ≠ j' := by
        intro hk
        fin_cases j <;> fin_cases j' <;> simp [k] at hk hj
      exact hC (fourCycle_isContained
        hp'
        (hT2 j k hk1.symm)
        (hT2 k j' hk2)
        (hi ▸ hq').symm
        (hsep i k)
        (ht2inj.ne hj))
    · by_cases hj : j = j'
      · let k : Fin 3 := ⟨3 - i.val - i'.val, by
          have hiv : i.val < 3 := i.isLt
          have hi' : i'.val < 3 := i'.isLt
          have hsum : i.val + i'.val ≤ 3 := by
            fin_cases i <;> fin_cases i' <;> simp at hi ⊢
          omega⟩
        have hk1 : k ≠ i := by
          intro hk
          fin_cases i <;> fin_cases i' <;> simp [k] at hk hi
        have hk2 : k ≠ i' := by
          intro hk
          fin_cases i <;> fin_cases i' <;> simp [k] at hk hi
        exact hC (fourCycle_isContained
          hp'.symm
          (hT1 i k hk1.symm)
          (hT1 k i' hk2)
          (hj ▸ hq')
          (hsep k j).symm
          (ht1inj.ne hi))
      · exact hC (fourCycle_isContained
          hp'
          (hT2 j j' hj)
          hq'.symm
          (hT1 i' i (Ne.symm hi))
          (hsep i j')
          (hsep i' j).symm)
  have hrows :
      (∑ i : Fin 3, ∑ j : Fin 3, if G.Adj (t1 i) (t2 j) then 1 else 0) =
        (if G.Adj a x then 1 else 0) + (if G.Adj a y then 1 else 0) +
            (if G.Adj a z then 1 else 0) +
          ((if G.Adj b x then 1 else 0) + (if G.Adj b y then 1 else 0) +
            (if G.Adj b z then 1 else 0)) +
          ((if G.Adj c x then 1 else 0) + (if G.Adj c y then 1 else 0) +
            (if G.Adj c z then 1 else 0)) := by
    simp only [Fin.sum_univ_three, t1, t2]
  have hprod :
      (∑ p : Fin 3 × Fin 3, if G.Adj (t1 p.1) (t2 p.2) then 1 else 0) =
        ∑ i : Fin 3, ∑ j : Fin 3, if G.Adj (t1 i) (t2 j) then 1 else 0 :=
    Fintype.sum_prod_type' fun i j => if G.Adj (t1 i) (t2 j) then 1 else 0
  have hcard :
      (∑ p : Fin 3 × Fin 3, if G.Adj (t1 p.1) (t2 p.2) then 1 else 0) = cross.card := by
    rw [Finset.sum_boole]
    simp [cross]
  have hassoc :
      (if G.Adj a x then 1 else 0) + (if G.Adj a y then 1 else 0) + (if G.Adj a z then 1 else 0) +
          (if G.Adj b x then 1 else 0) + (if G.Adj b y then 1 else 0) +
          (if G.Adj b z then 1 else 0) +
          (if G.Adj c x then 1 else 0) + (if G.Adj c y then 1 else 0) +
          (if G.Adj c z then 1 else 0) =
        (if G.Adj a x then 1 else 0) + (if G.Adj a y then 1 else 0) + (if G.Adj a z then 1 else 0) +
          ((if G.Adj b x then 1 else 0) + (if G.Adj b y then 1 else 0) +
            (if G.Adj b z then 1 else 0)) +
          ((if G.Adj c x then 1 else 0) + (if G.Adj c y then 1 else 0) +
            (if G.Adj c z then 1 else 0)) := by ac_rfl
  rw [hassoc, ← hrows, ← hprod, hcard]
  exact hle

/-- Not Lemma 5.8(4). The hypotheses omit both triangles and a shortest path between their
vertex sets. On `K₂`, take `d = 0`, `u = v` and `z` the neighbour of `u`: the hypotheses hold
and the induced-path order is 2. -/
theorem lemma_5_8_path (hC : StrongC4Free G) {u v x z : V} {d : ℕ}
    (hdist : G.dist u v = d) (hx : x ≠ u ∧ G.Adj x u) (hz : z ≠ v ∧ G.Adj v z)
    (hmin : ∀ u' v', G.Adj x u' → G.Adj u' x → G.Adj z v' → G.Adj v' z → d ≤ G.dist u' v') :
    d + 3 ≤ inducedPathOrder G := by
  -- missing: the two triangles and a geodesic between their vertex sets
  sorry

/-- Lemma 5.9. A closed replay of the four seeds does not prove this lemma: the
embedding of those seeds and the comparison of mask-loss with `L(v)` stay open. -/
theorem lemma_5_9 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 7) (htri : 2 ≤ triangleCount G) :
    ∃ v, deletionLoss G v ≤ 3 := by
  -- missing: the four seeds embed, and every searched graph has a vertex of deletion loss at most 3
  sorry

/-- The induced-path order of the Petersen graph. -/
private def petersenPath5 : Fin 5 → PetersenVertex
  | ⟨0, _⟩ => ⟨{0, 1}, by decide⟩
  | ⟨1, _⟩ => ⟨{2, 3}, by decide⟩
  | ⟨2, _⟩ => ⟨{0, 4}, by decide⟩
  | ⟨3, _⟩ => ⟨{1, 2}, by decide⟩
  | ⟨4, _⟩ => ⟨{0, 3}, by decide⟩

/-- The ten vertices of the Petersen graph, indexed by `Fin 10`. -/
private def pv (i : Fin 10) : PetersenVertex :=
  if i.val = 0 then ⟨{0, 1}, by decide⟩
  else if i.val = 1 then ⟨{0, 2}, by decide⟩
  else if i.val = 2 then ⟨{0, 3}, by decide⟩
  else if i.val = 3 then ⟨{0, 4}, by decide⟩
  else if i.val = 4 then ⟨{1, 2}, by decide⟩
  else if i.val = 5 then ⟨{1, 3}, by decide⟩
  else if i.val = 6 then ⟨{1, 4}, by decide⟩
  else if i.val = 7 then ⟨{2, 3}, by decide⟩
  else if i.val = 8 then ⟨{2, 4}, by decide⟩
  else ⟨{3, 4}, by decide⟩

private lemma pv_surj (v : PetersenVertex) : ∃ i : Fin 10, pv i = v := by
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp v.2
  fin_cases a <;> fin_cases b <;> try exact absurd hab (by decide)
  all_goals
    first
      | (refine ⟨⟨0, by decide⟩, ?_⟩; apply Subtype.ext; simp only [pv]; rw [hs]; decide)
      | (refine ⟨⟨1, by decide⟩, ?_⟩; apply Subtype.ext; simp only [pv]; rw [hs]; decide)
      | (refine ⟨⟨2, by decide⟩, ?_⟩; apply Subtype.ext; simp only [pv]; rw [hs]; decide)
      | (refine ⟨⟨3, by decide⟩, ?_⟩; apply Subtype.ext; simp only [pv]; rw [hs]; decide)
      | (refine ⟨⟨4, by decide⟩, ?_⟩; apply Subtype.ext; simp only [pv]; rw [hs]; decide)
      | (refine ⟨⟨5, by decide⟩, ?_⟩; apply Subtype.ext; simp only [pv]; rw [hs]; decide)
      | (refine ⟨⟨6, by decide⟩, ?_⟩; apply Subtype.ext; simp only [pv]; rw [hs]; decide)
      | (refine ⟨⟨7, by decide⟩, ?_⟩; apply Subtype.ext; simp only [pv]; rw [hs]; decide)
      | (refine ⟨⟨8, by decide⟩, ?_⟩; apply Subtype.ext; simp only [pv]; rw [hs]; decide)
      | (refine ⟨⟨9, by decide⟩, ?_⟩; apply Subtype.ext; simp only [pv]; rw [hs]; decide)

/-- Ordered pairs for the ten vertices, so adjacency is a `Bool` comparison. -/
private def pairOf (i : Fin 10) : Fin 5 × Fin 5 :=
  if i.val = 0 then (0, 1)
  else if i.val = 1 then (0, 2)
  else if i.val = 2 then (0, 3)
  else if i.val = 3 then (0, 4)
  else if i.val = 4 then (1, 2)
  else if i.val = 5 then (1, 3)
  else if i.val = 6 then (1, 4)
  else if i.val = 7 then (2, 3)
  else if i.val = 8 then (2, 4)
  else (3, 4)

private def disjPair (p q : Fin 5 × Fin 5) : Bool :=
  !decide (p.1 = q.1) && !decide (p.1 = q.2) && !decide (p.2 = q.1) && !decide (p.2 = q.2)

private lemma disjPair_iff (i j : Fin 10) :
    disjPair (pairOf i) (pairOf j) = true ↔ Disjoint (pv i).1 (pv j).1 := by
  fin_cases i <;> fin_cases j <;>
    simp [disjPair, pairOf, pv, Finset.disjoint_left]

private def ix6 (a b c d e f : Fin 10) (i : Fin 6) : Fin 10 :=
  if i.val = 0 then a
  else if i.val = 1 then b
  else if i.val = 2 then c
  else if i.val = 3 then d
  else if i.val = 4 then e
  else f

private def pathAdj6 (i j : Fin 6) : Bool :=
  decide (i.val + 1 = j.val) || decide (j.val + 1 = i.val)

private lemma pathAdj6_iff (i j : Fin 6) :
    pathAdj6 i j = true ↔ (pathGraph 6).Adj i j := by
  simp [pathAdj6, pathGraph_adj, Bool.or_eq_true]

private lemma bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

private def p6ok (a b c d e f : Fin 10) : Bool :=
  (List.finRange 6).all fun i =>
    (List.finRange 6).all fun j =>
      ((decide (i = j) || decide (ix6 a b c d e f i ≠ ix6 a b c d e f j)) &&
        (disjPair (pairOf (ix6 a b c d e f i)) (pairOf (ix6 a b c d e f j)) ==
          pathAdj6 i j))

private def existsP6 : Bool :=
  (List.finRange 10).any fun a =>
    (List.finRange 10).any fun b =>
      (List.finRange 10).any fun c =>
        (List.finRange 10).any fun d =>
          (List.finRange 10).any fun e =>
            (List.finRange 10).any fun f => p6ok a b c d e f

private lemma ix6_eq {a b c d e f6 : Fin 10} {g : Fin 6 → PetersenVertex}
    (h0 : pv a = g 0) (h1 : pv b = g 1) (h2 : pv c = g 2)
    (h3 : pv d = g 3) (h4 : pv e = g 4) (h5 : pv f6 = g 5)
    (i : Fin 6) : pv (ix6 a b c d e f6 i) = g i := by
  fin_cases i <;> simp [ix6, h0, h1, h2, h3, h4, h5]

private lemma p6ok_embed (f : pathGraph 6 ↪g petersenGraph) {a b c d e f6 : Fin 10}
    (ha : pv a = f 0) (hb : pv b = f 1) (hc : pv c = f 2)
    (hd : pv d = f 3) (he : pv e = f 4) (hf : pv f6 = f 5) :
    p6ok a b c d e f6 = true := by
  rw [p6ok, List.all_eq_true]
  intro i _
  rw [List.all_eq_true]
  intro j _
  rw [Bool.and_eq_true, beq_iff_eq]
  constructor
  · by_cases hij : i = j
    · simp [hij]
    · have hne : ix6 a b c d e f6 i ≠ ix6 a b c d e f6 j := by
        intro hidx
        apply f.injective.ne hij
        rw [← ix6_eq ha hb hc hd he hf i, ← ix6_eq ha hb hc hd he hf j, hidx]
      simp [decide_eq_false hij, hne]
  · apply bool_eq_of_iff
    have hdis : disjPair (pairOf (ix6 a b c d e f6 i)) (pairOf (ix6 a b c d e f6 j)) = true ↔
        Disjoint (f i).1 (f j).1 := by
      rw [← ix6_eq ha hb hc hd he hf i, ← ix6_eq ha hb hc hd he hf j]
      exact disjPair_iff _ _
    have hpath : pathAdj6 i j = true ↔ (pathGraph 6).Adj i j := pathAdj6_iff i j
    have hadj : Disjoint (f i).1 (f j).1 ↔ (pathGraph 6).Adj i j := by
      simpa [petersenGraph] using f.map_rel_iff
    exact hdis.trans (hadj.trans hpath.symm)

private lemma existsP6_of_embed (f : pathGraph 6 ↪g petersenGraph) : existsP6 = true := by
  obtain ⟨a, ha⟩ := pv_surj (f 0)
  obtain ⟨b, hb⟩ := pv_surj (f 1)
  obtain ⟨c, hc⟩ := pv_surj (f 2)
  obtain ⟨d, hd⟩ := pv_surj (f 3)
  obtain ⟨e, he⟩ := pv_surj (f 4)
  obtain ⟨g, hg⟩ := pv_surj (f 5)
  have hok := p6ok_embed f ha hb hc hd he hg
  rw [existsP6, List.any_eq_true]
  refine ⟨a, List.mem_finRange a, ?_⟩
  rw [List.any_eq_true]
  refine ⟨b, List.mem_finRange b, ?_⟩
  rw [List.any_eq_true]
  refine ⟨c, List.mem_finRange c, ?_⟩
  rw [List.any_eq_true]
  refine ⟨d, List.mem_finRange d, ?_⟩
  rw [List.any_eq_true]
  refine ⟨e, List.mem_finRange e, ?_⟩
  rw [List.any_eq_true]
  exact ⟨g, List.mem_finRange g, hok⟩

private lemma existsP6_false : existsP6 = false := by
  native_decide

theorem petersen_inducedPathOrder : inducedPathOrder petersenGraph = 5 := by
  have h5 : pathGraph 5 ⊴ petersenGraph := by
    refine ⟨{
      toFun := petersenPath5
      inj' := by
        intro i j h
        have hval := congrArg Subtype.val h
        fin_cases i <;> fin_cases j <;> simp [petersenPath5] at hval ⊢ <;>
          exact absurd hval (by decide)
      map_rel_iff' := by
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp [pathGraph_adj, petersenGraph, Finset.disjoint_left] <;>
          try decide
    }⟩
  have h6 : ¬ pathGraph 6 ⊴ petersenGraph := by
    intro ⟨f⟩
    have := existsP6_of_embed f
    simp [existsP6_false] at this
  have hge : 5 ≤ inducedPathOrder petersenGraph :=
    le_csSup (inducedPathOrder_bddAbove petersenGraph) h5
  have hlt : inducedPathOrder petersenGraph < 6 :=
    (isPkFree_iff_inducedPathOrder_lt petersenGraph 6).mp h6
  omega

/-- Theorem 5.10. -/
theorem theorem_5_10 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 7) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V ∧
      (neighbourhoodIndependenceSum G = 3 * Fintype.card V ↔
        Nonempty (G ≃g petersenGraph)) := by
  -- missing: Theorems 5.6 and 5.7
  sorry

/-- Theorem 5.11, REAL-133 for `ℓ ≤ 4`. -/
theorem theorem_5_11 [Fintype V] [DecidableEq V] (hell : ell G ≤ 4)
    (hn : 2 ≤ Fintype.card V) (hconn : G.Connected) :
    (inducedPathOrder G : ℚ) ≥ (radiusNat G : ℚ) + ell G ^ cC4 G := by
  -- missing: the case split on `c_{C₄}` using Theorems 3.6, 4.2 and 5.10
  sorry

end InducedPaths
