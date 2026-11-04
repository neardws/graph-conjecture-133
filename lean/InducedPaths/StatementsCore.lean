/-
Statements of the preprint, in dependency order. Proofs are `sorry` except where noted.
Paper numbers refer to `paper/main.tex` at `c6d3eb76`.
-/
module

public import InducedPaths.Basic
public import InducedPaths.Certificate
public import InducedPaths.C6Mass
public import InducedPaths.MaskGraph
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic.IntervalCases

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

/-- The executable certificate loss is actual deletion loss in its decoded
strongly `C₄`-free simple graph. -/
theorem certificate_loss_eq_deletionLoss (g : List ℕ) (h : Certificate.WellFormed g)
    (hC : StrongC4Free (Certificate.toSimpleGraph g h)) (v : Fin g.length) :
    Certificate.loss g v.val = deletionLoss (Certificate.toSimpleGraph g h) v := by
  rw [Certificate.loss_eq_degree_sub_trianglesAt, lemma_2_2 hC]

/-- Deletion loss is final in an induced subgraph containing every neighbour
of the designated vertex. This is the locality step in the two-triangle search. -/
theorem deletionLoss_induce_eq [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hC : StrongC4Free G) {s : Set V} [DecidablePred (· ∈ s)] {v : V}
    (hv : v ∈ s) (hN : G.neighborSet v ⊆ s) :
    deletionLoss (G.induce s) ⟨v, hv⟩ = deletionLoss G v := by
  classical
  let e : (G.induce s).neighborSet ⟨v, hv⟩ ≃ G.neighborSet v :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      invFun := fun x => ⟨⟨x.val, hN x.property⟩, x.property⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => Subtype.ext rfl }
  have hd : (G.induce s).degree ⟨v, hv⟩ = G.degree v := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    exact Fintype.card_congr e
  have hCs := strongC4Free_induce (s := s) hC
  have hl := lambda_induce_eq hv hN
  have ht : trianglesAt (G.induce s) ⟨v, hv⟩ = trianglesAt G v := by
    have ha := lambda_add_trianglesAt hCs ⟨v, hv⟩
    have hb := lambda_add_trianglesAt hC v
    omega
  rw [lemma_2_2 hCs, lemma_2_2 hC, hd, ht]

/-- A deficient vertex in an induced subgraph must have a new neighbour if
its ambient deletion loss is at least four. -/
theorem exists_neighbor_outside_of_loss [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hC : StrongC4Free G) {s : Set V} [DecidablePred (· ∈ s)] {v : V}
    (hv : v ∈ s) (hsmall : deletionLoss (G.induce s) ⟨v, hv⟩ < 4)
    (hlarge : 4 ≤ deletionLoss G v) : ∃ w, G.Adj v w ∧ w ∉ s := by
  classical
  by_contra h
  have hN : G.neighborSet v ⊆ s := by
    intro w hw
    by_contra hws
    exact h ⟨w, hw, hws⟩
  rw [deletionLoss_induce_eq hC hv hN] at hsmall
  omega

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

set_option maxHeartbeats 4000000 in
/-- Lemma 2.10. A triangle-free strong `C₄`-free `P₇`-free graph with no cut vertex
has no clique cutset: a 2-clique cutset would leave two components, and the three
vertices of a shortest path through each component, meeting at the cut edge, form
an induced `P₇`. -/
theorem lemma_2_10 [Fintype V] [DecidableEq V] (hconn : G.Connected)
    (htri : G.CliqueFree 3) (hC : StrongC4Free G) (hp : IsPkFree G 7)
    (hcut : ∀ v, ¬ IsCutVertex G v) : ¬ HasCliqueCutset G := by
  classical
  have _usedConn : Nonempty V := hconn.nonempty
  intro hHas
  obtain ⟨s, hscl, hsne, -, hnot⟩ := hHas
  have hcard : s.ncard = 2 := by
    have hpos : 0 < s.ncard := (Set.ncard_pos).mpr hsne
    have hle : s.ncard ≤ 2 := by
      by_contra hgt
      have h3 : 2 < s.ncard := by omega
      obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff).1 h3
      exact htri {a, b, c} (is3Clique_triple_iff.mpr
        ⟨hscl ha hb hab, hscl ha hc hac, hscl hb hc hbc⟩)
    have hne1 : s.ncard ≠ 1 := by
      intro h1
      obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp h1
      have hcutw : IsCutVertex G w := by
        rw [IsCutVertex]
        have hscomp : sᶜ = {x | x ≠ w} := by
          ext x
          simp [hw, Set.mem_compl_iff, Set.mem_singleton_iff]
        rw [hscomp] at hnot
        exact hnot
      exact hcut w hcutw
    omega
  obtain ⟨u, v, huv, hsuv⟩ := Set.ncard_eq_two.mp hcard
  have huv_adj : G.Adj u v := hscl (by simp [hsuv]) (by simp [hsuv]) huv
  let H := G.induce (sᶜ)
  obtain ⟨x, y, hxy⟩ : ∃ x y : ↥(sᶜ), ¬ H.Reachable x y := by
    rw [Preconnected] at hnot
    push Not at hnot
    exact hnot
  let Cof : ↥(sᶜ) → Set V := fun t => {w | ∃ hw : w ∈ sᶜ, H.Reachable t ⟨w, hw⟩}
  have hCof_uv (t : ↥(sᶜ)) : u ∉ Cof t ∧ v ∉ Cof t := by
    constructor
    · intro ⟨hw, _⟩
      exact hw (by simp [hsuv])
    · intro ⟨hw, _⟩
      exact hw (by simp [hsuv])
  have hsplit {z anchor other : V} (hanchor : anchor ∈ s) (hother : other ∈ s)
      (hane : anchor ≠ other) (hz : z ∈ s) : z = anchor ∨ z = other := by
    have hanc : anchor = u ∨ anchor = v := by
      simpa [hsuv, Set.mem_insert_iff, Set.mem_singleton_iff] using hanchor
    have hoth : other = u ∨ other = v := by
      simpa [hsuv, Set.mem_insert_iff, Set.mem_singleton_iff] using hother
    have hzuv : z = u ∨ z = v := by
      simpa [hsuv, Set.mem_insert_iff, Set.mem_singleton_iff] using hz
    rcases hanc with rfl | rfl <;> rcases hoth with rfl | rfl <;> rcases hzuv with rfl | rfl
    · exact (hane rfl).elim
    · exact (hane rfl).elim
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact (hane rfl).elim
    · exact (hane rfl).elim
  have exists_nbr {anchor other : V} (hanchor : anchor ∈ s) (hother : other ∈ s)
      (hane : anchor ≠ other) (t out : ↥(sᶜ)) (_hsep : ¬ H.Reachable t out) :
      ∃ a : ↥(sᶜ), H.Reachable t a ∧ G.Adj other a.val := by
    have htA : t.val ≠ anchor := fun h => t.2 (h.symm ▸ hanchor)
    have hoA : out.val ≠ anchor := fun h => out.2 (h.symm ▸ hanchor)
    have htO : t.val ≠ other := fun h => t.2 (h.symm ▸ hother)
    have hpre : (G.induce {w | w ≠ anchor}).Preconnected := by
      simpa [IsCutVertex] using hcut anchor
    obtain ⟨q0⟩ := hpre ⟨t.val, htA⟩ ⟨out.val, hoA⟩
    let emb := SimpleGraph.Embedding.induce (G := G) {w | w ≠ anchor}
    let qRaw := q0.map emb.toHom
    have hsq : emb ⟨t.val, htA⟩ = t.val := rfl
    have hoq : emb ⟨out.val, hoA⟩ = out.val := rfl
    let qG : G.Walk t.val out.val := qRaw.copy hsq hoq
    have hqG_ne {z : V} (hz : z ∈ qG.support) : z ≠ anchor := by
      have hz' : z ∈ qRaw.support := by simpa [qG, Walk.support_copy] using hz
      rw [Walk.support_map] at hz'
      obtain ⟨w, -, hw⟩ := List.mem_map.mp hz'
      have hval : emb.toHom w = w.val := by
        simp [emb, SimpleGraph.Embedding.induce, SimpleGraph.Embedding.comap_apply,
          Function.Embedding.subtype_apply]
      rw [← hw, hval]
      exact w.2
    haveI : Decidable (other ∈ qG.support) := Classical.propDecidable _
    by_cases hhit : other ∈ qG.support
    · have hex : ∃ i, qG.getVert i = other ∧ i ≤ qG.length :=
        (Walk.mem_support_iff_exists_getVert).1 hhit
      haveI : DecidablePred (fun i => qG.getVert i = other ∧ i ≤ qG.length) :=
        fun _ => Classical.propDecidable _
      let i0 := Nat.find hex
      have hi0 := Nat.find_spec hex
      have hi0pos : 0 < i0 := by
        by_contra h0
        have hstart : qG.getVert i0 = other := hi0.1
        rw [show i0 = 0 by omega] at hstart
        rw [Walk.getVert_zero] at hstart
        exact htO hstart
      have hbefore {k : ℕ} (hk : k < i0) (hkle : k ≤ qG.length) : qG.getVert k ∈ sᶜ := by
        rw [Set.mem_compl_iff]
        intro hws
        have hwne_a : qG.getVert k ≠ anchor := hqG_ne (qG.getVert_mem_support k)
        have hwne_o : qG.getVert k ≠ other := by
          intro h
          exact (Nat.find_min hex hk ⟨h, hkle⟩).elim
        rcases hsplit hanchor hother hane hws with hza | hzo
        · exact hwne_a hza
        · exact hwne_o hzo
      have htake_len : (qG.take (i0 - 1)).length = i0 - 1 := by
        rw [Walk.take_length, min_eq_left (by omega : i0 - 1 ≤ qG.length)]
      have hprefix_in : ∀ w ∈ (qG.take (i0 - 1)).support, w ∈ sᶜ := by
        intro w hw
        obtain ⟨k, hk, hkle⟩ := (Walk.mem_support_iff_exists_getVert).1 hw
        have hk' : k ≤ i0 - 1 := by simpa [htake_len] using hkle
        have hkw : qG.getVert k = w := by
          rw [Walk.take_getVert] at hk
          simpa [min_eq_right hk'] using hk
        rw [← hkw]
        exact hbefore (by omega) (by omega)
      have hpred_in : qG.getVert (i0 - 1) ∈ sᶜ := hbefore (by omega) (by omega)
      have hadj : G.Adj (qG.getVert (i0 - 1)) other := by
        have hadj' := qG.adj_getVert_succ (show i0 - 1 < qG.length by omega)
        have hidx : (i0 - 1) + 1 = i0 := by omega
        have hadj'' : G.Adj (qG.getVert (i0 - 1)) (qG.getVert i0) := by
          simpa [hidx] using hadj'
        exact hi0.1 ▸ hadj''
      let qH := (qG.take (i0 - 1)).induce (sᶜ) hprefix_in
      have hstart :
          (⟨t.val, hprefix_in _ (qG.take (i0 - 1)).start_mem_support⟩ : ↥(sᶜ)) = t :=
        Subtype.ext rfl
      have hend :
          (⟨qG.getVert (i0 - 1),
              hprefix_in _ (qG.take (i0 - 1)).end_mem_support⟩ : ↥(sᶜ)) =
            ⟨qG.getVert (i0 - 1), hpred_in⟩ :=
        Subtype.ext rfl
      refine ⟨⟨qG.getVert (i0 - 1), hpred_in⟩, ⟨qH.copy hstart hend⟩, hadj.symm⟩
    · have hprefix_in : ∀ w ∈ qG.support, w ∈ sᶜ := by
        intro w hw
        rw [Set.mem_compl_iff]
        intro hws
        have hwne_a : w ≠ anchor := hqG_ne hw
        have hwne_o : w ≠ other := fun hwo => hhit (hwo ▸ hw)
        rcases hsplit hanchor hother hane hws with hza | hzo
        · exact hwne_a hza
        · exact hwne_o hzo
      let qH := qG.induce (sᶜ) hprefix_in
      have hstart : (⟨t.val, hprefix_in _ qG.start_mem_support⟩ : ↥(sᶜ)) = t :=
        Subtype.ext rfl
      have hend : (⟨out.val, hprefix_in _ qG.end_mem_support⟩ : ↥(sᶜ)) = out :=
        Subtype.ext rfl
      exact (_hsep ⟨qH.copy hstart hend⟩).elim
  have through (t out : ↥(sᶜ)) (hsep : ¬ H.Reachable t out) :
      ∃ p : G.Walk u v, 4 ≤ p.length ∧ p.IsPath ∧
        (∀ i, 0 < i → i < p.length → p.getVert i ∈ Cof t) ∧
        ∀ i j, i ≤ p.length → j ≤ p.length → i + 2 ≤ j → ¬ (i = 0 ∧ j = p.length) →
          ¬ G.Adj (p.getVert i) (p.getVert j) := by
    obtain ⟨a, haR, hau⟩ :=
      exists_nbr (show v ∈ s from by simp [hsuv]) (show u ∈ s from by simp [hsuv])
        (Ne.symm huv) t out hsep
    obtain ⟨b, hbR, hbv⟩ :=
      exists_nbr (show u ∈ s from by simp [hsuv]) (show v ∈ s from by simp [hsuv])
        huv t out hsep
    obtain ⟨r⟩ := haR.symm.trans hbR
    let emb := SimpleGraph.Embedding.induce (G := G) (sᶜ)
    let rRaw := r.map emb.toHom
    have hra : emb a = a.val := rfl
    have hrb : emb b = b.val := rfl
    let rG : G.Walk a.val b.val := rRaw.copy hra hrb
    let p0 : G.Walk u v := (rG.cons hau).concat hbv.symm
    have hp0len : p0.length = r.length + 2 := by
      have h : p0.length = r.length + 1 + 1 := by
        simp [p0, rG, rRaw, Walk.length_concat, Walk.length_cons, Walk.length_copy,
          Walk.length_map]
      omega
    let lens : Set ℕ :=
      {n | ∃ p : G.Walk u v, p.length = n ∧ 2 ≤ p.length ∧
        ∀ i, 0 < i → i < p.length → p.getVert i ∈ Cof t}
    have hp0int : ∀ i, 0 < i → i < p0.length → p0.getVert i ∈ Cof t := by
      intro i hi0 hiL
      have hi : i ≤ r.length + 1 := by
        have := hiL
        simp only [hp0len] at this
        omega
      have hp0eq : p0 = (rG.cons hau).append hbv.symm.toWalk := rfl
      have hget : p0.getVert i = (r.getVert (i - 1)).val := by
        have hlen1 : (rG.cons hau).length = r.length + 1 := by
          simp [rG, rRaw, Walk.length_cons, Walk.length_copy, Walk.length_map]
        have hle : i ≤ (rG.cons hau).length := by rw [hlen1]; exact hi
        rw [hp0eq, Walk.getVert_append', ite_eq_left hle]
        rw [Walk.getVert_cons rG hau (by omega : i ≠ 0)]
        rw [Walk.getVert_copy, Walk.getVert_map]
        simp [emb, SimpleGraph.Embedding.induce, SimpleGraph.Embedding.comap_apply,
          Function.Embedding.subtype_apply]
      rw [hget]
      simp only [Cof, Set.mem_ofPred_eq]
      exact ⟨(r.getVert (i - 1)).2,
        haR.trans (⟨r.take (i - 1)⟩ : H.Reachable a (r.getVert (i - 1)))⟩
    have hp0ge : 2 ≤ p0.length := by
      rw [hp0len]
      omega
    have hne : lens.Nonempty := by
      refine ⟨p0.length, ?_⟩
      simp only [lens, Set.mem_ofPred_eq]
      exact ⟨p0, rfl, hp0ge, hp0int⟩
    have hmem := Nat.sInf_mem hne
    simp only [lens, Set.mem_ofPred_eq] at hmem
    obtain ⟨p, hlen, hpge, hint⟩ := hmem
    have hshort (q : G.Walk u v) (hqint : ∀ i, 0 < i → i < q.length → q.getVert i ∈ Cof t)
        (hqge : 2 ≤ q.length) : p.length ≤ q.length := by
      have hqmem : q.length ∈ lens := by
        simp only [lens, Set.mem_ofPred_eq]
        exact ⟨q, rfl, hqge, hqint⟩
      calc
        p.length = sInf lens := hlen
        _ ≤ q.length := Nat.sInf_le hqmem
    have hfalse : ∀ a b : ℕ, a < b → b ≤ p.length → p.getVert a = p.getVert b → False := by
      intro a b hab hbnd hget
      have htake_len : (p.take a).length = a := by
        rw [Walk.take_length, min_eq_left (by omega : a ≤ p.length)]
      let q := (p.take a).append ((p.drop b).copy hget.symm rfl)
      have hqlen : q.length = a + (p.length - b) := by
        simp only [q, Walk.length_append, Walk.length_copy, Walk.take_length, Walk.drop_length,
          min_eq_left (show a ≤ p.length by omega)]
      have hqlt : q.length < p.length := by
        rw [hqlen]
        omega
      have hqge : 2 ≤ q.length := by
        rw [hqlen]
        by_contra hlt
        have hle1 : a + (p.length - b) ≤ 1 := by omega
        have ha1 : a ≤ 1 := by omega
        by_cases ha0 : a = 0
        · rw [ha0] at hget
          by_cases hbEq : b = p.length
          · rw [hbEq, Walk.getVert_zero, Walk.getVert_length] at hget
            exact huv hget
          · have hb1 : b = p.length - 1 := by omega
            have hmemI := hint b (by omega) (by omega)
            rw [← hget, Walk.getVert_zero] at hmemI
            exact (hCof_uv t).1 hmemI
        · have ha1eq : a = 1 := by omega
          have hbEq : b = p.length := by omega
          have hmemI := hint a (by omega) (by omega)
          rw [ha1eq] at hget hmemI
          rw [hget, hbEq, Walk.getVert_length] at hmemI
          exact (hCof_uv t).2 hmemI
      have hqint : ∀ k, 0 < k → k < q.length → q.getVert k ∈ Cof t := by
        intro k hk0 hkL
        have hkL' : k < a + (p.length - b) := by simpa [hqlen] using hkL
        unfold q
        rw [Walk.getVert_append']
        simp only [htake_len]
        split_ifs with hka
        · rw [Walk.take_getVert, min_eq_right hka]
          exact hint k hk0 (by omega)
        · rw [Walk.getVert_copy, Walk.drop_getVert]
          exact hint (b + (k - a)) (by omega) (by omega)
      exact (lt_irrefl _ ((hshort q hqint hqge).trans_lt hqlt)).elim
    have hpath : p.IsPath := by
      apply Walk.IsPath.mk'
      by_contra hdup
      rw [List.nodup_iff_injective_getElem] at hdup
      obtain ⟨i, j, heq, hneij⟩ := Function.not_injective_iff.mp hdup
      have hgetij : p.getVert i.1 = p.getVert j.1 := by
        rw [← p.support_getElem_eq_getVert i.isLt, ← p.support_getElem_eq_getVert j.isLt]
        exact heq
      have hiL : i.1 ≤ p.length := by
        have hlt : i.1 < p.support.length := i.isLt
        have hlen : p.support.length = p.length + 1 := p.length_support
        omega
      have hjL : j.1 ≤ p.length := by
        have hlt : j.1 < p.support.length := j.isLt
        have hlen : p.support.length = p.length + 1 := p.length_support
        omega
      rcases lt_or_gt_of_ne (fun h => hneij (Fin.ext h)) with hij | hij
      · exact hfalse i.1 j.1 hij hjL hgetij
      · exact hfalse j.1 i.1 hij hiL hgetij.symm
    have hnot2 : p.length ≠ 2 := by
      intro h2
      have h01 : G.Adj u (p.getVert 1) := by
        simpa [Walk.getVert_zero] using p.adj_getVert_succ (by omega : (0 : ℕ) < p.length)
      have h1v : G.Adj (p.getVert 1) v := by
        have hadj := p.adj_getVert_succ (by omega : 1 < p.length)
        have hv : p.getVert 2 = v := by simpa [h2] using Walk.getVert_length p
        simpa [hv] using hadj
      exact htri {u, p.getVert 1, v} (is3Clique_triple_iff.mpr ⟨h01, huv_adj, h1v⟩)
    have hnot3 : p.length ≠ 3 := by
      intro h3
      have h01 : G.Adj u (p.getVert 1) := by
        simpa [Walk.getVert_zero] using p.adj_getVert_succ (by omega : 0 < p.length)
      have h12 : G.Adj (p.getVert 1) (p.getVert 2) := p.adj_getVert_succ (by omega : 1 < p.length)
      have h2v : G.Adj (p.getVert 2) v := by
        have hadj := p.adj_getVert_succ (by omega : 2 < p.length)
        have hv : p.getVert 3 = v := by simpa [h3] using Walk.getVert_length p
        simpa [hv] using hadj
      have hneU : u ≠ p.getVert 2 := by
        intro h
        exact (hCof_uv t).1 (h.symm ▸ hint 2 (by omega) (by omega))
      have hneV : p.getVert 1 ≠ v := by
        intro h
        exact (hCof_uv t).2 (h.symm ▸ hint 1 (by omega) (by omega))
      exact hC (fourCycle_isContained h01 h12 h2v huv_adj.symm hneU hneV)
    have hfar : ∀ i j, i ≤ p.length → j ≤ p.length → i + 2 ≤ j →
        ¬ (i = 0 ∧ j = p.length) → ¬ G.Adj (p.getVert i) (p.getVert j) := by
      intro i j hi hj hgap hnot hadj
      have htake_len : (p.take i).length = i := by
        rw [Walk.take_length, min_eq_left hi]
      let qf := (p.take i).append ((p.drop j).cons hadj)
      have hqflen : qf.length = i + ((p.length - j) + 1) := by
        simp only [qf, Walk.length_append, Walk.length_cons, Walk.drop_length, htake_len]
      have hqfge : 2 ≤ qf.length := by
        rw [hqflen]
        by_contra hlt
        exact hnot (by omega)
      have hqflt : qf.length < p.length := by
        rw [hqflen]
        omega
      have hqfint : ∀ k, 0 < k → k < qf.length → qf.getVert k ∈ Cof t := by
        intro k hk0 hkL
        have hkL' : k < i + ((p.length - j) + 1) := by simpa [hqflen] using hkL
        unfold qf
        rw [Walk.getVert_append']
        simp only [htake_len]
        split_ifs with hki
        · rw [Walk.take_getVert, min_eq_right hki]
          exact hint k hk0 (by omega)
        · have hm : k - i ≠ 0 := by omega
          rw [Walk.getVert_cons (p.drop j) hadj hm, Walk.drop_getVert]
          exact hint (j + ((k - i) - 1)) (by omega) (by omega)
      exact (lt_irrefl _ ((hshort qf hqfint hqfge).trans_lt hqflt)).elim
    exact ⟨p, by omega, hpath, hint, hfar⟩
  obtain ⟨p, hp4, hppath, hpint, hpfar⟩ := through x y hxy
  obtain ⟨q, hq4, hqpath, hqint, hqfar⟩ := through y x fun hryx => hxy hryx.symm
  have hCof_disj {a b : V} (ha : a ∈ Cof x) (hb : b ∈ Cof y) : a ≠ b := by
    intro hab
    rcases ha with ⟨ha', hax⟩
    rcases hb with ⟨hb', hby⟩
    have hab' : (⟨a, ha'⟩ : ↥(sᶜ)) = ⟨b, hb'⟩ := Subtype.ext hab
    exact hxy (hax.trans (hab' ▸ hby.symm))
  have hno_cross {a b : V} (ha : a ∈ Cof x) (hb : b ∈ Cof y) : ¬ G.Adj a b := by
    intro hadj
    rcases ha with ⟨ha', hax⟩
    rcases hb with ⟨hb', hby⟩
    have hadjH : H.Adj (⟨a, ha'⟩ : ↥(sᶜ)) (⟨b, hb'⟩ : ↥(sᶜ)) :=
      SimpleGraph.induce_adj.mpr hadj
    have hstep : H.Reachable (⟨a, ha'⟩ : ↥(sᶜ)) (⟨b, hb'⟩ : ↥(sᶜ)) := ⟨hadjH.toWalk⟩
    exact hxy (hax.trans (hstep.trans hby.symm))
  let x1 := p.getVert (p.length - 3)
  let y1 := p.getVert (p.length - 2)
  let z1 := p.getVert (p.length - 1)
  let x2 := q.getVert (q.length - 3)
  let y2 := q.getVert (q.length - 2)
  let z2 := q.getVert (q.length - 1)
  have hx1y1 : G.Adj x1 y1 := by
    have hadj := p.adj_getVert_succ (show p.length - 3 < p.length by omega)
    simpa [x1, y1, show (p.length - 3) + 1 = p.length - 2 by omega] using hadj
  have hy1z1 : G.Adj y1 z1 := by
    have hadj := p.adj_getVert_succ (show p.length - 2 < p.length by omega)
    simpa [y1, z1, show (p.length - 2) + 1 = p.length - 1 by omega] using hadj
  have hz1v : G.Adj z1 v := by
    have hadj := p.adj_getVert_succ (show p.length - 1 < p.length by omega)
    have hv : p.getVert p.length = v := Walk.getVert_length p
    simpa [z1, show (p.length - 1) + 1 = p.length by omega, hv] using hadj
  have hx2y2 : G.Adj x2 y2 := by
    have hadj := q.adj_getVert_succ (show q.length - 3 < q.length by omega)
    simpa [x2, y2, show (q.length - 3) + 1 = q.length - 2 by omega] using hadj
  have hy2z2 : G.Adj y2 z2 := by
    have hadj := q.adj_getVert_succ (show q.length - 2 < q.length by omega)
    simpa [y2, z2, show (q.length - 2) + 1 = q.length - 1 by omega] using hadj
  have hz2v : G.Adj z2 v := by
    have hadj := q.adj_getVert_succ (show q.length - 1 < q.length by omega)
    have hv : q.getVert q.length = v := Walk.getVert_length q
    simpa [z2, show (q.length - 1) + 1 = q.length by omega, hv] using hadj
  have hy2x2 : G.Adj y2 x2 := hx2y2.symm
  have hz2y2 : G.Adj z2 y2 := hy2z2.symm
  have hvz2 : G.Adj v z2 := hz2v.symm
  let w1 : G.Walk y2 x2 := hy2x2.toWalk
  let w2 : G.Walk z2 x2 := w1.cons hz2y2
  let w3 : G.Walk v x2 := w2.cons hvz2
  let w4 : G.Walk z1 x2 := w3.cons hz1v
  let w5 : G.Walk y1 x2 := w4.cons hy1z1
  let w : G.Walk x1 x2 := w5.cons hx1y1
  have hsup : w.support = [x1, y1, z1, v, z2, y2, x2] := by
    unfold w w5 w4 w3 w2 w1
    simp [Walk.support_cons, Walk.support_nil]
  have hwlen : w.length = 6 := by
    have hs := w.length_support
    rw [hsup] at hs
    simp at hs
    omega
  have hlist : ([x1, y1, z1, v, z2, y2, x2] : List V).length = 7 := by simp
  have hget (n : ℕ) (hn : n < 7) : w.getVert n =
      [x1, y1, z1, v, z2, y2, x2][n]'(by rw [hlist]; exact hn) := by
    have hlt : n < w.support.length := by
      rw [Walk.length_support, hwlen]
      omega
    simpa [hsup] using (w.support_getElem_eq_getVert hlt).symm
  have hpref (n : ℕ) (hn : n ≤ 3) : w.getVert n = p.getVert (p.length - 3 + n) := by
    interval_cases n
    · rw [Walk.getVert_zero]
      unfold x1
      exact congrArg p.getVert (by omega)
    · have h1 : w.getVert 1 = y1 := by simpa using hget 1 (by decide)
      rw [h1]
      unfold y1
      exact congrArg p.getVert (by omega)
    · have h2 : w.getVert 2 = z1 := by simpa using hget 2 (by decide)
      rw [h2]
      unfold z1
      exact congrArg p.getVert (by omega)
    · have h3 : w.getVert 3 = v := by simpa using hget 3 (by decide)
      rw [h3]
      have hv : p.getVert (p.length - 3 + 3) = v := by
        have : p.length - 3 + 3 = p.length := by omega
        simp [this]
      exact hv.symm
  have hright (n : ℕ) (hn0 : 3 ≤ n) (hn : n ≤ 6) :
      w.getVert n = q.getVert (q.length - (n - 3)) := by
    interval_cases n
    · have h3 : w.getVert 3 = v := by simpa using hget 3 (by decide)
      rw [h3]
      have hv : q.getVert (q.length - (3 - 3)) = v := by simp
      exact hv.symm
    · have h4 : w.getVert 4 = z2 := by simpa using hget 4 (by decide)
      rw [h4]
    · have h5 : w.getVert 5 = y2 := by simpa using hget 5 (by decide)
      rw [h5]
    · have h6 : w.getVert 6 = x2 := by simpa using hget 6 (by decide)
      rw [h6]
  have hleftC (n : ℕ) (hn : n ≤ 2) : w.getVert n ∈ Cof x := by
    rw [hpref n (by omega)]
    exact hpint (p.length - 3 + n) (by omega) (by omega)
  have hrightC (n : ℕ) (hn4 : 4 ≤ n) (hn : n ≤ 6) : w.getVert n ∈ Cof y := by
    rw [hright n (by omega) hn]
    exact hqint (q.length - (n - 3)) (by omega) (by omega)
  have hneq (i j : ℕ) (hj : j ≤ 6) (hij : i < j) : w.getVert i ≠ w.getVert j := by
    intro heq
    by_cases hj3 : j ≤ 3
    · have := hppath.getVert_injOn
        (Set.mem_ofPred.mpr (show p.length - 3 + i ≤ p.length by omega))
        (Set.mem_ofPred.mpr (show p.length - 3 + j ≤ p.length by omega))
        ((hpref i (by omega)).symm.trans (heq.trans (hpref j (by omega))))
      omega
    · by_cases hi3 : 3 ≤ i
      · have := hqpath.getVert_injOn
          (Set.mem_ofPred.mpr (show q.length - (j - 3) ≤ q.length by omega))
          (Set.mem_ofPred.mpr (show q.length - (i - 3) ≤ q.length by omega))
          ((hright j (by omega) hj).symm.trans (heq.symm.trans (hright i hi3 (by omega))))
        omega
      · exact hCof_disj (hleftC i (by omega)) (hrightC j (by omega) hj) heq
  have hbad (i j : ℕ) (hgap : i + 2 ≤ j) (hj : j ≤ 6) : ¬ G.Adj (w.getVert i) (w.getVert j) := by
    intro hadj
    by_cases hj3 : j ≤ 3
    · exact hpfar (p.length - 3 + i) (p.length - 3 + j) (by omega) (by omega) (by omega)
        (by rintro ⟨_, _⟩; omega)
        (by simpa [hpref i (by omega), hpref j (by omega)] using hadj)
    · by_cases hi3 : 3 ≤ i
      · exact hqfar (q.length - (j - 3)) (q.length - (i - 3)) (by omega) (by omega) (by omega)
          (by rintro ⟨_, _⟩; omega)
          (by simpa [hright j (by omega) hj, hright i hi3 (by omega)] using hadj.symm)
      · exact hno_cross (hleftC i (by omega)) (hrightC j (by omega) hj) hadj
  have hwpath : w.IsPath := by
    apply Walk.IsPath.mk'
    rw [List.nodup_iff_injective_getElem]
    intro i j heq
    by_contra hne
    have hij : i.1 ≠ j.1 := fun h => hne (Fin.ext h)
    have hlt_i : i.1 < w.support.length := i.isLt
    have hlt_j : j.1 < w.support.length := j.isLt
    have hgetij : w.getVert i.1 = w.getVert j.1 := by
      rw [← w.support_getElem_eq_getVert hlt_i, ← w.support_getElem_eq_getVert hlt_j]
      exact heq
    have hi6 : i.1 ≤ 6 := by
      have hlen : w.support.length = 7 := by rw [Walk.length_support, hwlen]
      omega
    have hj6 : j.1 ≤ 6 := by
      have hlen : w.support.length = 7 := by rw [Walk.length_support, hwlen]
      omega
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact hneq i.1 j.1 hj6 hlt hgetij
    · exact hneq j.1 i.1 hi6 hlt hgetij.symm
  have hwchord : w.IsChordless := by
    rw [Walk.isChordless_iff_forall_mem_edges]
    intro a b ha hb hab
    obtain ⟨i, hi, hiL⟩ := (Walk.mem_support_iff_exists_getVert).1 ha
    obtain ⟨j, hj, hjL⟩ := (Walk.mem_support_iff_exists_getVert).1 hb
    have hi6 : i ≤ 6 := by simpa [hwlen] using hiL
    have hj6 : j ≤ 6 := by simpa [hwlen] using hjL
    rcases lt_trichotomy i j with hij | hij | hij
    · by_cases hstep : j = i + 1
      · have hmem : s(w.getVert i, w.getVert (i + 1)) ∈ w.edges :=
          (Walk.mk_mem_edges_iff_exists w).2 ⟨i, by rw [hwlen]; omega, rfl⟩
        rw [← hi, ← hj, hstep]
        exact hmem
      · exact (hbad i j (by omega) hj6 (by simpa [hi, hj] using hab)).elim
    · exact (hab.ne (hi.symm.trans (hij ▸ hj))).elim
    · by_cases hstep : i = j + 1
      · have hmem : s(w.getVert j, w.getVert (j + 1)) ∈ w.edges :=
          (Walk.mk_mem_edges_iff_exists w).2 ⟨j, by rw [hwlen]; omega, rfl⟩
        rw [← hi, ← hj, hstep, Sym2.eq_swap]
        exact hmem
      · exact (hbad j i (by omega) hi6 (by simpa [hi, hj] using hab.symm)).elim
  have hind : w.toSubgraph.IsInduced := Walk.isInduced_toSubgraph.mpr hwchord
  have hcont : pathGraph (w.length + 1) ⊴ G :=
    hwpath.pathGraphIsoToSubgraph.isIndContained.trans hind.isIndContained
  have hlen7 : w.length + 1 = 7 := by simp [hwlen]
  rw [hlen7] at hcont
  exact hp hcont

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

/-- The key cross-edge fact in Lemma 3.3: external neighbours of two
nonadjacent neighbours of `v` must be adjacent. The exclusion of `v` itself
is explicit because the external sets are outside the *closed* neighbourhood. -/
lemma section3_external_adj (hC : StrongC4Free G) (hp : IsPkFree G 5)
    {v x y a b : V} (hvx : G.Adj v x) (hvy : G.Adj v y)
    (hxy : x ≠ y) (hnxy : ¬ G.Adj x y)
    (hxa : G.Adj x a) (hyb : G.Adj y b)
    (hav : a ≠ v) (hbv : b ≠ v) (hnva : ¬ G.Adj v a) (hnvb : ¬ G.Adj v b) :
    G.Adj a b := by
  have hnxb : ¬ G.Adj x b := by
    intro h
    exact hC (fourCycle_isContained hvx h hyb.symm hvy.symm hbv.symm hxy)
  have hnya : ¬ G.Adj y a := by
    intro h
    exact hC (fourCycle_isContained hvx hxa h.symm hvy.symm hav.symm hxy)
  have hab : a ≠ b := by
    intro h
    exact hnya (h.symm ▸ hyb)
  have hay : a ≠ y := by
    intro h
    exact hnva (h.symm ▸ hvy)
  have hbx : b ≠ x := by
    intro h
    exact hnvb (h.symm ▸ hvx)
  by_contra hnab
  let verts : Fin 5 → V := ![a, x, v, y, b]
  let f : pathGraph 5 ↪g G :=
    { toFun := verts
      inj' := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [verts, hxa.ne, hvx.ne, hvy.ne, hyb.ne, Ne.symm]
      map_rel_iff' := by
        intro i j
        change G.Adj (verts i) (verts j) ↔ (pathGraph 5).Adj i j
        fin_cases i <;> fin_cases j <;>
          simp [verts, pathGraph_adj, hxa, hxa.symm, hvx, hvx.symm, hvy, hvy.symm,
            hyb, hyb.symm, hnxy, hnya, hnxb, hnva, hnvb, hnab,
            G.adj_comm, SimpleGraph.irrefl] }
  exact hp ⟨f⟩

/-- If two different units have nonempty external neighbourhoods, each
external neighbourhood has at most one vertex (Lemma 3.3's key fact). -/
lemma section3_external_subsingleton (hC : StrongC4Free G) (hp : IsPkFree G 5)
    {v x y b : V} (hvx : G.Adj v x) (hvy : G.Adj v y)
    (hxy : x ≠ y) (hnxy : ¬ G.Adj x y)
    (hyb : G.Adj y b) (hbv : b ≠ v) (hnvb : ¬ G.Adj v b) :
    {a | G.Adj x a ∧ a ≠ v ∧ ¬ G.Adj v a}.Subsingleton := by
  have hxb : x ≠ b := by
    intro h
    exact hnvb (h ▸ hvx)
  intro a ha a' ha'
  have hab := section3_external_adj hC hp hvx hvy hxy hnxy ha.1 hyb ha.2.1 hbv ha.2.2 hnvb
  have ha'b := section3_external_adj hC hp hvx hvy hxy hnxy ha'.1 hyb ha'.2.1 hbv ha'.2.2 hnvb
  exact commonNeighbors_subsingleton hC hxb ⟨ha.1, hab.symm⟩ ⟨ha'.1, ha'b.symm⟩

/-- Three pairwise nonadjacent neighbours cannot have two active external
neighbourhoods. This is the induced `P₅` obstruction in Case 2 of Lemma 3.3. -/
lemma section3_no_two_active (hC : StrongC4Free G) (hp : IsPkFree G 5)
    {v x y z a b : V} (hvx : G.Adj v x) (hvy : G.Adj v y) (hvz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hnxy : ¬ G.Adj x y) (hnxz : ¬ G.Adj x z) (hnyz : ¬ G.Adj y z)
    (hya : G.Adj y a) (hzb : G.Adj z b)
    (hav : a ≠ v) (hbv : b ≠ v) (hnva : ¬ G.Adj v a) (hnvb : ¬ G.Adj v b) : False := by
  have hab := section3_external_adj hC hp hvy hvz hyz hnyz hya hzb hav hbv hnva hnvb
  have hnxa : ¬ G.Adj x a := by
    intro h
    exact hC (fourCycle_isContained hvx h hya.symm hvy.symm hav.symm hxy)
  have hnxb : ¬ G.Adj x b := by
    intro h
    exact hC (fourCycle_isContained hvx h hzb.symm hvz.symm hbv.symm hxz)
  have hnyb : ¬ G.Adj y b := by
    intro h
    exact hC (fourCycle_isContained hvy h hzb.symm hvz.symm hbv.symm hyz)
  have hax : a ≠ x := by
    intro h
    exact hnva (h.symm ▸ hvx)
  have hbx : b ≠ x := by
    intro h
    exact hnvb (h.symm ▸ hvx)
  have hby : b ≠ y := by
    intro h
    exact hnvb (h.symm ▸ hvy)
  let verts : Fin 5 → V := ![x, v, y, a, b]
  let f : pathGraph 5 ↪g G :=
    { toFun := verts
      inj' := by
        intro i j hij
        fin_cases i <;> fin_cases j <;>
          simp_all [verts, hvx.ne, hvy.ne, hya.ne, hab.ne, Ne.symm]
      map_rel_iff' := by
        intro i j
        change G.Adj (verts i) (verts j) ↔ (pathGraph 5).Adj i j
        fin_cases i <;> fin_cases j <;>
          simp [verts, pathGraph_adj, hvx, hvx.symm, hvy, hvy.symm,
            hya, hya.symm, hab, hab.symm, hnxy, hnxa, hnxb, hnva, hnvb, hnyb,
            G.adj_comm, SimpleGraph.irrefl] }
  exact hp ⟨f⟩

/-- A neighbour with empty external neighbourhood is simplicial. -/
lemma section3_inactive_simplicial [Fintype V] [DecidableEq V]
    (hC : StrongC4Free G) {v y : V} (hvy : G.Adj v y)
    (hinactive : ∀ a, G.Adj y a → a = v ∨ G.Adj v a) : lambda G y = 1 := by
  classical
  let H := G.induce (G.neighborSet y)
  have hclique : ∀ a b : G.neighborSet y, a ≠ b → H.Adj a b := by
    intro a b hab
    change G.Adj a.val b.val
    rcases hinactive a.val a.property with ha | ha
    · rw [ha]
      exact (hinactive b.val b.property).resolve_left (by
        intro hb
        exact hab (Subtype.ext (ha.trans hb.symm)))
    · rcases hinactive b.val b.property with hb | hb
      · rw [hb]
        exact ha.symm
      · have heq : a.val = b.val := commonNeighbors_subsingleton hC hvy.ne
          ⟨ha, a.property⟩ ⟨hb, b.property⟩
        exact (hab (Subtype.ext heq)).elim
  have hlow : 1 ≤ H.indepNum := by
    have hI : H.IsIndepSet ({⟨v, hvy.symm⟩} : Finset (G.neighborSet y)) := by
      simp [isIndepSet_iff]
    simpa using hI.card_le_indepNum
  obtain ⟨s, hs⟩ := H.exists_isNIndepSet_indepNum
  have hcard : s.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    by_contra hab
    exact hs.isIndepSet ha hb hab (hclique a b hab)
  change H.indepNum = 1
  have := hs.card_eq
  omega

/-- An inactive unit supplies a simplicial vertex with a unique high neighbour.
Both endpoints must be inactive when the unit is an edge. -/
lemma section3_inactive_private [Fintype V] [DecidableEq V]
    (hC : StrongC4Free G) {v y : V} (hvy : G.Adj v y)
    (hinactive : ∀ a, G.Adj y a → a = v ∨ G.Adj v a)
    (hunit : ∀ z, G.Adj y z → z ≠ v → ∀ a, G.Adj z a → a = v ∨ G.Adj v a) :
    lambda G y = 1 ∧ ∀ z, G.Adj y z → 3 ≤ lambda G z → z = v := by
  refine ⟨section3_inactive_simplicial hC hvy hinactive, ?_⟩
  intro z hyz hz
  by_contra hne
  have hvz : G.Adj v z := (hinactive z hyz).resolve_left hne
  have := section3_inactive_simplicial hC hvz (hunit z hyz hne)
  omega

/-- Among the neighbourhood components of a high vertex, at most one
contains a vertex with a neighbour outside the closed neighbourhood. -/
lemma section3_active_units [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hC : StrongC4Free G) (hp : IsPkFree G 5) (v : V) (hv : 3 ≤ lambda G v) :
    let H := G.induce (G.neighborSet v)
    {C : H.ConnectedComponent | ∃ x : G.neighborSet v,
      H.connectedComponentMk x = C ∧ ∃ a, G.Adj x.val a ∧ a ≠ v ∧ ¬ G.Adj v a}.Subsingleton := by
  classical
  dsimp only
  let H := G.induce (G.neighborSet v)
  have hcard : 3 ≤ Nat.card H.ConnectedComponent := by
    rw [lambda_eq_ncard_components hC v]
    exact hv
  intro C hCact D hDact
  by_contra hCD
  obtain ⟨y, hyC, a, hya, hav, hnva⟩ := hCact
  obtain ⟨z, hzD, b, hzb, hbv, hnvb⟩ := hDact
  have hex : ∃ E : H.ConnectedComponent, E ≠ C ∧ E ≠ D := by
    by_contra hnot
    have hsub : (Set.univ : Set H.ConnectedComponent) ⊆ {C, D} := by
      intro E _
      by_contra he
      have hneC : E ≠ C := by intro h; exact he (by simp [h])
      have hneD : E ≠ D := by intro h; exact he (by simp [h])
      exact hnot ⟨E, hneC, hneD⟩
    have hle := Set.ncard_le_ncard hsub
    have htwo : ({C, D} : Set H.ConnectedComponent).ncard ≤ 2 := by simp [Set.ncard_pair hCD]
    rw [Set.ncard_univ] at hle
    omega
  obtain ⟨E, hEC, hED⟩ := hex
  let x : G.neighborSet v := E.out
  have hxE : H.connectedComponentMk x = E := E.out_eq
  have hsep {p q : G.neighborSet v} (hne : H.connectedComponentMk p ≠ H.connectedComponentMk q) :
      p.val ≠ q.val ∧ ¬ G.Adj p.val q.val := by
    constructor
    · intro h
      exact hne (congrArg H.connectedComponentMk (Subtype.ext h))
    · intro h
      exact hne (ConnectedComponent.sound (G := H) ((show H.Adj p q from h).reachable))
  have hxy := hsep (p := x) (q := y) (by rw [hxE, hyC]; exact hEC)
  have hxz := hsep (p := x) (q := z) (by rw [hxE, hzD]; exact hED)
  have hyz := hsep (p := y) (q := z) (by rw [hyC, hzD]; exact hCD)
  exact section3_no_two_active hC hp x.property y.property z.property
    hxy.1 hxz.1 hyz.1 hxy.2 hxz.2 hyz.2 hya hzb hav hbv hnva hnvb

/-- A high vertex has at least `λ(v)-1` private simplicial neighbours. -/
lemma section3_private_card [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hC : StrongC4Free G) (hp : IsPkFree G 5) (v : V) (hv : 3 ≤ lambda G v) :
    lambda G v - 1 ≤ (univ.filter fun y => G.Adj v y ∧ lambda G y = 1 ∧
      ∀ z, G.Adj y z → 3 ≤ lambda G z → z = v).card := by
  classical
  let H := G.induce (G.neighborSet v)
  let active : Set H.ConnectedComponent := {C | ∃ x : G.neighborSet v,
    H.connectedComponentMk x = C ∧ ∃ a, G.Adj x.val a ∧ a ≠ v ∧ ¬ G.Adj v a}
  have hactive : active.Subsingleton := section3_active_units hC hp v hv
  have hleA : active.ncard ≤ 1 := Set.ncard_le_one_iff_subsingleton.mpr hactive
  letI := Fintype.ofFinite H.ConnectedComponent
  let inactive := univ.filter (fun C : H.ConnectedComponent => C ∉ active)
  have hcardI : lambda G v - 1 ≤ inactive.card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset H.ConnectedComponent)) (p := fun C => C ∈ active)
    have hA : (univ.filter fun C : H.ConnectedComponent => C ∈ active).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro C hC D hD
      exact hactive (mem_filter.mp hC).2 (mem_filter.mp hD).2
    have hCcard : Fintype.card H.ConnectedComponent = lambda G v := by
      rw [← Nat.card_eq_fintype_card]
      exact lambda_eq_ncard_components hC v
    simp only [Finset.card_univ] at hsplit
    dsimp [inactive]
    omega
  let good := univ.filter fun y => G.Adj v y ∧ lambda G y = 1 ∧
    ∀ z, G.Adj y z → 3 ≤ lambda G z → z = v
  have hmem (C : H.ConnectedComponent) (hC : C ∈ inactive) : C.out.val ∈ good := by
    have hnot : C ∉ active := (mem_filter.mp hC).2
    have hinact {y : G.neighborSet v} (hy : H.connectedComponentMk y = C) :
        ∀ a, G.Adj y.val a → a = v ∨ G.Adj v a := by
      intro a ha
      by_contra h
      push Not at h
      exact hnot ⟨y, hy, a, ha, h.1, h.2⟩
    have hpriv := section3_inactive_private (G := G) ‹StrongC4Free G› C.out.property
      (hinact C.out_eq) (by
        intro z hyz hz
        have hvz := (hinact C.out_eq z hyz).resolve_left hz
        let z' : G.neighborSet v := ⟨z, hvz⟩
        have hzC : H.connectedComponentMk z' = C :=
          (ConnectedComponent.sound (G := H) (show H.Adj C.out z' from hyz).reachable).symm.trans C.out_eq
        exact hinact hzC)
    exact mem_filter.mpr ⟨mem_univ _, C.out.property, hpriv⟩
  have hinj : ∀ C ∈ inactive, ∀ D ∈ inactive, C.out.val = D.out.val → C = D := by
    intro C _ D _ h
    have hsub : C.out = D.out := Subtype.ext h
    exact C.out_eq.symm.trans ((congrArg H.connectedComponentMk hsub).trans D.out_eq)
  exact hcardI.trans (Finset.card_le_card_of_injOn (fun C => C.out.val) hmem hinj)

/-- The counting step of Lemma 3.3. The structural argument must supply the
weighted bound on high vertices by the number of simplicial vertices. No graph
hypotheses are needed for this purely numerical implication. -/
lemma section3_counting [Fintype V] [DecidableEq V] (f : V → ℕ)
    (hcharge : (∑ v ∈ univ.filter (fun v => 3 ≤ f v), (f v - 1)) ≤
      (univ.filter fun v => f v = 1).card) :
    (∑ v, f v) ≤ 2 * Fintype.card V - (univ.filter fun v => 3 ≤ f v).card := by
  classical
  have hpoint (v : V) : f v + (if 3 ≤ f v then 1 else 0) +
      (if f v = 1 then 1 else 0) ≤ 2 + (if 3 ≤ f v then f v - 1 else 0) := by
    split_ifs <;> omega
  have hsum := Finset.sum_le_sum (s := (univ : Finset V)) (fun v _ => hpoint v)
  have hcharge' : (∑ v, if 3 ≤ f v then f v - 1 else 0) ≤
      (univ.filter fun v => f v = 1).card := by
    simpa only [← Finset.sum_filter] using hcharge
  simp only [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, Nat.cast_id] at hsum
  omega

/-- Lemma 3.3. `h` is the number of vertices with `λ ≥ 3`. -/
theorem lemma_3_3 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 5) :
    neighbourhoodIndependenceSum G ≤
        2 * Fintype.card V -
          (Finset.univ.filter fun v => 3 ≤ lambda G v).card ∧
      neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V := by
  classical
  let good (v : V) := univ.filter fun y => G.Adj v y ∧ lambda G y = 1 ∧
    ∀ z, G.Adj y z → 3 ≤ lambda G z → z = v
  let high := univ.filter fun v => 3 ≤ lambda G v
  have hd : (high : Set V).PairwiseDisjoint good := by
    intro v hv u hu hne
    apply Finset.disjoint_left.mpr
    intro y hyv hyu
    have hyu' := (mem_filter.mp hyu).2
    have hyv' := (mem_filter.mp hyv).2
    exact hne (hyv'.2.2 u hyu'.1.symm (mem_filter.mp hu).2).symm
  have hs : high.biUnion good ⊆ univ.filter (fun y => lambda G y = 1) := by
    intro y hy
    obtain ⟨v, _, hyv⟩ := mem_biUnion.mp hy
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hyv).2.2.1⟩
  have hc : (∑ v ∈ high, (lambda G v - 1)) ≤
      (univ.filter fun y => lambda G y = 1).card := by
    calc
      (∑ v ∈ high, (lambda G v - 1)) ≤ ∑ v ∈ high, (good v).card :=
        sum_le_sum (fun v hv => section3_private_card hC hp v (mem_filter.mp hv).2)
      _ = (high.biUnion good).card := (card_biUnion hd).symm
      _ ≤ (univ.filter fun y => lambda G y = 1).card := card_le_card hs
  have hmain := section3_counting (lambda G) hc
  exact ⟨hmain, hmain.trans (Nat.sub_le _ _)⟩

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
  classical
  let W : Set V := {v | ∀ i, c i ≠ v}
  have hmeet (w : V) (hw : w ∈ W) : ∃ i, G.Adj w (c i) := by
    obtain ⟨i, hi⟩ := hdom w
    exact ⟨i, hi.resolve_left (Ne.symm (hw i))⟩
  have hWeq : W = hexOutside c := by
    ext w
    simp [W, hexOutside, Set.mem_range]
  have hm := hexDominating_mass hC hp c hdom
  rw [← hWeq] at hm
  refine ⟨?_, ?_, ?_, ?_, hm.1, hm.2, ?_⟩
  · intro w hw
    exact hexTrace_antipodal hC hp c hw (hmeet w hw)
  · intro w hw w' hw' hne i
    exact hexTrace_disjoint hC hp c hw hw' hne i
  · intro w hw w' hw' _
    exact hexTrace_nonadjacent hC hp c hw hw' (hmeet w hw) (hmeet w' hw')
  · exact hexTrace_card_le_three hC hp c W (fun _ hw => hw) hmeet
  · rintro ⟨w, hw⟩
    obtain ⟨i, hi⟩ := hexTrace_eccent_le_two hC hp c hdom hw
    exact ENat.toNat_le_of_le_natCast (G.radius_le_eccent.trans hi)

/-- Lemma 3.5. -/
theorem lemma_3_5 [Fintype V] [DecidableEq V] (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 6) :
    (∃ v, G.eccent v ≤ 2) ∨ Nonempty (G ≃g cycleGraph 6) := by
  classical
  obtain ⟨X, hXconn, hXdom, hXcase⟩ := lemma_2_8 hconn hp
  haveI : Nonempty V := hconn.nonempty
  rcases hXcase with hXfree | he
  · haveI : Nonempty X := hXconn.nonempty
    obtain ⟨u, hu⟩ : ∃ u : X, ∀ x : X, x = u ∨ (G.induce X).Adj u x := by
      by_cases hn : 2 ≤ Fintype.card X
      · exact lemma_2_7 hXconn (strongC4Free_induce hC) hXfree hn
      · haveI : Subsingleton X := Fintype.card_le_one_iff_subsingleton.mp (by omega)
        exact ⟨Classical.choice hXconn.nonempty, fun x => Or.inl (Subsingleton.elim _ _)⟩
    left
    refine ⟨u.val, ?_⟩
    rw [eccent_le_iff]
    intro v
    obtain ⟨x, hx, hv⟩ := hXdom v
    rcases hu ⟨x, hx⟩ with hxu | hux
    · have hxu' : x = u.val := congrArg Subtype.val hxu
      rcases hv with rfl | hv
      · simp [hxu']
      · let p : G.Walk u.val v := (hxu' ▸ hv).symm.toWalk
        exact p.edist_le.trans (by simp [p])
    · have hux' : G.Adj u.val x := SimpleGraph.induce_adj.mp hux
      rcases hv with rfl | hv
      · exact hux'.toWalk.edist_le.trans (by simp)
      · let p : G.Walk u.val v := hv.symm.toWalk.cons hux'
        exact p.edist_le.trans (by simp [p])
  · obtain ⟨e⟩ := he
    let c : cycleGraph 6 ↪g G := e.symm.toEmbedding.trans (Embedding.induce X)
    have hcdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i) := by
      intro v
      obtain ⟨x, hx, hv⟩ := hXdom v
      refine ⟨e ⟨x, hx⟩, ?_⟩
      simpa [c] using hv
    have hc := lemma_3_4 hconn hC hp c hcdom
    let W : Set V := {v | ∀ i, c i ≠ v}
    by_cases hW : W.Nonempty
    · left
      have hr : radiusNat G ≤ 2 := hc.2.2.2.2.2.2 hW
      obtain ⟨u, hu⟩ := G.exists_eccent_eq_radius
      refine ⟨u, ?_⟩
      rw [hu, ← ENat.natCast_toNat ((G.radius_ne_top_iff).2 hconn)]
      exact_mod_cast hr
    · right
      have hsurj : Function.Surjective c := by
        intro v
        by_contra hv
        apply hW
        refine ⟨v, ?_⟩
        intro i hi
        exact hv ⟨i, hi⟩
      let iso : cycleGraph 6 ≃g G :=
        { toEquiv := Equiv.ofBijective c ⟨c.injective, hsurj⟩
          map_rel_iff' := c.map_rel_iff' }
      exact ⟨iso.symm⟩

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
  -- missing: layer mass counts, canonical extremal isomorphisms, chordal elimination, and small-order/equality classification
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
  intro i hoff
  by_contra hnot
  have hi0 : i.val ≠ 0 := fun h => hnot (Or.inl h)
  have hil : i.val ≠ n - 1 := fun h => hnot (Or.inr h)
  have hlt : i.val < n := i.isLt
  let p : Fin n := ⟨i.val - 1, by omega⟩
  let q : Fin n := ⟨i.val + 1, by omega⟩
  have hpne : p ≠ i := by
    intro h
    have : p.val = i.val := congrArg Fin.val h
    simp [p] at this
    omega
  have hqne : i ≠ q := by
    intro h
    have : i.val = q.val := congrArg Fin.val h
    simp [q] at this
  have hpq : p ≠ q := by
    intro h
    have : p.val = q.val := congrArg Fin.val h
    simp [p, q] at this
  have hadj_p : G.Adj (f p) (f i) := by
    rw [f.map_adj_iff, pathGraph_adj]
    refine Or.inl ?_
    simp [p]
    omega
  have hadj_q : G.Adj (f i) (f q) := by
    rw [f.map_adj_iff, pathGraph_adj]
    refine Or.inl ?_
    simp [q]
  have hchord : ¬ G.Adj (f p) (f q) := by
    rw [f.map_adj_iff, pathGraph_adj]
    simp [p, q]
    omega
  have hfpq : f p ≠ f q := f.injective.ne hpq
  rcases E.exhaustive (f i) with ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
  · exact (hoff j hj).elim
  · have hp_mem : f p = E.cycleEmb j ∨ f p ∈ E.attach j :=
      E.no_extra_attach j (f i) (f p) hj hadj_p.symm
    have hq_mem : f q = E.cycleEmb j ∨ f q ∈ E.attach j :=
      E.no_extra_attach j (f i) (f q) hj hadj_q
    rcases hp_mem with hpC | hpA <;> rcases hq_mem with hqC | hqA
    · exact (hfpq (hpC.trans hqC.symm)).elim
    · have hcross : G.Adj (f q) (E.cycleEmb j) := (E.trace j (f q) hqA j).mpr rfl
      rw [← hpC] at hcross
      exact hchord hcross.symm
    · have hcross : G.Adj (f p) (E.cycleEmb j) := (E.trace j (f p) hpA j).mpr rfl
      rw [← hqC] at hcross
      exact hchord hcross
    · have hsame := E.matching j (f i) hj (f p) hpA hadj_p.symm (f q) hqA hadj_q
      exact (hfpq hsame.symm).elim
  · have hp_mem : f p = E.cycleEmb j ∨ f p = E.cycleEmb (j + 1) :=
      (E.edge_adj j (f i) hj (f p)).mp hadj_p.symm
    have hq_mem : f q = E.cycleEmb j ∨ f q = E.cycleEmb (j + 1) :=
      (E.edge_adj j (f i) hj (f q)).mp hadj_q
    have hcycle : G.Adj (E.cycleEmb j) (E.cycleEmb (j + 1)) := by
      rw [E.cycle_induced, cycleGraph_adj']
      refine Or.inr ?_
      simp
    rcases hp_mem with hp1 | hp2 <;> rcases hq_mem with hq1 | hq2
    · exact (hfpq (hp1.trans hq1.symm)).elim
    · rw [hp1, hq2] at hchord
      exact hchord hcycle
    · rw [hp2, hq1] at hchord
      exact hchord hcycle.symm
    · exact (hfpq (hp2.trans hq2.symm)).elim

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

/-- An induced `P₄` cannot start at `s` under the hypothesis of Lemma 5.3. -/
private lemma no_induced_P4_start [DecidableEq V] {s a b c : V}
    (hab : G.Adj s a) (hbc : G.Adj a b) (hcd : G.Adj b c)
    (hsb : ¬ G.Adj s b) (hsc : ¬ G.Adj s c) (hac : ¬ G.Adj a c)
    (hsbne : s ≠ b) (hscne : s ≠ c) (hacne : a ≠ c)
    (hp : ∀ n (hn : 4 ≤ n) (f : pathGraph n ↪g G),
      f ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 4) hn⟩ ≠ s) : False := by
  let verts : Fin 4 → V := fun i =>
    if i.val = 0 then s else if i.val = 1 then a else if i.val = 2 then b else c
  have hbs : ¬ G.Adj b s := fun h => hsb h.symm
  have hcs : ¬ G.Adj c s := fun h => hsc h.symm
  have hca : ¬ G.Adj c a := fun h => hac h.symm
  let f : pathGraph 4 ↪g G := {
    toFun := verts
    inj' := by
      intro i j hij
      by_contra hne
      fin_cases i <;> fin_cases j <;> simp [verts] at hij <;> first
        | exact hne rfl
        | exact hab.ne hij
        | exact hab.ne hij.symm
        | exact hsbne hij
        | exact hsbne hij.symm
        | exact hscne hij
        | exact hscne hij.symm
        | exact hbc.ne hij
        | exact hbc.ne hij.symm
        | exact hacne hij
        | exact hacne hij.symm
        | exact hcd.ne hij
        | exact hcd.ne hij.symm
    map_rel_iff' := by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [verts, pathGraph_adj, hab, hab.symm, hbc, hbc.symm, hcd, hcd.symm,
          hsb, hbs, hsc, hcs, hac, hca, SimpleGraph.irrefl] }
  have hn4 : (4 : ℕ) ≤ 4 := le_rfl
  have hbad := hp 4 hn4 f
  have h0 : f ⟨0, Nat.lt_of_lt_of_le (by decide : (0 : ℕ) < 4) hn4⟩ = s := by
    simp [f, verts]
  exact hbad h0

/-- Lemma 5.3. No induced `P₄` starts at `s`, and `m = e(G[N(s)])`. -/
theorem lemma_5_3 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) {s : V}
    (hp : ∀ n (hn : 4 ≤ n) (f : pathGraph n ↪g G),
      f ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 4) hn⟩ ≠ s) :
    neighbourhoodIndependenceSum G ≤
      2 * (Fintype.card V - 1) - edgeCount (G.induce (G.neighborSet s)) := by
  classical
  have hdist_le (v : V) : G.dist s v ≤ 2 := by
    by_contra hgt
    have h3 : 3 ≤ G.dist s v := by omega
    obtain ⟨p, -, hlen⟩ := (hconn s v).exists_path_of_dist
    have hlen3 : 3 ≤ p.length := by omega
    let q := p.take 3
    have hqlen : q.length = 3 := by
      rw [Walk.take_length, min_eq_left hlen3]
    have hqdist : q.length = G.dist s (p.getVert 3) :=
      length_eq_dist_of_subwalk hlen (Walk.isSubwalk_take p 3)
    have hpref (k : ℕ) (hk : k ≤ 3) : G.dist s (q.getVert k) = k := by
      have hlenk : (q.take k).length = k := by
        rw [Walk.take_length, hqlen, min_eq_left hk]
      have hdistk := length_eq_dist_of_subwalk hqdist (Walk.isSubwalk_take q k)
      rw [← hdistk, hlenk]
    have hpath : q.IsPath := q.isPath_of_length_eq_dist hqdist
    have hne {i j : ℕ} (hi : i ≤ 3) (hj : j ≤ 3) (hij : i ≠ j) :
        q.getVert i ≠ q.getVert j := by
      intro h
      exact hij (hpath.getVert_injOn (Set.mem_ofPred.mpr (by omega : i ≤ q.length))
        (Set.mem_ofPred.mpr (by omega : j ≤ q.length)) h)
    have h01 : G.Adj s (q.getVert 1) := by
      simpa [Walk.getVert_zero] using q.adj_getVert_succ (by omega : 0 < q.length)
    have h12 : G.Adj (q.getVert 1) (q.getVert 2) :=
      q.adj_getVert_succ (by omega : 1 < q.length)
    have h23 : G.Adj (q.getVert 2) (q.getVert 3) :=
      q.adj_getVert_succ (by omega : 2 < q.length)
    have h02 : ¬ G.Adj s (q.getVert 2) := by
      intro h
      have hd := hpref 2 (by omega)
      have hle : G.dist s (q.getVert 2) ≤ 1 := dist_le h.toWalk
      omega
    have h03 : ¬ G.Adj s (q.getVert 3) := by
      intro h
      have hd := hpref 3 (by omega)
      have hle : G.dist s (q.getVert 3) ≤ 1 := dist_le h.toWalk
      omega
    have h13 : ¬ G.Adj (q.getVert 1) (q.getVert 3) := by
      intro h
      have hle : G.dist s (q.getVert 3) ≤
          G.dist s (q.getVert 1) + G.dist (q.getVert 1) (q.getVert 3) :=
        hconn.dist_triangle
      have hnear : G.dist (q.getVert 1) (q.getVert 3) ≤ 1 := dist_le h.toWalk
      rw [hpref 1 (by omega), hpref 3 (by omega)] at hle
      omega
    have hne02 : s ≠ q.getVert 2 := by
      simpa [Walk.getVert_zero] using
        hne (by decide : (0 : ℕ) ≤ 3) (by decide : 2 ≤ 3) (by decide)
    have hne03 : s ≠ q.getVert 3 := by
      simpa [Walk.getVert_zero] using
        hne (by decide : (0 : ℕ) ≤ 3) (by decide : 3 ≤ 3) (by decide)
    have hne13 : q.getVert 1 ≠ q.getVert 3 :=
      hne (by decide : (1 : ℕ) ≤ 3) (by decide : 3 ≤ 3) (by decide)
    exact no_induced_P4_start h01 h12 h23 h02 h03 h13 hne02 hne03 hne13 hp
  let N1 : Finset V := G.neighborFinset s
  let N2 : Finset V := univ.filter fun v => G.dist s v = 2
  have hsN1 : s ∉ N1 := by simp [N1, mem_neighborFinset]
  have hsN2 : s ∉ N2 := by simp [N2, dist_self]
  have hdisj : Disjoint N1 N2 := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    have h1 : G.dist s v = 1 := by
      rw [dist_eq_one_iff_adj]
      simpa [N1, mem_neighborFinset] using hv1
    have h2 : G.dist s v = 2 := by simpa [N2] using hv2
    omega
  have hcov : (univ : Finset V) = insert s (N1 ∪ N2) := by
    ext v
    simp only [mem_univ, mem_insert, mem_union, true_iff]
    by_cases hv : v = s
    · exact Or.inl hv
    · right
      have hle := hdist_le v
      have hpos : 0 < G.dist s v := hconn.pos_dist_of_ne (Ne.symm hv)
      rcases (show G.dist s v = 1 ∨ G.dist s v = 2 by omega) with h1 | h2
      · exact Or.inl (by simpa [N1, mem_neighborFinset, dist_eq_one_iff_adj] using h1)
      · exact Or.inr (by simp [N2, h2])
  have hex (y : V) (hy : y ∈ N2) :
      ∃ a, a ∈ N1 ∧ G.Adj a y ∧ ∀ b, b ∈ N1 → G.Adj b y → b = a := by
    have hdist : G.dist s y = 2 := by simpa [N2] using hy
    obtain ⟨p, -, hlen⟩ := (hconn s y).exists_path_of_dist
    have hlen2 : p.length = 2 := by rw [hlen, hdist]
    have hsa : G.Adj s (p.getVert 1) := by
      simpa [Walk.getVert_zero] using p.adj_getVert_succ (by omega : 0 < p.length)
    have hay : G.Adj (p.getVert 1) y := by
      have hadj := p.adj_getVert_succ (by omega : 1 < p.length)
      have hyv : p.getVert 2 = y := by simpa [hlen2] using (Walk.getVert_length p)
      simpa [hyv] using hadj
    refine ⟨p.getVert 1, by simpa [N1, mem_neighborFinset] using hsa, hay, ?_⟩
    intro b hb hby
    have hsne : s ≠ y := by
      intro h
      have : G.dist s y = 0 := by simp [h]
      omega
    have hmem1 : p.getVert 1 ∈ G.commonNeighbors s y := by
      rw [mem_commonNeighbors]
      exact ⟨hsa, hay.symm⟩
    have hmemb : b ∈ G.commonNeighbors s y := by
      rw [mem_commonNeighbors]
      exact ⟨by simpa [N1, mem_neighborFinset] using hb, hby.symm⟩
    exact commonNeighbors_subsingleton hC hsne hmemb hmem1
  let parent (y : V) (hy : y ∈ N2) : V := Classical.choose (hex y hy)
  have hparent (y : V) (hy : y ∈ N2) :
      parent y hy ∈ N1 ∧ G.Adj (parent y hy) y ∧
        ∀ b, b ∈ N1 → G.Adj b y → b = parent y hy :=
    Classical.choose_spec (hex y hy)
  have hsame {y z : V} (hy : y ∈ N2) (hz : z ∈ N2) (hyz : G.Adj y z) :
      parent z hz = parent y hy := by
    by_contra hne
    have hay := (hparent y hy).2.1
    have ha := (hparent y hy).1
    have hsy : ¬ G.Adj s y := by
      intro h
      have : G.dist s y = 1 := dist_eq_one_iff_adj.mpr h
      have : G.dist s y = 2 := by simpa [N2] using hy
      omega
    have hsz : ¬ G.Adj s z := by
      intro h
      have : G.dist s z = 1 := dist_eq_one_iff_adj.mpr h
      have : G.dist s z = 2 := by simpa [N2] using hz
      omega
    have haz : ¬ G.Adj (parent y hy) z := by
      intro h
      exact hne ((hparent z hz).2.2 (parent y hy) ha h).symm
    have hsne_y : s ≠ y := fun h => by
      have : G.dist s y = 0 := by simp [h]
      have : G.dist s y = 2 := by simpa [N2] using hy
      omega
    have hsne_z : s ≠ z := fun h => by
      have : G.dist s z = 0 := by simp [h]
      have : G.dist s z = 2 := by simpa [N2] using hz
      omega
    have hane : parent y hy ≠ z := by
      intro h
      have h1 : G.dist s (parent y hy) = 1 := by
        rw [dist_eq_one_iff_adj]
        simpa [N1, mem_neighborFinset] using ha
      have h2 : G.dist s z = 2 := by simpa [N2] using hz
      rw [h] at h1
      omega
    exact no_induced_P4_start
      (by simpa [N1, mem_neighborFinset] using ha)
      hay hyz hsy hsz haz hsne_y hsne_z hane hp
  have hlam_y (y : V) (hy : y ∈ N2) : lambda G y = 1 := by
    let a := parent y hy
    have ha := hparent y hy
    have hay : G.Adj a y := ha.2.1
    let nbr2 := N2.filter fun z => G.Adj y z
    have hnbr_le : nbr2.card ≤ 1 := by
      by_contra hgt
      obtain ⟨z1, z2, hz1, hz2, hne⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < nbr2.card)
      have hz1N : z1 ∈ N2 := (mem_filter.mp hz1).1
      have hz2N : z2 ∈ N2 := (mem_filter.mp hz2).1
      have hz1a : G.Adj y z1 := (mem_filter.mp hz1).2
      have hz2a : G.Adj y z2 := (mem_filter.mp hz2).2
      have hpar1 := hsame hy hz1N hz1a
      have hpar2 := hsame hy hz2N hz2a
      have hmem1 : z1 ∈ G.commonNeighbors a y := by
        rw [mem_commonNeighbors]
        refine ⟨?_, hz1a⟩
        have hadjP : G.Adj (parent z1 hz1N) z1 := (hparent z1 hz1N).2.1
        rw [hpar1] at hadjP
        exact hadjP
      have hmem2 : z2 ∈ G.commonNeighbors a y := by
        rw [mem_commonNeighbors]
        refine ⟨?_, hz2a⟩
        have hadjP : G.Adj (parent z2 hz2N) z2 := (hparent z2 hz2N).2.1
        rw [hpar2] at hadjP
        exact hadjP
      exact hne (commonNeighbors_subsingleton hC hay.ne hmem1 hmem2)
    have hclass {w : V} (hw : G.Adj y w) : w = a ∨ w ∈ nbr2 := by
      have hw_ne : w ≠ s := fun h => by
        have : G.dist s y = 1 := by simpa [h] using dist_eq_one_iff_adj.mpr hw.symm
        have : G.dist s y = 2 := by simpa [N2] using hy
        omega
      have hle := hdist_le w
      have hpos : 0 < G.dist s w := hconn.pos_dist_of_ne (Ne.symm hw_ne)
      rcases (show G.dist s w = 1 ∨ G.dist s w = 2 by omega) with h1 | h2
      · left
        have hwN : w ∈ N1 := by simpa [N1, mem_neighborFinset, dist_eq_one_iff_adj] using h1
        exact ha.2.2 w hwN hw.symm
      · right
        have hwN : w ∈ N2 := by simp [N2, h2]
        exact mem_filter.mpr ⟨hwN, hw⟩
    let H := G.induce (G.neighborSet y)
    have ha_mem : a ∈ G.neighborSet y := by rw [mem_neighborSet]; exact hay.symm
    have hpos : 1 ≤ lambda G y := by
      have hI : H.IsIndepSet
          ({(⟨a, ha_mem⟩ : G.neighborSet y)} : Finset (G.neighborSet y)) := by
        simp [isIndepSet_iff]
      simpa [lambda, alphaIn, H] using IsIndepSet.card_le_indepNum hI
    obtain ⟨t, ht⟩ := H.exists_isNIndepSet_indepNum
    have htc : t.card ≤ 1 := by
      by_contra hgt
      obtain ⟨u, v, hu, hv, huv⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < t.card)
      have huw : G.Adj y u.val := by rw [← mem_neighborSet]; exact u.2
      have hvw : G.Adj y v.val := by rw [← mem_neighborSet]; exact v.2
      have hclass_adj : G.Adj u.val v.val := by
        rcases hclass huw with huA | huN <;> rcases hclass hvw with hvA | hvN
        · exact (huv (Subtype.ext (huA.trans hvA.symm))).elim
        · rw [huA]
          have hvN2 : v.val ∈ N2 := (mem_filter.mp hvN).1
          have hvadj : G.Adj y v.val := (mem_filter.mp hvN).2
          have hadjP : G.Adj (parent v.val hvN2) v.val := (hparent v.val hvN2).2.1
          rw [hsame hy hvN2 hvadj] at hadjP
          exact hadjP
        · rw [hvA]
          have huN2 : u.val ∈ N2 := (mem_filter.mp huN).1
          have huadj : G.Adj y u.val := (mem_filter.mp huN).2
          have hadjP : G.Adj (parent u.val huN2) u.val := (hparent u.val huN2).2.1
          rw [hsame hy huN2 huadj] at hadjP
          exact hadjP.symm
        · have hpair : ({u.val, v.val} : Finset V).card = 2 :=
            (card_pair_eq_two_iff).mpr (fun h => huv (Subtype.ext h))
          have hsub : ({u.val, v.val} : Finset V) ⊆ nbr2 := by
            intro z hz
            simp only [mem_insert, mem_singleton] at hz
            rcases hz with rfl | rfl
            · exact huN
            · exact hvN
          have hle := card_le_card hsub
          rw [hpair] at hle
          omega
      have hHadj : H.Adj u v := induce_adj.mpr hclass_adj
      exact ht.isIndepSet hu hv huv hHadj
    have hle : lambda G y ≤ 1 := by simpa [lambda, alphaIn, H, ht.card_eq] using htc
    omega
  have hlam_a (a : V) (ha : a ∈ N1) :
      lambda G a ≤ 1 + (N2.filter fun y => G.Adj a y).card := by
    let kids := N2.filter fun y => G.Adj a y
    let H := G.induce (G.neighborSet a)
    have hclass {w : V} (hw : G.Adj a w) : w = s ∨ w ∈ N1 ∨ w ∈ kids := by
      by_cases hws : w = s
      · exact Or.inl hws
      · have hle := hdist_le w
        have hpos : 0 < G.dist s w := hconn.pos_dist_of_ne (Ne.symm hws)
        rcases (show G.dist s w = 1 ∨ G.dist s w = 2 by omega) with h1 | h2
        · exact Or.inr (Or.inl (by simpa [N1, mem_neighborFinset, dist_eq_one_iff_adj] using h1))
        · exact Or.inr (Or.inr (mem_filter.mpr ⟨by simp [N2, h2], hw⟩))
    obtain ⟨t, ht⟩ := H.exists_isNIndepSet_indepNum
    let inside := t.filter fun w => w.val ∈ kids
    let outside := t.filter fun w => w.val ∉ kids
    have hsplit : inside.card + outside.card = t.card :=
      card_filter_add_card_filter_not (s := t)
        (fun w : ↥(G.neighborSet a) => w.val ∈ kids)
    have hin : inside.card ≤ kids.card := by
      have hsub : inside.image Subtype.val ⊆ kids := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
        exact (mem_filter.mp hw).2
      rw [← card_image_of_injective _ Subtype.val_injective]
      exact card_le_card hsub
    have hout : outside.card ≤ 1 := by
      by_contra hgt
      obtain ⟨u, v, hu, hv, huv⟩ := Finset.one_lt_card_iff.mp (by omega : 1 < outside.card)
      have huN : u.val = s ∨ u.val ∈ N1 := by
        have huw : G.Adj a u.val := by rw [← mem_neighborSet]; exact u.2
        have hnot : u.val ∉ kids := (mem_filter.mp hu).2
        rcases hclass huw with hs | hN | hk
        · exact Or.inl hs
        · exact Or.inr hN
        · exact (hnot hk).elim
      have hvN : v.val = s ∨ v.val ∈ N1 := by
        have hvw : G.Adj a v.val := by rw [← mem_neighborSet]; exact v.2
        have hnot : v.val ∉ kids := (mem_filter.mp hv).2
        rcases hclass hvw with hs | hN | hk
        · exact Or.inl hs
        · exact Or.inr hN
        · exact (hnot hk).elim
      have hadjuv : G.Adj u.val v.val := by
        rcases huN with huS | hu1 <;> rcases hvN with hvS | hv1
        · exact (huv (Subtype.ext (huS.trans hvS.symm))).elim
        · rw [huS]
          simpa [N1, mem_neighborFinset] using hv1
        · rw [hvS]
          exact (by simpa [N1, mem_neighborFinset] using hu1 : G.Adj s u.val).symm
        · have hmemu : u.val ∈ G.commonNeighbors s a := by
            rw [mem_commonNeighbors]
            exact ⟨by simpa [N1, mem_neighborFinset] using hu1,
              by rw [← mem_neighborSet]; exact u.2⟩
          have hmemv : v.val ∈ G.commonNeighbors s a := by
            rw [mem_commonNeighbors]
            exact ⟨by simpa [N1, mem_neighborFinset] using hv1,
              by rw [← mem_neighborSet]; exact v.2⟩
          have hsa : G.Adj s a := by simpa [N1, mem_neighborFinset] using ha
          exact (huv (Subtype.ext (commonNeighbors_subsingleton hC hsa.ne hmemu hmemv))).elim
      have hu' : u ∈ t := (mem_filter.mp hu).1
      have hv' : v ∈ t := (mem_filter.mp hv).1
      exact ht.isIndepSet hu' hv' huv (induce_adj.mpr hadjuv)
    have hle : t.card ≤ 1 + kids.card := by omega
    simpa [lambda, alphaIn, H, ht.card_eq, kids] using hle
  have hm : edgeCount (G.induce (G.neighborSet s)) = trianglesAt G s :=
    (trianglesAt_eq_neighborEdges (G := G) s).symm
  have hdeg : N1.card = G.degree s := by simp [N1, card_neighborFinset_eq_degree]
  have hlam_s : lambda G s = N1.card - edgeCount (G.induce (G.neighborSet s)) := by
    rw [lambda_eq_degree_sub_trianglesAt hC s, hdeg, hm]
  have hm_le : edgeCount (G.induce (G.neighborSet s)) ≤ N1.card := by
    have hlamAdd := lambda_add_trianglesAt hC s
    rw [← hdeg, ← hm] at hlamAdd
    omega
  let f : V → V := fun y => if hy : y ∈ N2 then parent y hy else s
  have hsumKids : ∑ a ∈ N1, (N2.filter fun y => G.Adj a y).card = N2.card := by
    have hmap : (N2 : Set V).MapsTo f N1 := by
      intro y hy
      have hyN : y ∈ N2 := hy
      rw [show f y = parent y hyN by simp [f, dite_eq_left hyN]]
      exact (hparent y hyN).1
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    refine Finset.sum_congr rfl ?_
    intro a ha
    refine congrArg Finset.card ?_
    ext y
    constructor
    · intro hyA
      have hyN : y ∈ N2 := (mem_filter.mp hyA).1
      have hadj : G.Adj a y := (mem_filter.mp hyA).2
      have hpar : parent y hyN = a := ((hparent y hyN).2.2 a ha hadj).symm
      exact mem_filter.mpr ⟨hyN, by simp [f, dite_eq_left hyN, hpar]⟩
    · intro hyf
      have hyN : y ∈ N2 := (mem_filter.mp hyf).1
      have hf : f y = a := (mem_filter.mp hyf).2
      have hpar : parent y hyN = a := by simpa [f, dite_eq_left hyN] using hf
      exact mem_filter.mpr ⟨hyN, hpar ▸ (hparent y hyN).2.1⟩
  have hsum : neighbourhoodIndependenceSum G =
      lambda G s + ∑ a ∈ N1, lambda G a + ∑ y ∈ N2, lambda G y := by
    have hsout : s ∉ N1 ∪ N2 := by
      simp [mem_union, hsN1, hsN2]
    simp only [neighbourhoodIndependenceSum]
    rw [hcov, sum_insert hsout, sum_union hdisj, add_assoc]
  have hsum2 : ∑ y ∈ N2, lambda G y = N2.card := by
    simpa using (Finset.sum_const_nat fun y hy => hlam_y y hy)
  have hsum1 : ∑ a ∈ N1, lambda G a ≤ N1.card + N2.card := by
    have hle : ∑ a ∈ N1, lambda G a ≤
        ∑ a ∈ N1, (1 + (N2.filter fun y => G.Adj a y).card) :=
      Finset.sum_le_sum fun a ha => hlam_a a ha
    have hsplit : ∑ a ∈ N1, (1 + (N2.filter fun y => G.Adj a y).card) =
        N1.card + ∑ a ∈ N1, (N2.filter fun y => G.Adj a y).card := by
      rw [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)]
      simp
    rw [hsplit, hsumKids] at hle
    exact hle
  have hcard : Fintype.card V = N1.card + N2.card + 1 := by
    have hsout : s ∉ N1 ∪ N2 := by simp [mem_union, hsN1, hsN2]
    rw [← card_univ, hcov, card_insert_of_notMem hsout, card_union_of_disjoint hdisj]
  have hbound : lambda G s + ∑ a ∈ N1, lambda G a + ∑ y ∈ N2, lambda G y ≤
      2 * (Fintype.card V - 1) - edgeCount (G.induce (G.neighborSet s)) := by
    rw [hlam_s, hsum2]
    calc
      N1.card - edgeCount (G.induce (G.neighborSet s)) +
          ∑ a ∈ N1, lambda G a + N2.card
        ≤ N1.card - edgeCount (G.induce (G.neighborSet s)) + (N1.card + N2.card) + N2.card := by
            gcongr
      _ = 2 * (N1.card + N2.card) - edgeCount (G.induce (G.neighborSet s)) := by
            have hmle := hm_le
            omega
      _ = 2 * (Fintype.card V - 1) - edgeCount (G.induce (G.neighborSet s)) := by
            rw [hcard]
            omega
  rw [hsum]
  exact hbound

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

/-- Lemma 5.8(4). Disjoint triangles `T₁ = {u, a, b}` and `T₂ = {v, c, e}` in one
component, at distance `d` between the two vertex sets, give an induced path
`a, u, p₁, …, p_{d-1}, v, c` on `d + 3` vertices. The third vertices `b` and `e`
are the `C₄`s that forbid edges from `a` to `p₁` and from `c` to `p_{d-1}`.
Finiteness makes the induced-path order a maximum. -/
theorem lemma_5_8_path [Fintype V] [DecidableEq V] (hC : StrongC4Free G)
    {u a b v c e : V} {d : ℕ}
    (hT1 : G.Adj u a ∧ G.Adj a b ∧ G.Adj b u)
    (hT2 : G.Adj v c ∧ G.Adj c e ∧ G.Adj e v)
    (hdisj : ({u, a, b} : Set V) ∩ {v, c, e} = ∅)
    (hreach : G.Reachable u v) (hd : G.dist u v = d)
    (hmin : ∀ p q, p ∈ ({u, a, b} : Set V) → q ∈ ({v, c, e} : Set V) → d ≤ G.dist p q) :
    d + 3 ≤ inducedPathOrder G := by
  have hsep {x y : V} (hx : x ∈ ({u, a, b} : Set V)) (hy : y ∈ ({v, c, e} : Set V)) :
      x ≠ y := by
    intro hxy
    simpa [hdisj] using (show x ∈ ({u, a, b} : Set V) ∩ {v, c, e} from ⟨hx, hxy ▸ hy⟩)
  have hu1 : u ∈ ({u, a, b} : Set V) := by simp
  have ha1 : a ∈ ({u, a, b} : Set V) := by simp
  have hb1 : b ∈ ({u, a, b} : Set V) := by simp
  have hv2 : v ∈ ({v, c, e} : Set V) := by simp
  have hc2 : c ∈ ({v, c, e} : Set V) := by simp
  have he2 : e ∈ ({v, c, e} : Set V) := by simp
  have hdpos : 0 < d := by
    have hne : d ≠ 0 := by
      intro hd0
      exact hsep hu1 hv2 ((hreach.dist_eq_zero_iff).1 (hd ▸ hd0))
    omega
  obtain ⟨p, hp, hplen⟩ := hreach.exists_path_of_dist
  rw [hd] at hplen
  have offL {x : V} (hx : x ∈ ({u, a, b} : Set V)) (hxu : x ≠ u) : x ∉ p.support := by
    intro hmem
    obtain ⟨n, hn, hnle⟩ := (Walk.mem_support_iff_exists_getVert).1 hmem
    by_cases hn0 : n = 0
    · rw [hn0, Walk.getVert_zero] at hn
      exact hxu hn.symm
    · by_cases hnd : n = d
      · rw [hnd, ← hplen, Walk.getVert_length] at hn
        exact hsep hx hv2 hn.symm
      · have hpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hle : G.dist x v ≤ d - n := by
          have hdrop : (p.drop n).length = d - n := by simp [Walk.drop_length, hplen]
          simpa [hdrop, hn] using dist_le (p.drop n)
        have hge : d ≤ G.dist x v := hmin x v hx hv2
        omega
  have offR {y : V} (hy : y ∈ ({v, c, e} : Set V)) (hyv : y ≠ v) : y ∉ p.support := by
    intro hmem
    obtain ⟨n, hn, hnle⟩ := (Walk.mem_support_iff_exists_getVert).1 hmem
    have hnle' : n ≤ d := by simpa [hplen] using hnle
    by_cases hn0 : n = 0
    · rw [hn0, Walk.getVert_zero] at hn
      exact hsep hu1 hy hn
    · by_cases hnd : n = d
      · rw [hnd, ← hplen, Walk.getVert_length] at hn
        exact hyv hn.symm
      · have hle : G.dist u y ≤ n := by
          have htake : (p.take n).length = n := by
            rw [Walk.take_length, hplen]
            exact Nat.min_eq_left hnle'
          simpa [htake, hn] using dist_le (p.take n)
        have hge : d ≤ G.dist u y := hmin u y hu1 hy
        omega
  have ha_off : a ∉ p.support := offL ha1 hT1.1.ne.symm
  have hb_off : b ∉ p.support := offL hb1 hT1.2.2.ne
  have hc_off : c ∉ p.support := offR hc2 hT2.1.ne.symm
  have he_off : e ∉ p.support := offR he2 hT2.2.2.ne
  have hfirst : G.Adj u (p.getVert 1) := by
    have hlt : 0 < p.length := by simpa [← hplen] using hdpos
    simpa [Walk.getVert_zero] using p.adj_getVert_succ hlt
  have ha_no {i : ℕ} (hi0 : 0 < i) (hi : i ≤ d) : ¬ G.Adj a (p.getVert i) := by
    intro hadj
    by_cases hi1 : i = 1
    · rw [hi1] at hadj
      have hb_ne : b ≠ p.getVert 1 := by
        intro hbeq
        exact hb_off (hbeq.symm ▸ p.getVert_mem_support 1)
      exact hC (fourCycle_isContained hT1.2.2 hfirst hadj.symm hT1.2.1 hb_ne hT1.1.ne)
    · have hi2 : 2 ≤ i := by omega
      have hle : G.dist a v ≤ (d - i) + 1 := by
        have hdrop : (p.drop i).length = d - i := by simp [Walk.drop_length, hplen]
        have hlenw : ((p.drop i).cons hadj).length = (d - i) + 1 := by
          simp [Walk.length_cons, hdrop]
        simpa [hlenw] using dist_le ((p.drop i).cons hadj)
      have hge : d ≤ G.dist a v := hmin a v ha1 hv2
      have hlt : (d - i) + 1 < d := by omega
      omega
  have hc_no {i : ℕ} (hi : i < d) : ¬ G.Adj c (p.getVert i) := by
    intro hadj
    by_cases hid : i = d - 1
    · have hstep : G.Adj (p.getVert (d - 1)) v := by
        have hlt : d - 1 < p.length := by rw [hplen]; omega
        have hadjp := p.adj_getVert_succ hlt
        have hidx : (d - 1) + 1 = d := by omega
        have hv : p.getVert d = v := by
          rw [← hplen]
          exact Walk.getVert_length p
        simpa [hidx, hv] using hadjp
      rw [hid] at hadj
      have he_ne : e ≠ p.getVert (d - 1) := by
        intro hbeq
        exact he_off (hbeq.symm ▸ p.getVert_mem_support (d - 1))
      exact hC (fourCycle_isContained hT2.2.2 hstep.symm hadj.symm hT2.2.1 he_ne hT2.1.ne)
    · have hle : G.dist u c ≤ i + 1 := by
        have htake : (p.take i).length = i := by
          rw [Walk.take_length, hplen]
          exact Nat.min_eq_left (Nat.le_of_lt hi)
        have hlenw : ((p.take i).concat hadj.symm).length = i + 1 := by
          rw [Walk.length_concat, htake]
        simpa [hlenw] using dist_le ((p.take i).concat hadj.symm)
      have hge : d ≤ G.dist u c := hmin u c hu1 hc2
      have hlt : i + 1 < d := by omega
      omega
  have hac : ¬ G.Adj a c := by
    intro hadj
    by_cases hd1 : d = 1
    · have huv : G.Adj u v := by
        have hidx : p.getVert 1 = v := by
          have hlen1 : (1 : ℕ) = p.length := by rw [hplen, hd1]
          rw [hlen1, Walk.getVert_length]
        simpa [hidx] using hfirst
      exact hC (fourCycle_isContained hadj hT2.1.symm huv.symm hT1.1 (hsep ha1 hv2)
        (hsep hu1 hc2).symm)
    · have hle : G.dist a c ≤ 1 := by simpa using dist_le hadj.toWalk
      have hge : d ≤ G.dist a c := hmin a c ha1 hc2
      have hd2 : 2 ≤ d := by omega
      omega
  have ha_only {y : V} (hy : y ∈ p.support) (hadj : G.Adj a y) : y = u := by
    obtain ⟨i, rfl, hi⟩ := (Walk.mem_support_iff_exists_getVert).1 hy
    have hi0 : i = 0 := by
      by_contra hne
      exact ha_no (Nat.pos_of_ne_zero hne) (by simpa [hplen] using hi) hadj
    simp [hi0, Walk.getVert_zero]
  have hc_only {x : V} (hx : x ∈ p.support) (hadj : G.Adj x c) : x = v := by
    obtain ⟨i, rfl, hi⟩ := (Walk.mem_support_iff_exists_getVert).1 hx
    have hid : i = d := by
      by_contra hne
      exact hc_no (lt_of_le_of_ne (by simpa [hplen] using hi) hne) hadj.symm
    rw [hid, ← hplen, Walk.getVert_length]
  set q : G.Walk a c := (p.cons hT1.1.symm).concat hT2.1
  have hsup : q.support = a :: p.support ++ [c] := by
    simp [q, Walk.support_concat, Walk.support_cons]
  have hmemq {w : V} : w ∈ q.support ↔ w = a ∨ w ∈ p.support ∨ w = c := by
    simp [hsup, List.mem_cons, List.mem_append]
  have hedges : q.edges = (s(a, u) :: p.edges) ++ [s(v, c)] := by
    simp [q, Walk.edges_concat, Walk.edges_cons, List.concat_eq_append]
  have hau_edge : s(a, u) ∈ q.edges := by simp [hedges]
  have hvc_edge : s(v, c) ∈ q.edges := by simp [hedges]
  have hedge_p {x y : V} (h : s(x, y) ∈ p.edges) : s(x, y) ∈ q.edges := by simp [hedges, h]
  have hpchord : p.IsChordless := isChordless_of_length_eq_dist p (hplen.trans hd.symm)
  have hqpath : q.IsPath := by
    have hcmem : c ∉ (p.cons hT1.1.symm).support := by
      intro hmem
      simp [Walk.support_cons] at hmem
      rcases hmem with rfl | hmem
      · exact hsep ha1 hc2 rfl
      · exact hc_off hmem
    exact (hp.cons ha_off (h := hT1.1.symm)).concat hcmem hT2.1
  have hqchord : q.IsChordless := by
    rw [Walk.isChordless_iff_forall_mem_edges]
    intro x y hx hy hxy
    rcases hmemq.mp hx with rfl | hxP | rfl
    · rcases hmemq.mp hy with rfl | hyP | rfl
      · exact (hxy.ne rfl).elim
      · rw [ha_only hyP hxy]
        exact hau_edge
      · exact (hac hxy).elim
    · rcases hmemq.mp hy with rfl | hyP | rfl
      · rw [ha_only hxP hxy.symm, Sym2.eq_swap]
        exact hau_edge
      · exact hedge_p ((Walk.isChordless_iff_forall_mem_edges.mp hpchord) hxP hyP hxy)
      · rw [hc_only hxP hxy]
        exact hvc_edge
    · rcases hmemq.mp hy with rfl | hyP | rfl
      · exact (hac hxy.symm).elim
      · rw [hc_only hyP hxy.symm, Sym2.eq_swap]
        exact hvc_edge
      · exact (hxy.ne rfl).elim
  have hind : q.toSubgraph.IsInduced := Walk.isInduced_toSubgraph.mpr hqchord
  have hcont : pathGraph (q.length + 1) ⊴ G :=
    hqpath.pathGraphIsoToSubgraph.isIndContained.trans hind.isIndContained
  have hlen : q.length + 1 = d + 3 := by
    simp [q, Walk.length_concat, Walk.length_cons, hplen]
  rw [hlen] at hcont
  exact le_csSup (inducedPathOrder_bddAbove G) hcont

/-- In a `P₇`-free graph the distance between disjoint triangles, measured at
closest vertices, is at most three. -/
theorem lemma_5_8_distance_le_three [Fintype V] [DecidableEq V]
    (hC : StrongC4Free G) (hp : IsPkFree G 7)
    {u a b v c e : V} {d : ℕ}
    (hT1 : G.Adj u a ∧ G.Adj a b ∧ G.Adj b u)
    (hT2 : G.Adj v c ∧ G.Adj c e ∧ G.Adj e v)
    (hdisj : ({u, a, b} : Set V) ∩ {v, c, e} = ∅)
    (hreach : G.Reachable u v) (hd : G.dist u v = d)
    (hmin : ∀ p q, p ∈ ({u, a, b} : Set V) → q ∈ ({v, c, e} : Set V) →
      d ≤ G.dist p q) :
    d ≤ 3 := by
  have hpath := lemma_5_8_path hC hT1 hT2 hdisj hreach hd hmin
  have hbound := (isPkFree_iff_inducedPathOrder_lt G 7).mp hp
  omega

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
