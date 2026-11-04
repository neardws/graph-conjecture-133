/-
Statements of the preprint, in dependency order. Proofs are `sorry` except where noted.
Paper numbers refer to `paper/main.tex` at `c6d3eb76`.
-/
module

public import InducedPaths.Basic
public import InducedPaths.Certificate
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
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
  -- missing: `λ` adds across the two blocks of `G - v`
  sorry

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
  -- missing: any two cross edges between disjoint triangles span a `C₄`
  sorry

/-- Lemma 5.8(4). `d` is the distance between two disjoint triangles, realised by `u` and `v`.
`x` and `z` lie on those triangles and are not the attachment vertices. The induced path
`x, u, …, v, z` has order `d + 3`. Part (3), that the induced subgraph on the two triangles
and a shortest path is exactly those edges, is the reason this path is induced. -/
theorem lemma_5_8_path (hC : StrongC4Free G) {u v x z : V} {d : ℕ}
    (hdist : G.dist u v = d) (hx : x ≠ u ∧ G.Adj x u) (hz : z ≠ v ∧ G.Adj v z)
    (hmin : ∀ u' v', G.Adj x u' → G.Adj u' x → G.Adj z v' → G.Adj v' z → d ≤ G.dist u' v') :
    d + 3 ≤ inducedPathOrder G := by
  -- missing: the induced subgraph on the two triangles and a shortest path is that path
  sorry

/-- Lemma 5.9. A closed replay of the four seeds does not prove this lemma: the
embedding of those seeds and the comparison of mask-loss with `L(v)` stay open. -/
theorem lemma_5_9 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 7) (htri : 2 ≤ triangleCount G) :
    ∃ v, deletionLoss G v ≤ 3 := by
  -- missing: the four seeds embed, and every searched graph has a vertex of deletion loss at most 3
  sorry

/-- The induced-path order of the Petersen graph. -/
theorem petersen_inducedPathOrder : inducedPathOrder petersenGraph = 5 := by
  -- missing: Petersen has an induced `P₅` and no induced `P₆`
  sorry

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
