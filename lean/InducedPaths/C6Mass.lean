module

public import InducedPaths.C6Trace
public import InducedPaths.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators

open scoped SimpleGraph
open Finset SimpleGraph

@[expose] public section
namespace InducedPaths

variable {V : Type*} {G : SimpleGraph V}

/-- The vertices outside the designated induced hexagon. -/
def hexOutside (c : cycleGraph 6 ↪g G) : Set V := (Set.range c)ᶜ

private theorem hexOutside_ne (c : cycleGraph 6 ↪g G) {w : V}
    (hw : w ∈ hexOutside c) : ∀ i, c i ≠ w := by
  intro i h
  exact hw ⟨i, h⟩

private theorem hexOutside_meet (c : cycleGraph 6 ↪g G)
    (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i)) {w : V}
    (hw : w ∈ hexOutside c) : ∃ i, G.Adj w (c i) := by
  obtain ⟨i, hi⟩ := hdom w
  exact ⟨i, hi.resolve_left (hexOutside_ne c hw i).symm⟩

/-- A dominating induced hexagon gives an exact partition of the vertices. -/
noncomputable def hexPartition (c : cycleGraph 6 ↪g G) :
    Fin 6 ⊕ hexOutside c ≃ V :=
  Equiv.ofBijective (Sum.elim c Subtype.val) (by
    constructor
    · intro a b h
      cases a with
      | inl i =>
        cases b with
        | inl j => exact congrArg Sum.inl (c.injective h)
        | inr w => exact False.elim (w.property ⟨i, h⟩)
      | inr w =>
        cases b with
        | inl j => exact False.elim (w.property ⟨j, h.symm⟩)
        | inr z => exact congrArg Sum.inr (Subtype.ext h)
    · intro v
      by_cases hv : v ∈ Set.range c
      · obtain ⟨i, rfl⟩ := hv; exact ⟨Sum.inl i, rfl⟩
      · exact ⟨Sum.inr ⟨v, hv⟩, rfl⟩)

/-- Every triangle is excluded by the antipodal, disjoint external traces. -/
theorem hexDominating_no_triangle (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G)
    (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i)) :
    ∀ a b d, G.Adj a b → G.Adj b d → ¬ G.Adj a d := by
  classical
  have hn (w z : hexOutside c) : ¬ G.Adj w.val z.val :=
    hexTrace_nonadjacent hC hp c (hexOutside_ne c w.property)
      (hexOutside_ne c z.property) (hexOutside_meet c hdom w.property)
      (hexOutside_meet c hdom z.property)
  have hc : ∀ i j k : Fin 6, (cycleGraph 6).Adj i j →
      (cycleGraph 6).Adj j k → ¬ (cycleGraph 6).Adj i k := by native_decide
  have he (w : hexOutside c) (i j : Fin 6) (hij : (cycleGraph 6).Adj i j) :
      ¬ (G.Adj w.val (c i) ∧ G.Adj w.val (c j)) := by
    obtain ⟨k, hk⟩ := hexTrace_antipodal hC hp c (hexOutside_ne c w.property)
      (hexOutside_meet c hdom w.property)
    have hf : ∀ i j k : Fin 6, (cycleGraph 6).Adj i j →
        ¬ ((i = k ∨ i = k + 3) ∧ (j = k ∨ j = k + 3)) := by native_decide
    rintro ⟨hi, hj⟩
    exact hf i j k hij ⟨(hk i).1 hi, (hk j).1 hj⟩
  intro a b d hab hbd had
  obtain ⟨a, rfl⟩ := (hexPartition c).surjective a
  obtain ⟨b, rfl⟩ := (hexPartition c).surjective b
  obtain ⟨d, rfl⟩ := (hexPartition c).surjective d
  cases a with
  | inl i =>
    cases b with
    | inl j =>
      cases d with
      | inl k =>
        exact hc i j k ((c.map_rel_iff).1 hab)
          ((c.map_rel_iff).1 hbd) ((c.map_rel_iff).1 had)
      | inr w => exact he w i j ((c.map_rel_iff).1 hab) ⟨had.symm, hbd.symm⟩
    | inr w =>
      cases d with
      | inl k => exact he w i k ((c.map_rel_iff).1 had) ⟨hab.symm, hbd⟩
      | inr z => exact hn w z hbd
  | inr w =>
    cases b with
    | inl j =>
      cases d with
      | inl k => exact he w j k ((c.map_rel_iff).1 hbd) ⟨hab, had⟩
      | inr z => exact hn w z had
    | inr z => exact hn w z hab

/-- Neighbourhood independence equals degree for a dominating induced hexagon. -/
theorem hexDominating_lambda_eq_degree [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G)
    (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i)) (v : V) :
    lambda G v = G.degree v := by
  classical
  have he : (G.induce (G.neighborSet v)).edgeFinset = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    have ha := adj_out_of_mem (G.induce (G.neighborSet v)) e he
    exact hexDominating_no_triangle hC hp c hdom v e.out.1.val e.out.2.val
      e.out.1.property ha e.out.2.property
  have ht : trianglesAt G v = 0 := by
    rw [trianglesAt_eq_neighborEdges, edgeCount, he, Finset.card_empty]
  have := lambda_add_trianglesAt hC v
  omega

private theorem hexPartition_sum [Fintype V] (c : cycleGraph 6 ↪g G)
    [Fintype (hexOutside c)] (f : V → ℕ) :
    (∑ v, f v) = (∑ i : Fin 6, f (c i)) + ∑ w : hexOutside c, f w.val := by
  classical
  rw [← Fintype.sum_equiv (hexPartition c) (fun x => f (hexPartition c x)) f
    (fun _ => rfl), Fintype.sum_sum_type]
  rfl

/-- The exact mass in the dominating-hexagon case of Lemma 3.4. -/
theorem hexDominating_mass [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i)) :
    neighbourhoodIndependenceSum G = 12 + 4 * Nat.card (hexOutside c) ∧
      neighbourhoodIndependenceSum G < 3 * Fintype.card V := by
  classical
  have hn (w z : hexOutside c) : ¬ G.Adj w.val z.val :=
    hexTrace_nonadjacent hC hp c (hexOutside_ne c w.property)
      (hexOutside_ne c z.property) (hexOutside_meet c hdom w.property)
      (hexOutside_meet c hdom z.property)
  have htrace (w : hexOutside c) :
      (∑ i : Fin 6, if G.Adj w.val (c i) then 1 else 0) = 2 := by
    obtain ⟨k, hk⟩ := hexTrace_antipodal hC hp c (hexOutside_ne c w.property)
      (hexOutside_meet c hdom w.property)
    simp_rw [hk]
    have hf : ∀ k : Fin 6, (∑ i : Fin 6, if i = k ∨ i = k + 3 then 1 else 0) = 2 := by
      native_decide
    exact hf k
  have hdeg (v : V) : G.degree v =
      (∑ i : Fin 6, if G.Adj v (c i) then 1 else 0) +
        ∑ w : hexOutside c, if G.Adj v w.val then 1 else 0 := by
    have hv : G.degree v = ∑ x : V, if G.Adj v x then 1 else 0 := by
      simpa only [Finset.sum_boole, Nat.cast_id, ← G.neighborFinset_eq_filter] using
        (G.card_neighborFinset_eq_degree v).symm
    rw [hv, hexPartition_sum c]
  have hwdeg (w : hexOutside c) : G.degree w.val = 2 := by
    rw [hdeg, htrace]
    simp [hn]
  have hcycle (i : Fin 6) :
      (∑ j : Fin 6, if G.Adj (c i) (c j) then 1 else 0) = 2 := by
    simp_rw [c.map_rel_iff]
    have hf : ∀ i : Fin 6,
        (∑ j : Fin 6, if (cycleGraph 6).Adj i j then 1 else 0) = 2 := by native_decide
    exact hf i
  have hcycled : (∑ i : Fin 6, G.degree (c i)) =
      12 + 2 * Fintype.card (hexOutside c) := by
    simp_rw [hdeg, hcycle]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    have ht : ∀ w : hexOutside c,
        (∑ i : Fin 6, if G.Adj (c i) w.val then 1 else 0) = 2 := by
      intro w
      simpa only [G.adj_comm] using htrace w
    simp_rw [ht]
    simp [Nat.mul_comm]
  have hmass : neighbourhoodIndependenceSum G =
      12 + 4 * Nat.card (hexOutside c) := by
    unfold neighbourhoodIndependenceSum
    simp_rw [hexDominating_lambda_eq_degree hC hp c hdom]
    rw [hexPartition_sum c, hcycled]
    simp_rw [hwdeg]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Nat.card_eq_fintype_card]
    omega
  have hcard : Fintype.card V = 6 + Nat.card (hexOutside c) := by
    have ht := Fintype.card_congr (hexPartition c)
    simpa only [Fintype.card_sum, Fintype.card_fin, Nat.card_eq_fintype_card] using ht.symm
  have hle : Nat.card (hexOutside c) ≤ 3 :=
    hexTrace_card_le_three hC hp c (hexOutside c)
      (fun _ hw => hexOutside_ne c hw) (fun _ hw => hexOutside_meet c hdom hw)
  exact ⟨hmass, by omega⟩

end InducedPaths
