/- Local second-layer obstructions for the hexagon branch of Theorem 3.6. -/
module

public import InducedPaths.C6Trace
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public meta import Mathlib.Data.Fintype.Pi

open scoped SimpleGraph
open SimpleGraph

set_option maxHeartbeats 400000
set_option synthInstance.maxSize 256

@[expose] public section
namespace InducedPaths

/-- A third-layer edge would extend around the hexagon to an induced `P₆`.
The hypotheses are stated solely as nonadjacencies, so the lemma does not
require a developed distance-to-set API. -/
theorem hexTrace_no_third_layer {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    {a x z : V} (ha : ∀ i, c i ≠ a) (hx : ∀ i, ¬ G.Adj x (c i))
    (hz : ∀ i, ¬ G.Adj z (c i)) (hax : G.Adj a x) (hxz : G.Adj x z)
    (hza : ¬ G.Adj z a) (hmeet : ∃ i, G.Adj a (c i)) : False := by
  classical
  obtain ⟨i, hi⟩ := hexTrace_antipodal hC hp c ha hmeet
  have hac : G.Adj a (c i) := (hi i).2 (Or.inl rfl)
  have hnext : ∀ j : Fin 6, (cycleGraph 6).Adj j (j + 1) := by native_decide
  have hxc : ∀ j, x ≠ c j := fun j h => by
    apply hx (j + 1)
    rw [h]
    exact (c.map_rel_iff).2 (hnext j)
  have hzc : ∀ j, z ≠ c j := fun j h => by
    apply hz (j + 1)
    rw [h]
    exact (c.map_rel_iff).2 (hnext j)
  have hzx : z ≠ x := hxz.ne.symm
  have hxa : x ≠ a := hax.ne.symm
  have hza' : z ≠ a := by
    intro h
    exact hz i (h ▸ hac)
  have hfin : ∀ i : Fin 6,
      (cycleGraph 6).Adj i (i + 1) ∧
      (cycleGraph 6).Adj (i + 1) (i + 2) ∧
      ¬ (cycleGraph 6).Adj i (i + 2) ∧
      i ≠ i + 1 ∧ i ≠ i + 2 ∧ i + 1 ≠ i + 2 ∧
      ¬ (i + 1 = i ∨ i + 1 = i + 3) ∧
      ¬ (i + 2 = i ∨ i + 2 = i + 3) := by native_decide
  obtain ⟨h01, h12, hn02, hn01, hn02', hn12, hn1, hn2⟩ := hfin i
  have hnac1 : ¬ G.Adj a (c (i + 1)) := fun h => hn1 ((hi _).1 h)
  have hnac2 : ¬ G.Adj a (c (i + 2)) := fun h => hn2 ((hi _).1 h)
  have hxc' : ∀ j, c j ≠ x := fun j => (hxc j).symm
  have hzc' : ∀ j, c j ≠ z := fun j => (hzc j).symm
  have hc01 := (c.map_rel_iff).2 h01
  have hc12 := (c.map_rel_iff).2 h12
  have hnc02 : ¬ G.Adj (c i) (c (i + 2)) := fun h => hn02 ((c.map_rel_iff).1 h)
  let f : Fin 6 → V := ![z, x, a, c i, c (i + 1), c (i + 2)]
  apply hp
  refine ⟨{ toEmbedding := ⟨f, ?_⟩, map_rel_iff' := ?_ }⟩
  · intro u v heq
    fin_cases u <;> fin_cases v <;>
      simp only [f, Matrix.cons_val_zero, Matrix.cons_val_succ] at heq ⊢ <;>
      first | rfl | exact False.elim (hzc _ heq) | exact False.elim (hzc' _ heq)
            | exact False.elim (hxc _ heq) | exact False.elim (hxc' _ heq)
            | exact False.elim (ha _ heq) | exact False.elim (ha _ heq.symm)
            | exact False.elim (hzx heq) | exact False.elim (hzx heq.symm)
            | exact False.elim (hxa heq) | exact False.elim (hxa heq.symm)
            | exact False.elim (hza' heq) | exact False.elim (hza' heq.symm)
            | exact False.elim (hn01 (c.injective heq))
            | exact False.elim (hn01 (c.injective heq).symm)
            | exact False.elim (hn02' (c.injective heq))
            | exact False.elim (hn02' (c.injective heq).symm)
            | exact False.elim (hn12 (c.injective heq))
            | exact False.elim (hn12 (c.injective heq).symm)
  · intro u v
    change G.Adj (f u) (f v) ↔ (pathGraph 6).Adj u v
    rw [pathGraph_adj]
    fin_cases u <;> fin_cases v
    · change G.Adj (z) (z) ↔ (0 + 1 = 0 ∨ 0 + 1 = 0)
      exact iff_of_false ((G.loopless.irrefl _)) (by decide)
    · change G.Adj (z) (x) ↔ (0 + 1 = 1 ∨ 1 + 1 = 0)
      exact iff_of_true hxz.symm (by decide)
    · change G.Adj (z) (a) ↔ (0 + 1 = 2 ∨ 2 + 1 = 0)
      exact iff_of_false (hza) (by decide)
    · change G.Adj (z) (c i) ↔ (0 + 1 = 3 ∨ 3 + 1 = 0)
      exact iff_of_false (hz (i)) (by decide)
    · change G.Adj (z) (c (i + 1)) ↔ (0 + 1 = 4 ∨ 4 + 1 = 0)
      exact iff_of_false (hz (i + 1)) (by decide)
    · change G.Adj (z) (c (i + 2)) ↔ (0 + 1 = 5 ∨ 5 + 1 = 0)
      exact iff_of_false (hz (i + 2)) (by decide)
    · change G.Adj (x) (z) ↔ (1 + 1 = 0 ∨ 0 + 1 = 1)
      exact iff_of_true hxz (by decide)
    · change G.Adj (x) (x) ↔ (1 + 1 = 1 ∨ 1 + 1 = 1)
      exact iff_of_false ((G.loopless.irrefl _)) (by decide)
    · change G.Adj (x) (a) ↔ (1 + 1 = 2 ∨ 2 + 1 = 1)
      exact iff_of_true hax.symm (by decide)
    · change G.Adj (x) (c i) ↔ (1 + 1 = 3 ∨ 3 + 1 = 1)
      exact iff_of_false (hx (i)) (by decide)
    · change G.Adj (x) (c (i + 1)) ↔ (1 + 1 = 4 ∨ 4 + 1 = 1)
      exact iff_of_false (hx (i + 1)) (by decide)
    · change G.Adj (x) (c (i + 2)) ↔ (1 + 1 = 5 ∨ 5 + 1 = 1)
      exact iff_of_false (hx (i + 2)) (by decide)
    · change G.Adj (a) (z) ↔ (2 + 1 = 0 ∨ 0 + 1 = 2)
      exact iff_of_false ((fun h => hza h.symm)) (by decide)
    · change G.Adj (a) (x) ↔ (2 + 1 = 1 ∨ 1 + 1 = 2)
      exact iff_of_true hax (by decide)
    · change G.Adj (a) (a) ↔ (2 + 1 = 2 ∨ 2 + 1 = 2)
      exact iff_of_false ((G.loopless.irrefl _)) (by decide)
    · change G.Adj (a) (c i) ↔ (2 + 1 = 3 ∨ 3 + 1 = 2)
      exact iff_of_true hac (by decide)
    · change G.Adj (a) (c (i + 1)) ↔ (2 + 1 = 4 ∨ 4 + 1 = 2)
      exact iff_of_false (hnac1) (by decide)
    · change G.Adj (a) (c (i + 2)) ↔ (2 + 1 = 5 ∨ 5 + 1 = 2)
      exact iff_of_false (hnac2) (by decide)
    · change G.Adj (c i) (z) ↔ (3 + 1 = 0 ∨ 0 + 1 = 3)
      exact iff_of_false ((fun h => hz _ h.symm)) (by decide)
    · change G.Adj (c i) (x) ↔ (3 + 1 = 1 ∨ 1 + 1 = 3)
      exact iff_of_false ((fun h => hx _ h.symm)) (by decide)
    · change G.Adj (c i) (a) ↔ (3 + 1 = 2 ∨ 2 + 1 = 3)
      exact iff_of_true hac.symm (by decide)
    · change G.Adj (c i) (c i) ↔ (3 + 1 = 3 ∨ 3 + 1 = 3)
      exact iff_of_false ((G.loopless.irrefl _)) (by decide)
    · change G.Adj (c i) (c (i + 1)) ↔ (3 + 1 = 4 ∨ 4 + 1 = 3)
      exact iff_of_true hc01 (by decide)
    · change G.Adj (c i) (c (i + 2)) ↔ (3 + 1 = 5 ∨ 5 + 1 = 3)
      exact iff_of_false (hnc02) (by decide)
    · change G.Adj (c (i + 1)) (z) ↔ (4 + 1 = 0 ∨ 0 + 1 = 4)
      exact iff_of_false ((fun h => hz _ h.symm)) (by decide)
    · change G.Adj (c (i + 1)) (x) ↔ (4 + 1 = 1 ∨ 1 + 1 = 4)
      exact iff_of_false ((fun h => hx _ h.symm)) (by decide)
    · change G.Adj (c (i + 1)) (a) ↔ (4 + 1 = 2 ∨ 2 + 1 = 4)
      exact iff_of_false ((fun h => hnac1 h.symm)) (by decide)
    · change G.Adj (c (i + 1)) (c i) ↔ (4 + 1 = 3 ∨ 3 + 1 = 4)
      exact iff_of_true hc01.symm (by decide)
    · change G.Adj (c (i + 1)) (c (i + 1)) ↔ (4 + 1 = 4 ∨ 4 + 1 = 4)
      exact iff_of_false ((G.loopless.irrefl _)) (by decide)
    · change G.Adj (c (i + 1)) (c (i + 2)) ↔ (4 + 1 = 5 ∨ 5 + 1 = 4)
      exact iff_of_true hc12 (by decide)
    · change G.Adj (c (i + 2)) (z) ↔ (5 + 1 = 0 ∨ 0 + 1 = 5)
      exact iff_of_false ((fun h => hz _ h.symm)) (by decide)
    · change G.Adj (c (i + 2)) (x) ↔ (5 + 1 = 1 ∨ 1 + 1 = 5)
      exact iff_of_false ((fun h => hx _ h.symm)) (by decide)
    · change G.Adj (c (i + 2)) (a) ↔ (5 + 1 = 2 ∨ 2 + 1 = 5)
      exact iff_of_false ((fun h => hnac2 h.symm)) (by decide)
    · change G.Adj (c (i + 2)) (c i) ↔ (5 + 1 = 3 ∨ 3 + 1 = 5)
      exact iff_of_false ((fun h => hnc02 h.symm)) (by decide)
    · change G.Adj (c (i + 2)) (c (i + 1)) ↔ (5 + 1 = 4 ∨ 4 + 1 = 5)
      exact iff_of_true hc12.symm (by decide)
    · change G.Adj (c (i + 2)) (c (i + 2)) ↔ (5 + 1 = 5 ∨ 5 + 1 = 5)
      exact iff_of_false ((G.loopless.irrefl _)) (by decide)

private theorem hexTrace_contacts : ∀ i j : Fin 6,
      (∀ k, ¬ ((k = i ∨ k = i + 3) ∧ (k = j ∨ k = j + 3))) →
      ∃ p q r : Fin 6, (p = i ∨ p = i + 3) ∧ (r = j ∨ r = j + 3) ∧
        ¬ (q = i ∨ q = i + 3) ∧ ¬ (r = i ∨ r = i + 3) ∧
        ¬ (p = j ∨ p = j + 3) ∧ ¬ (q = j ∨ q = j + 3) ∧
        (cycleGraph 6).Adj p q ∧ (cycleGraph 6).Adj q r ∧
        ¬ (cycleGraph 6).Adj p r ∧ p ≠ q ∧ p ≠ r ∧ q ≠ r := by native_decide

/-- A vertex with empty cycle trace which meets one first-layer vertex meets
all first-layer vertices (the second-layer rule of Theorem 3.6). -/
theorem hexTrace_second_layer_complete {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    {a b x : V} (ha : ∀ i, c i ≠ a) (hb : ∀ i, c i ≠ b)
    (hma : ∃ i, G.Adj a (c i)) (hmb : ∃ i, G.Adj b (c i))
    (hx : ∀ i, ¬ G.Adj x (c i)) (hxa : G.Adj x a) : G.Adj x b := by
  classical
  by_contra hxb
  have hab : a ≠ b := fun h => hxb (h ▸ hxa)
  obtain ⟨i, hi⟩ := hexTrace_antipodal hC hp c ha hma
  obtain ⟨j, hj⟩ := hexTrace_antipodal hC hp c hb hmb
  have hdis : ∀ k, ¬ ((k = i ∨ k = i + 3) ∧ (k = j ∨ k = j + 3)) := by
    intro k hk
    exact hexTrace_disjoint hC hp c ha hb hab k ⟨(hi k).2 hk.1, (hj k).2 hk.2⟩
  obtain ⟨p, q, r, hpi, hrj, hnqi, hnri, hnpj, hnqj, hpq, hqr, hnpr, hpq', hpr', hqr'⟩ := hexTrace_contacts i j hdis
  have hap := (hi p).2 hpi
  have hbr := (hj r).2 hrj
  have hnaq : ¬ G.Adj a (c q) := fun h => hnqi ((hi q).1 h)
  have hnar : ¬ G.Adj a (c r) := fun h => hnri ((hi r).1 h)
  have hnbp : ¬ G.Adj b (c p) := fun h => hnpj ((hj p).1 h)
  have hnbq : ¬ G.Adj b (c q) := fun h => hnqj ((hj q).1 h)
  have hnab := hexTrace_nonadjacent hC hp c ha hb hma hmb
  have hcpq := (c.map_rel_iff).2 hpq
  have hcqr := (c.map_rel_iff).2 hqr
  have hncpr : ¬ G.Adj (c p) (c r) := fun h => hnpr ((c.map_rel_iff).1 h)
  have hnext : ∀ k : Fin 6, (cycleGraph 6).Adj k (k + 1) := by native_decide
  have hxc : ∀ k, x ≠ c k := by
    intro k h
    exact hx (k + 1) (h ▸ (c.map_rel_iff).2 (hnext k))
  have hxb' : x ≠ b := by
    intro h
    exact hx r (h ▸ hbr)
  let f : Fin 6 → V := ![x, a, c p, c q, c r, b]
  apply hp
  refine ⟨{ toEmbedding := ⟨f, ?_⟩, map_rel_iff' := ?_ }⟩
  · intro u v heq
    fin_cases u <;> fin_cases v <;> simp only [f] at heq ⊢ <;>
      first | rfl
            | exact False.elim (hxa.ne heq) | exact False.elim (hxa.ne heq.symm)
            | exact False.elim (hxb' heq) | exact False.elim (hxb' heq.symm)
            | exact False.elim (hab heq) | exact False.elim (hab heq.symm)
            | exact False.elim (hxc _ heq) | exact False.elim (hxc _ heq.symm)
            | exact False.elim (ha _ heq) | exact False.elim (ha _ heq.symm)
            | exact False.elim (hb _ heq) | exact False.elim (hb _ heq.symm)
            | exact False.elim (hpq' (c.injective heq))
            | exact False.elim (hpq' (c.injective heq).symm)
            | exact False.elim (hpr' (c.injective heq))
            | exact False.elim (hpr' (c.injective heq).symm)
            | exact False.elim (hqr' (c.injective heq))
            | exact False.elim (hqr' (c.injective heq).symm)
  · intro u v
    change G.Adj (f u) (f v) ↔ (pathGraph 6).Adj u v
    rw [pathGraph_adj]
    fin_cases u <;> fin_cases v
    · change G.Adj (x) (x) ↔ (0 + 1 = 0 ∨ 0 + 1 = 0)
      exact iff_of_false (G.loopless.irrefl _) (by decide)
    · change G.Adj (x) (a) ↔ (0 + 1 = 1 ∨ 1 + 1 = 0)
      exact iff_of_true (hxa) (by decide)
    · change G.Adj (x) (c p) ↔ (0 + 1 = 2 ∨ 2 + 1 = 0)
      exact iff_of_false (hx p) (by decide)
    · change G.Adj (x) (c q) ↔ (0 + 1 = 3 ∨ 3 + 1 = 0)
      exact iff_of_false (hx q) (by decide)
    · change G.Adj (x) (c r) ↔ (0 + 1 = 4 ∨ 4 + 1 = 0)
      exact iff_of_false (hx r) (by decide)
    · change G.Adj (x) (b) ↔ (0 + 1 = 5 ∨ 5 + 1 = 0)
      exact iff_of_false (hxb) (by decide)
    · change G.Adj (a) (x) ↔ (1 + 1 = 0 ∨ 0 + 1 = 1)
      exact iff_of_true (hxa).symm (by decide)
    · change G.Adj (a) (a) ↔ (1 + 1 = 1 ∨ 1 + 1 = 1)
      exact iff_of_false (G.loopless.irrefl _) (by decide)
    · change G.Adj (a) (c p) ↔ (1 + 1 = 2 ∨ 2 + 1 = 1)
      exact iff_of_true (hap) (by decide)
    · change G.Adj (a) (c q) ↔ (1 + 1 = 3 ∨ 3 + 1 = 1)
      exact iff_of_false (hnaq) (by decide)
    · change G.Adj (a) (c r) ↔ (1 + 1 = 4 ∨ 4 + 1 = 1)
      exact iff_of_false (hnar) (by decide)
    · change G.Adj (a) (b) ↔ (1 + 1 = 5 ∨ 5 + 1 = 1)
      exact iff_of_false (hnab) (by decide)
    · change G.Adj (c p) (x) ↔ (2 + 1 = 0 ∨ 0 + 1 = 2)
      exact iff_of_false (fun h => (hx p) h.symm) (by decide)
    · change G.Adj (c p) (a) ↔ (2 + 1 = 1 ∨ 1 + 1 = 2)
      exact iff_of_true (hap).symm (by decide)
    · change G.Adj (c p) (c p) ↔ (2 + 1 = 2 ∨ 2 + 1 = 2)
      exact iff_of_false (G.loopless.irrefl _) (by decide)
    · change G.Adj (c p) (c q) ↔ (2 + 1 = 3 ∨ 3 + 1 = 2)
      exact iff_of_true (hcpq) (by decide)
    · change G.Adj (c p) (c r) ↔ (2 + 1 = 4 ∨ 4 + 1 = 2)
      exact iff_of_false (hncpr) (by decide)
    · change G.Adj (c p) (b) ↔ (2 + 1 = 5 ∨ 5 + 1 = 2)
      exact iff_of_false ((fun h => hnbp h.symm)) (by decide)
    · change G.Adj (c q) (x) ↔ (3 + 1 = 0 ∨ 0 + 1 = 3)
      exact iff_of_false (fun h => (hx q) h.symm) (by decide)
    · change G.Adj (c q) (a) ↔ (3 + 1 = 1 ∨ 1 + 1 = 3)
      exact iff_of_false (fun h => (hnaq) h.symm) (by decide)
    · change G.Adj (c q) (c p) ↔ (3 + 1 = 2 ∨ 2 + 1 = 3)
      exact iff_of_true (hcpq).symm (by decide)
    · change G.Adj (c q) (c q) ↔ (3 + 1 = 3 ∨ 3 + 1 = 3)
      exact iff_of_false (G.loopless.irrefl _) (by decide)
    · change G.Adj (c q) (c r) ↔ (3 + 1 = 4 ∨ 4 + 1 = 3)
      exact iff_of_true (hcqr) (by decide)
    · change G.Adj (c q) (b) ↔ (3 + 1 = 5 ∨ 5 + 1 = 3)
      exact iff_of_false ((fun h => hnbq h.symm)) (by decide)
    · change G.Adj (c r) (x) ↔ (4 + 1 = 0 ∨ 0 + 1 = 4)
      exact iff_of_false (fun h => (hx r) h.symm) (by decide)
    · change G.Adj (c r) (a) ↔ (4 + 1 = 1 ∨ 1 + 1 = 4)
      exact iff_of_false (fun h => (hnar) h.symm) (by decide)
    · change G.Adj (c r) (c p) ↔ (4 + 1 = 2 ∨ 2 + 1 = 4)
      exact iff_of_false (fun h => (hncpr) h.symm) (by decide)
    · change G.Adj (c r) (c q) ↔ (4 + 1 = 3 ∨ 3 + 1 = 4)
      exact iff_of_true (hcqr).symm (by decide)
    · change G.Adj (c r) (c r) ↔ (4 + 1 = 4 ∨ 4 + 1 = 4)
      exact iff_of_false (G.loopless.irrefl _) (by decide)
    · change G.Adj (c r) (b) ↔ (4 + 1 = 5 ∨ 5 + 1 = 4)
      exact iff_of_true (hbr.symm) (by decide)
    · change G.Adj (b) (x) ↔ (5 + 1 = 0 ∨ 0 + 1 = 5)
      exact iff_of_false (fun h => (hxb) h.symm) (by decide)
    · change G.Adj (b) (a) ↔ (5 + 1 = 1 ∨ 1 + 1 = 5)
      exact iff_of_false (fun h => (hnab) h.symm) (by decide)
    · change G.Adj (b) (c p) ↔ (5 + 1 = 2 ∨ 2 + 1 = 5)
      exact iff_of_false (fun h => ((fun h => hnbp h.symm)) h.symm) (by decide)
    · change G.Adj (b) (c q) ↔ (5 + 1 = 3 ∨ 3 + 1 = 5)
      exact iff_of_false (fun h => ((fun h => hnbq h.symm)) h.symm) (by decide)
    · change G.Adj (b) (c r) ↔ (5 + 1 = 4 ∨ 4 + 1 = 5)
      exact iff_of_true (hbr.symm).symm (by decide)
    · change G.Adj (b) (b) ↔ (5 + 1 = 5 ∨ 5 + 1 = 5)
      exact iff_of_false (G.loopless.irrefl _) (by decide)

/-- A connected graph containing an induced hexagon has no third layer. -/
theorem hexTrace_two_layers {V : Type*} {G : SimpleGraph V}
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (v : V) :
    (∃ i, v = c i) ∨ (∃ i, G.Adj v (c i)) ∨
      ∃ a, (∀ i, c i ≠ a) ∧ (∃ i, G.Adj a (c i)) ∧ G.Adj v a := by
  classical
  let P : V → Prop := fun v =>
    (∃ i, v = c i) ∨ (∃ i, G.Adj v (c i)) ∨
      ∃ a, (∀ i, c i ≠ a) ∧ (∃ i, G.Adj a (c i)) ∧ G.Adj v a
  have hstep : ∀ x z, G.Adj x z → P x → P z := by
    intro x z hxz hpx
    by_cases hzc : ∃ i, z = c i
    · exact Or.inl hzc
    by_cases hzm : ∃ i, G.Adj z (c i)
    · exact Or.inr (Or.inl hzm)
    have hz : ∀ i, ¬ G.Adj z (c i) := by simpa using hzm
    rcases hpx with ⟨i, rfl⟩ | ⟨i, hxi⟩ | ⟨a, ha, hma, hxa⟩
    · exact False.elim (hz i hxz.symm)
    · have hxo : ∀ j, c j ≠ x := by
        intro j hj
        exact hz j (hj ▸ hxz.symm)
      exact Or.inr (Or.inr ⟨x, hxo, ⟨i, hxi⟩, hxz.symm⟩)
    · by_cases hza : G.Adj z a
      · exact Or.inr (Or.inr ⟨a, ha, hma, hza⟩)
      · by_cases hxm : ∃ i, G.Adj x (c i)
        · have hxo : ∀ j, c j ≠ x := by
            intro j hj
            exact hz j (hj ▸ hxz.symm)
          exact Or.inr (Or.inr ⟨x, hxo, hxm, hxz.symm⟩)
        · have hx : ∀ i, ¬ G.Adj x (c i) := by simpa using hxm
          exact False.elim (hexTrace_no_third_layer hC hp c ha hx hz hxa.symm hxz hza hma)
  have hwalk : ∀ {u w : V}, G.Walk u w → P u → P w := by
    intro u w p
    induction p with
    | nil => exact id
    | @cons u t w hut p ih =>
        intro hu
        exact ih (hstep u t hut hu)
  exact (hconn (c 0) v).elim fun p => hwalk p (Or.inl ⟨0, rfl⟩)

/-- With two first-layer vertices there is at most one vertex in the
second layer, since all second-layer vertices are common neighbours. -/
theorem hexTrace_second_layer_subsingleton {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    {a b : V} (ha : ∀ i, c i ≠ a) (hb : ∀ i, c i ≠ b) (hab : a ≠ b)
    (hma : ∃ i, G.Adj a (c i)) (hmb : ∃ i, G.Adj b (c i)) :
    {x | (∀ i, ¬ G.Adj x (c i)) ∧ ∃ d,
      (∀ i, c i ≠ d) ∧ (∃ i, G.Adj d (c i)) ∧ G.Adj x d}.Subsingleton := by
  intro x hx y hy
  obtain ⟨hx, d, hd, hmd, hxd⟩ := hx
  obtain ⟨hy, e, he, hme, hye⟩ := hy
  have hxa := hexTrace_second_layer_complete hC hp c hd ha hmd hma hx hxd
  have hxb := hexTrace_second_layer_complete hC hp c hd hb hmd hmb hx hxd
  have hya := hexTrace_second_layer_complete hC hp c he ha hme hma hy hye
  have hyb := hexTrace_second_layer_complete hC hp c he hb hme hmb hy hye
  exact commonNeighbors_subsingleton hC hab ⟨hxa.symm, hxb.symm⟩ ⟨hya.symm, hyb.symm⟩

end InducedPaths
