module

public import InducedPaths.IsoLoss
public meta import InducedPaths.Graphs
public meta import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Tactic

open Finset SimpleGraph

@[expose] public section
namespace InducedPaths

/-- A triangle-free neighbourhood is independent, so its independence number
is exactly the degree. No strong four-cycle hypothesis is needed. -/
theorem lambda_eq_degree_of_no_triangle {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (ht : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj a c) (v : V) :
    lambda G v = G.degree v := by
  classical
  let H := G.induce (G.neighborSet v)
  have hi : H.IsIndepSet (Finset.univ : Finset (G.neighborSet v)) := by
    intro x hx y hy hne hxy
    exact ht v x.val y.val x.property hxy y.property
  have hlo := hi.card_le_indepNum
  obtain ⟨s, hs⟩ := H.exists_isNIndepSet_indepNum
  have hup := Finset.card_le_univ s
  have he := hs.card_eq
  change H.indepNum = G.degree v
  rw [← G.card_neighborSet_eq_degree v]
  simp only [Finset.card_univ] at hlo
  omega

/-- Total neighbourhood mass of a triangle-free graph is its degree sum. -/
theorem mass_eq_degree_sum_of_no_triangle {V : Type*} [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (ht : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj a c) :
    neighbourhoodIndependenceSum G = ∑ v, G.degree v := by
  unfold neighbourhoodIndependenceSum
  exact Finset.sum_congr rfl (fun v _ => lambda_eq_degree_of_no_triangle ht v)

/-- The canonical Petersen graph has mass thirty, independently of any open
numbered theorem. -/
theorem petersen_mass : neighbourhoodIndependenceSum petersenGraph = 30 := by
  have ht : ∀ a b c, petersenGraph.Adj a b → petersenGraph.Adj b c →
      ¬ petersenGraph.Adj a c := by native_decide
  rw [mass_eq_degree_sum_of_no_triangle ht]
  native_decide

theorem petersen_vertex_card : Fintype.card PetersenVertex = 10 := by native_decide

/-- Canonical small extremal examples, computed without the classification. -/
def h8AdjCode : H8V → H8V → Prop
  | .cycle i, .cycle j => (cycleGraph 6).Adj i j
  | .cycle i, .extra j => i.val = j.val ∨ i.val = j.val + 3
  | .extra j, .cycle i => i.val = j.val ∨ i.val = j.val + 3
  | .extra _, .extra _ => False

instance : DecidableRel h8AdjCode := fun a b => by
  cases a <;> cases b <;> unfold h8AdjCode <;> infer_instance

instance : DecidableRel h8Graph.Adj := fun a b =>
  decidable_of_iff (h8AdjCode a b) (by
    cases a with
    | cycle i =>
      cases b with
      | cycle j =>
        change (cycleGraph 6).Adj i j ↔ _
        simp only [h8Graph, simpleOf, ne_eq, H8V.cycle.injEq,
          or_self, adj_comm]
        exact ⟨fun h => ⟨h.ne, h⟩, And.right⟩
      | extra j =>
        fin_cases i <;> fin_cases j <;> simp [h8AdjCode, h8Graph, simpleOf]
    | extra j =>
      cases b with
      | cycle i => fin_cases i <;> fin_cases j <;> simp [h8AdjCode, h8Graph, simpleOf]
      | extra k => fin_cases j <;> fin_cases k <;> simp [h8AdjCode, h8Graph, simpleOf])

theorem h8_mass : neighbourhoodIndependenceSum h8Graph = 20 := by
  have ht : ∀ a b c, h8Graph.Adj a b → h8Graph.Adj b c →
      ¬ h8Graph.Adj a c := by native_decide
  rw [mass_eq_degree_sum_of_no_triangle ht]
  native_decide

instance : DecidableRel petersenMinus.Adj := fun a b =>
  inferInstanceAs (Decidable (petersenGraph.Adj a.val b.val))

theorem petersenMinus_mass : neighbourhoodIndependenceSum petersenMinus = 24 := by
  have ht : ∀ a b c, petersenMinus.Adj a b → petersenMinus.Adj b c →
      ¬ petersenMinus.Adj a c := by native_decide
  rw [mass_eq_degree_sum_of_no_triangle ht]
  native_decide

theorem cycle5_mass : neighbourhoodIndependenceSum (cycleGraph 5) = 10 := by
  have ht : ∀ a b c : Fin 5, (cycleGraph 5).Adj a b → (cycleGraph 5).Adj b c →
      ¬ (cycleGraph 5).Adj a c := by native_decide
  rw [mass_eq_degree_sum_of_no_triangle ht]
  native_decide

theorem cycle6_mass : neighbourhoodIndependenceSum (cycleGraph 6) = 12 := by
  have ht : ∀ a b c : Fin 6, (cycleGraph 6).Adj a b → (cycleGraph 6).Adj b c →
      ¬ (cycleGraph 6).Adj a c := by native_decide
  rw [mass_eq_degree_sum_of_no_triangle ht]
  native_decide

theorem cycle8_mass : neighbourhoodIndependenceSum (cycleGraph 8) = 16 := by
  have ht : ∀ a b c : Fin 8, (cycleGraph 8).Adj a b → (cycleGraph 8).Adj b c →
      ¬ (cycleGraph 8).Adj a c := by native_decide
  rw [mass_eq_degree_sum_of_no_triangle ht]
  native_decide

/-- The Petersen equality direction transports to every vertex type. -/
theorem mass_eq_three_card_of_iso_petersen {V : Type*} [Fintype V]
    {G : SimpleGraph V} (he : Nonempty (G ≃g petersenGraph)) :
    neighbourhoodIndependenceSum G = 3 * Fintype.card V := by
  obtain ⟨e⟩ := he
  have hc := Fintype.card_congr e.toEquiv
  rw [petersen_vertex_card] at hc
  rw [neighbourhoodIndependenceSum_iso e, petersen_mass, hc]

end InducedPaths
