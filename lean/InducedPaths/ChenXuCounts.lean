module

public import InducedPaths.Graphs
public import Mathlib.Tactic
public meta import InducedPaths.Graphs
public meta import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public meta import Mathlib.Combinatorics.SimpleGraph.Basic

open scoped BigOperators SimpleGraph
open SimpleGraph Finset

@[expose] public section
namespace InducedPaths

set_option maxHeartbeats 2000000

noncomputable local instance (t : ℕ) : DecidableRel (f2Graph t).Adj := Classical.decRel _
noncomputable local instance (t : ℕ) : DecidableRel (f0pGraph t).Adj := Classical.decRel _

lemma f2_card (t : ℕ) : Fintype.card (F2V t) = 5 + 2*t := by
  have h := Fintype.card_congr (F2V.proxyTypeEquiv t)
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

lemma f2_sum (t : ℕ) (f : F2V t → ℕ) :
    ∑ v, f v = (∑ i, f (.cycle i)) + (∑ i, f (.A1 i)) + ∑ i, f (.A3 i) := by
  rw [← Equiv.sum_comp (F2V.proxyTypeEquiv t)]
  simp [Fintype.sum_sum_type, F2V.proxyTypeEquiv, add_assoc]

lemma f2_degree (t : ℕ) (v : F2V t) : (f2Graph t).degree v =
    match v with
    | .cycle i => 2 + if i = 0 ∨ i = 2 then t else 0
    | .A1 _ => 2
    | .A3 _ => 2 := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [f2_sum]
  cases v with
  | cycle i =>
    fin_cases i <;> simp [f2Graph, simpleOf, cycleGraph_adj, Fin.sum_univ_succ] <;> decide
  | A1 i => simp [f2Graph, simpleOf, Fin.sum_univ_succ]
  | A3 i => simp [f2Graph, simpleOf, Fin.sum_univ_succ]


lemma f2_edgeCount (t : ℕ) : edgeCount (f2Graph t) = 5 + 3*t := by
  have h := (f2Graph t).sum_degrees_eq_twice_card_edges
  rw [f2_sum] at h
  simp only [f2_degree] at h
  simp [Fin.sum_univ_succ, edgeCount] at h ⊢
  omega

lemma f0p_card (t : ℕ) : Fintype.card (F0pV t) = 6 + 2*t := by
  have h := Fintype.card_congr (F0pV.proxyTypeEquiv t)
  simp only [Fintype.card_sum, Fintype.card_fin] at h
  omega

lemma f0p_sum (t : ℕ) (f : F0pV t → ℕ) :
    ∑ v, f v = (∑ i, f (.cycle i)) + (∑ i, f (.Y1 i)) + ∑ i, f (.Y4 i) := by
  rw [← Equiv.sum_comp (F0pV.proxyTypeEquiv t)]
  simp [Fintype.sum_sum_type, F0pV.proxyTypeEquiv, add_assoc]

lemma f0p_degree (t : ℕ) (v : F0pV t) : (f0pGraph t).degree v =
    match v with
    | .cycle i => 2 + if i = 0 ∨ i = 3 then t else 0
    | .Y1 _ => 2
    | .Y4 _ => 2 := by
  classical
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  rw [f0p_sum]
  cases v with
  | cycle i =>
    fin_cases i <;> simp [f0pGraph, simpleOf, cycleGraph_adj, Fin.sum_univ_succ] <;> decide
  | Y1 i => simp [f0pGraph, simpleOf, Fin.sum_univ_succ]
  | Y4 i => simp [f0pGraph, simpleOf, Fin.sum_univ_succ]


lemma f0p_edgeCount (t : ℕ) : edgeCount (f0pGraph t) = 6 + 3*t := by
  have h := (f0pGraph t).sum_degrees_eq_twice_card_edges
  rw [f0p_sum] at h
  simp only [f0p_degree] at h
  simp [Fin.sum_univ_succ, edgeCount] at h ⊢
  omega

local instance {W : Type*} (r : W → W → Prop) [DecidableRel r] [DecidableEq W] :
    DecidableRel (simpleOf r).Adj := fun a b => inferInstanceAs (Decidable (a ≠ b ∧ (r a b ∨ r b a)))

instance : DecidableRel f3Graph.Adj := fun a b => by
  unfold f3Graph
  cases a <;> cases b <;> simp only [simpleOf] <;> infer_instance
instance : DecidableRel f4Graph.Adj := fun a b => by
  unfold f4Graph
  cases a <;> cases b <;> simp only [simpleOf] <;> infer_instance
def chenXuCode7 : C7X 1 → C7X 1 → Prop
  | .cycle i, .cycle j => (cycleGraph 7).Adj i j
  | .extra i, .cycle j | .cycle j, .extra i => (i.val = 0 ∧ c7Spoke 0 j)
  | .extra i, .extra j => False
instance : DecidableRel chenXuCode7 := fun a b => by
  cases a <;> cases b <;> unfold chenXuCode7 c7Spoke <;> infer_instance
instance : DecidableRel f7Graph.Adj := fun a b =>
  decidable_of_iff (chenXuCode7 a b) (by
    cases a <;> cases b <;> rename_i i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [chenXuCode7, f7Graph, simpleOf, c7Spoke, Fin.reduceFinMk] <;> decide)

def chenXuCode8 : C7X 2 → C7X 2 → Prop
  | .cycle i, .cycle j => (cycleGraph 7).Adj i j
  | .extra i, .cycle j | .cycle j, .extra i => (i.val = 0 ∧ c7Spoke 0 j) ∨ (i.val = 1 ∧ c7Spoke 1 j)
  | .extra i, .extra j => False
instance : DecidableRel chenXuCode8 := fun a b => by
  cases a <;> cases b <;> unfold chenXuCode8 c7Spoke <;> infer_instance
instance : DecidableRel f8Graph.Adj := fun a b =>
  decidable_of_iff (chenXuCode8 a b) (by
    cases a <;> cases b <;> rename_i i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [chenXuCode8, f8Graph, simpleOf, c7Spoke, Fin.reduceFinMk] <;> decide)

def chenXuCode9 : C7X 3 → C7X 3 → Prop
  | .cycle i, .cycle j => (cycleGraph 7).Adj i j
  | .extra i, .cycle j | .cycle j, .extra i => (i.val = 0 ∧ c7Spoke 0 j) ∨ (i.val = 1 ∧ c7Spoke 1 j)
  | .extra i, .extra j => (i.val = 2 ∧ (j.val = 0 ∨ j.val = 1)) ∨ (j.val = 2 ∧ (i.val = 0 ∨ i.val = 1))
instance : DecidableRel chenXuCode9 := fun a b => by
  cases a <;> cases b <;> unfold chenXuCode9 c7Spoke <;> infer_instance
instance : DecidableRel f9Graph.Adj := fun a b =>
  decidable_of_iff (chenXuCode9 a b) (by
    cases a <;> cases b <;> rename_i i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [chenXuCode9, f9Graph, simpleOf, c7Spoke, Fin.reduceFinMk] <;> decide)

def chenXuCode10 : C7X 2 → C7X 2 → Prop
  | .cycle i, .cycle j => (cycleGraph 7).Adj i j
  | .extra i, .cycle j | .cycle j, .extra i => (i.val = 0 ∧ c7Spoke 0 j) ∨ (i.val = 1 ∧ c7Spoke 4 j)
  | .extra i, .extra j => False
instance : DecidableRel chenXuCode10 := fun a b => by
  cases a <;> cases b <;> unfold chenXuCode10 c7Spoke <;> infer_instance
instance : DecidableRel f10Graph.Adj := fun a b =>
  decidable_of_iff (chenXuCode10 a b) (by
    cases a <;> cases b <;> rename_i i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [chenXuCode10, f10Graph, simpleOf, c7Spoke, Fin.reduceFinMk] <;> decide)

def chenXuCode11 : C7X 3 → C7X 3 → Prop
  | .cycle i, .cycle j => (cycleGraph 7).Adj i j
  | .extra i, .cycle j | .cycle j, .extra i => (i.val = 0 ∧ c7Spoke 0 j) ∨ (i.val = 1 ∧ c7Spoke 1 j) ∨ (i.val = 2 ∧ c7Spoke 4 j)
  | .extra i, .extra j => False
instance : DecidableRel chenXuCode11 := fun a b => by
  cases a <;> cases b <;> unfold chenXuCode11 c7Spoke <;> infer_instance
instance : DecidableRel f11Graph.Adj := fun a b =>
  decidable_of_iff (chenXuCode11 a b) (by
    cases a <;> cases b <;> rename_i i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [chenXuCode11, f11Graph, simpleOf, c7Spoke, Fin.reduceFinMk] <;> decide)

def chenXuCode12 : C7X 4 → C7X 4 → Prop
  | .cycle i, .cycle j => (cycleGraph 7).Adj i j
  | .extra i, .cycle j | .cycle j, .extra i => (i.val = 0 ∧ c7Spoke 0 j) ∨ (i.val = 1 ∧ c7Spoke 1 j) ∨ (i.val = 2 ∧ c7Spoke 4 j)
  | .extra i, .extra j => (i.val = 3 ∧ (j.val = 0 ∨ j.val = 1)) ∨ (j.val = 3 ∧ (i.val = 0 ∨ i.val = 1))
instance : DecidableRel chenXuCode12 := fun a b => by
  cases a <;> cases b <;> unfold chenXuCode12 c7Spoke <;> infer_instance
instance : DecidableRel f12Graph.Adj := fun a b =>
  decidable_of_iff (chenXuCode12 a b) (by
    cases a <;> cases b <;> rename_i i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [chenXuCode12, f12Graph, simpleOf, c7Spoke, Fin.reduceFinMk] <;> decide)

/-- The fixed rows of the Chen–Xu edge table, checked by finite computation. -/
lemma chenXu_fixed_counts :
    (Fintype.card PetersenVertex = 10 ∧ edgeCount petersenGraph = 15) ∧
    (edgeCount (cycleGraph 5) = 5) ∧
    (edgeCount (cycleGraph 6) = 6) ∧
    (edgeCount (cycleGraph 7) = 7) ∧
    (Fintype.card F3V = 8 ∧ edgeCount f3Graph = 10) ∧
    (Fintype.card F4V = 9 ∧ edgeCount f4Graph = 12) ∧
    (Fintype.card (C7X 1) = 8 ∧ edgeCount f7Graph = 9) ∧
    (Fintype.card (C7X 2) = 9 ∧ edgeCount f8Graph = 11) ∧
    (Fintype.card (C7X 3) = 10 ∧ edgeCount f9Graph = 13) ∧
    (edgeCount f10Graph = 11) ∧
    (edgeCount f11Graph = 13) ∧
    (Fintype.card (C7X 4) = 11 ∧ edgeCount f12Graph = 15) := by
  classical
  unfold edgeCount
  native_decide

variable {V : Type*} {G : SimpleGraph V}

private lemma chenXu_iso_counts {W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableRel G.Adj] {H : SimpleGraph W} [DecidableRel H.Adj]
    (e : G ≃g H) : edgeCount G = edgeCount H ∧ Fintype.card V = Fintype.card W := by
  classical
  exact ⟨e.card_edgeFinset_eq, Fintype.card_congr e.toEquiv⟩

/-- Standalone form of Lemma 5.2; imports no statement module. -/
theorem chenXu_counts [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : InChenXuFamily G) :
    (Nonempty (G ≃g petersenGraph) ∧ 2 * edgeCount G = 3 * Fintype.card V) ∨
      (¬ Nonempty (G ≃g petersenGraph) ∧
        2 * edgeCount G ≤ 3 * Fintype.card V - 3) := by
  classical
  obtain ⟨⟨pc, pe⟩, c5, c6, c7, ⟨n3,e3⟩, ⟨n4,e4⟩, ⟨n7,e7⟩,
    ⟨n8,e8⟩, ⟨n9,e9⟩, e10, e11, ⟨n12,e12⟩⟩ := chenXu_fixed_counts
  by_cases hp : Nonempty (G ≃g petersenGraph)
  · obtain ⟨e⟩ := hp
    obtain ⟨he, hn⟩ := chenXu_iso_counts e
    exact Or.inl ⟨⟨e⟩, by omega⟩
  · refine Or.inr ⟨hp, ?_⟩
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · obtain ⟨e⟩ := h
      obtain ⟨he,hn⟩ := chenXu_iso_counts e
      simp only [Fintype.card_fin] at hn
      omega
    · obtain ⟨e⟩ := h
      obtain ⟨he,hn⟩ := chenXu_iso_counts e
      simp only [Fintype.card_fin] at hn
      omega
    · exact (hp h).elim
    · obtain ⟨e⟩ := h
      obtain ⟨he,hn⟩ := chenXu_iso_counts e
      simp only [Fintype.card_fin] at hn
      omega
    · obtain ⟨t, _, ⟨e⟩⟩ := h
      obtain ⟨he,hn⟩ := chenXu_iso_counts e
      rw [f2_edgeCount] at he
      rw [f2_card] at hn
      omega
    · obtain ⟨t, _, ⟨e⟩⟩ := h
      obtain ⟨he,hn⟩ := chenXu_iso_counts e
      rw [f0p_edgeCount] at he
      rw [f0p_card] at hn
      omega
    all_goals
      obtain ⟨e⟩ := h
      obtain ⟨he,hn⟩ := chenXu_iso_counts e
      omega

/-- Weak family bound, convenient for nontruncated deficit arithmetic. -/
theorem chenXu_family_edge_bound [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : InChenXuFamily G) : 2 * edgeCount G ≤ 3 * Fintype.card V := by
  rcases chenXu_counts h with ⟨_, he⟩ | ⟨_, he⟩ <;> omega

/-- Separate the unbounded rows from the bounded fixed family. -/
theorem chenXu_table_refinement [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (h : InChenXuFamily G) :
    (Nonempty (G ≃g petersenGraph) ∧ Fintype.card V = 10 ∧ edgeCount G = 15) ∨
    (∃ t, Nonempty (G ≃g f2Graph t) ∧ Fintype.card V = 5 + 2*t ∧
      edgeCount G = 5 + 3*t) ∨
    (∃ t, Nonempty (G ≃g f0pGraph t) ∧ Fintype.card V = 6 + 2*t ∧
      edgeCount G = 6 + 3*t) ∨
    2 * edgeCount G ≤ 2 * Fintype.card V + 8 := by
  classical
  obtain ⟨⟨pc, pe⟩, c5, c6, c7, ⟨n3,e3⟩, ⟨n4,e4⟩, ⟨n7,e7⟩,
    ⟨n8,e8⟩, ⟨n9,e9⟩, e10, e11, ⟨n12,e12⟩⟩ := chenXu_fixed_counts
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨e⟩ := h
    obtain ⟨he,hn⟩ := chenXu_iso_counts e
    simp only [Fintype.card_fin] at hn
    exact Or.inr (Or.inr (Or.inr (by omega)))
  · obtain ⟨e⟩ := h
    obtain ⟨he,hn⟩ := chenXu_iso_counts e
    simp only [Fintype.card_fin] at hn
    exact Or.inr (Or.inr (Or.inr (by omega)))
  · obtain ⟨e⟩ := h
    obtain ⟨he,hn⟩ := chenXu_iso_counts e
    exact Or.inl ⟨⟨e⟩, by omega, by omega⟩
  · obtain ⟨e⟩ := h
    obtain ⟨he,hn⟩ := chenXu_iso_counts e
    simp only [Fintype.card_fin] at hn
    exact Or.inr (Or.inr (Or.inr (by omega)))
  · obtain ⟨t, _, ⟨e⟩⟩ := h
    obtain ⟨he,hn⟩ := chenXu_iso_counts e
    exact Or.inr (Or.inl ⟨t, ⟨e⟩, hn.trans (f2_card t), he.trans (f2_edgeCount t)⟩)
  · obtain ⟨t, _, ⟨e⟩⟩ := h
    obtain ⟨he,hn⟩ := chenXu_iso_counts e
    exact Or.inr (Or.inr (Or.inl ⟨t, ⟨e⟩, hn.trans (f0p_card t), he.trans (f0p_edgeCount t)⟩))
  all_goals
    obtain ⟨e⟩ := h
    obtain ⟨he,hn⟩ := chenXu_iso_counts e
    exact Or.inr (Or.inr (Or.inr (by omega)))

end InducedPaths
