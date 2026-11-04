module

public import InducedPaths.ChenXuCounts
public meta import InducedPaths.ChenXuCounts
public import Mathlib.Tactic
public import Mathlib.Data.Fintype.Powerset
public meta import Mathlib.Data.Fintype.Powerset

open scoped BigOperators SimpleGraph
open SimpleGraph Finset

@[expose] public section
namespace InducedPaths

set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 100
set_option maxRecDepth 4096
set_option synthInstance.maxSize 10000

/-- Distinct attachment vertices have disjoint open neighbourhoods in the core. -/
def ChenXuAttachmentDisjoint {V : Type*} (Q : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∀ z, ¬ (Q.Adj x z ∧ Q.Adj y z)

/-- Finite packing and edge slack, with strict slack outside Petersen. -/
def ChenXuAttachmentBounds {V : Type*} [Fintype V] (Q : SimpleGraph V)
    [DecidableRel Q.Adj] (petersen : Bool) : Prop :=
  ∀ A : Finset V, ChenXuAttachmentDisjoint Q A →
    A.card ≤ (3 * Fintype.card V - 2 * edgeCount Q) + 2 ∧
    ∀ u ∈ A, ∀ w ∈ A, Q.Adj u w →
      A.card + min (Q.degree u) (Q.degree w) ≤
        (3 * Fintype.card V - 2 * edgeCount Q) + (if petersen then 5 else 4)

lemma chenXu_fixed_attachment_bounds :
    ChenXuAttachmentBounds petersenGraph true ∧
    ChenXuAttachmentBounds (cycleGraph 5) false ∧
    ChenXuAttachmentBounds (cycleGraph 6) false ∧
    ChenXuAttachmentBounds (cycleGraph 7) false ∧
    ChenXuAttachmentBounds f3Graph false ∧
    ChenXuAttachmentBounds f4Graph false ∧
    ChenXuAttachmentBounds f7Graph false ∧
    ChenXuAttachmentBounds f8Graph false ∧
    ChenXuAttachmentBounds f9Graph false ∧
    ChenXuAttachmentBounds f10Graph false ∧
    ChenXuAttachmentBounds f11Graph false ∧
    ChenXuAttachmentBounds f12Graph false ∧
    ChenXuAttachmentBounds (completeGraph (Fin 1)) false ∧
    ChenXuAttachmentBounds k2Graph false := by
  unfold ChenXuAttachmentBounds ChenXuAttachmentDisjoint edgeCount
  repeat' constructor
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte]
    native_decide

lemma chenXu_attachment_card_le_four {V : Type*} [DecidableEq V]
    {Q : SimpleGraph V} [DecidableRel Q.Adj] (A : Finset V)
    (hA : ChenXuAttachmentDisjoint Q A) (r s : V)
    (hcover : ∀ x, x = r ∨ x = s ∨ Q.Adj x r ∨ Q.Adj x s) : A.card ≤ 4 := by
  have hr : (A.filter (fun x => Q.Adj x r)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hx, hxr⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy, hyr⟩ := Finset.mem_filter.mp hy
    by_contra hne
    exact hA x hx y hy hne r ⟨hxr, hyr⟩
  have hs : (A.filter (fun x => Q.Adj x s)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    obtain ⟨hx, hxs⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy, hys⟩ := Finset.mem_filter.mp hy
    by_contra hne
    exact hA x hx y hy hne s ⟨hxs, hys⟩
  have hsub : A ⊆ {r,s} ∪ A.filter (fun x => Q.Adj x r) ∪ A.filter (fun x => Q.Adj x s) := by
    intro x hx
    rcases hcover x with h | h | h | h <;> simp_all
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le ({r,s} ∪ A.filter (fun x => Q.Adj x r))
    (A.filter (fun x => Q.Adj x s))
  have hv := Finset.card_union_le ({r,s} : Finset V) (A.filter (fun x => Q.Adj x r))
  have hp : ({r,s} : Finset V).card ≤ 2 := by
    calc
      _ ≤ ({r} : Finset V).card + ({s} : Finset V).card := by
        simpa using Finset.card_union_le ({r} : Finset V) ({s} : Finset V)
      _ = 2 := by simp
  omega

noncomputable local instance (t : ℕ) : DecidableRel (f2Graph t).Adj := Classical.decRel _
noncomputable local instance (t : ℕ) : DecidableRel (f0pGraph t).Adj := Classical.decRel _

lemma f2_attachment_card (t : ℕ) (A : Finset (F2V t))
    (hA : ChenXuAttachmentDisjoint (f2Graph t) A) : A.card ≤ 4 := by
  apply chenXu_attachment_card_le_four A hA (.cycle 0) (.cycle 2)
  intro x
  cases x with
  | cycle i => fin_cases i <;> norm_num [f2Graph, simpleOf, cycleGraph_adj] <;> decide
  | A1 i => exact Or.inr (Or.inr (Or.inl (by simp [f2Graph, simpleOf])))
  | A3 i => exact Or.inr (Or.inr (Or.inr (by simp [f2Graph, simpleOf])))

lemma f0p_attachment_card (t : ℕ) (A : Finset (F0pV t))
    (hA : ChenXuAttachmentDisjoint (f0pGraph t) A) : A.card ≤ 4 := by
  apply chenXu_attachment_card_le_four A hA (.cycle 0) (.cycle 3)
  intro x
  cases x with
  | cycle i => fin_cases i <;> norm_num [f0pGraph, simpleOf, cycleGraph_adj] <;> decide
  | Y1 i => exact Or.inr (Or.inr (Or.inl (by simp [f0pGraph, simpleOf])))
  | Y4 i => exact Or.inr (Or.inr (Or.inr (by simp [f0pGraph, simpleOf])))

lemma f2_edge_min_degree (t : ℕ) (u w : F2V t) (h : (f2Graph t).Adj u w) :
    min ((f2Graph t).degree u) ((f2Graph t).degree w) ≤ 2 := by
  rw [f2_degree, f2_degree]
  cases u <;> cases w <;> simp_all [f2Graph, simpleOf]
  rename_i i j
  fin_cases i <;> fin_cases j <;> norm_num [cycleGraph_adj] at * <;> exfalso <;> revert h <;> decide

lemma f0p_edge_min_degree (t : ℕ) (u w : F0pV t) (h : (f0pGraph t).Adj u w) :
    min ((f0pGraph t).degree u) ((f0pGraph t).degree w) ≤ 2 := by
  rw [f0p_degree, f0p_degree]
  cases u <;> cases w <;> simp_all [f0pGraph, simpleOf]
  rename_i i j
  fin_cases i <;> fin_cases j <;> norm_num [cycleGraph_adj] at * <;> exfalso <;> revert h <;> decide

lemma f2_attachment_bounds (t : ℕ) : ChenXuAttachmentBounds (f2Graph t) false := by
  intro A hA
  have hc := f2_attachment_card t A hA
  have hn := f2_card t
  have he := f2_edgeCount t
  constructor
  · omega
  · intro u hu w hw huw
    have hd := f2_edge_min_degree t u w huw
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega

lemma f0p_attachment_bounds (t : ℕ) : ChenXuAttachmentBounds (f0pGraph t) false := by
  intro A hA
  have hc := f0p_attachment_card t A hA
  have hn := f0p_card t
  have he := f0p_edgeCount t
  constructor
  · omega
  · intro u hu w hw huw
    have hd := f0p_edge_min_degree t u w huw
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V]
    {Q : SimpleGraph V} {H : SimpleGraph W} [DecidableRel Q.Adj] [DecidableRel H.Adj]

lemma chenXu_attachment_bounds_iso (e : Q ≃g H) (b : Bool)
    (h : ChenXuAttachmentBounds H b) : ChenXuAttachmentBounds Q b := by
  classical
  intro A hA
  let B := A.map e.toEquiv.toEmbedding
  have hB : ChenXuAttachmentDisjoint H B := by
    intro x hx y hy hne z hz
    obtain ⟨x, hxA, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y, hyA, rfl⟩ := Finset.mem_map.mp hy
    have hxy : x ≠ y := fun he => hne (congrArg e he)
    apply hA x hxA y hyA hxy (e.symm z)
    constructor
    · exact e.map_rel_iff.mp (by simpa using hz.1)
    · exact e.map_rel_iff.mp (by simpa using hz.2)
  obtain ⟨hc, hd⟩ := h B hB
  have hn := Fintype.card_congr e.toEquiv
  have he : edgeCount Q = edgeCount H := e.card_edgeFinset_eq
  have hb : B.card = A.card := Finset.card_map _
  constructor
  · omega
  · intro u hu w hw huw
    have huB : e u ∈ B := Finset.mem_map.mpr ⟨u, hu, rfl⟩
    have hwB : e w ∈ B := Finset.mem_map.mpr ⟨w, hw, rfl⟩
    have hh := hd (e u) huB (e w) hwB (e.map_rel_iff.mpr huw)
    have hdu := e.degree_eq u
    have hdw := e.degree_eq w
    omega

/-- The possible stripped cores, including the two complete small cores. -/
def ChenXuSmallCore {V : Type*} (Q : SimpleGraph V) : Prop :=
  Nonempty (Q ≃g completeGraph (Fin 1)) ∨ Nonempty (Q ≃g k2Graph) ∨ InChenXuFamily Q

lemma chenXu_core_attachment_cases (hQ : ChenXuSmallCore Q) :
    (Nonempty (Q ≃g petersenGraph) ∧ ChenXuAttachmentBounds Q true) ∨
      ChenXuAttachmentBounds Q false := by
  classical
  obtain ⟨hp,h5,h6,h7,h3,h4,hf7,h8,h9,h10,h11,h12,h1,h2⟩ := chenXu_fixed_attachment_bounds
  rcases hQ with h | h | h
  · obtain ⟨e⟩ := h
    exact Or.inr (chenXu_attachment_bounds_iso e false h1)
  · obtain ⟨e⟩ := h
    exact Or.inr (chenXu_attachment_bounds_iso e false h2)
  · rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    · obtain ⟨e⟩ := h
      exact Or.inr (chenXu_attachment_bounds_iso e false h6)
    · obtain ⟨e⟩ := h
      exact Or.inr (chenXu_attachment_bounds_iso e false h5)
    · obtain ⟨e⟩ := h
      exact Or.inl ⟨⟨e⟩, chenXu_attachment_bounds_iso e true hp⟩
    · obtain ⟨e⟩ := h
      exact Or.inr (chenXu_attachment_bounds_iso e false h7)
    · obtain ⟨t, _, ⟨e⟩⟩ := h
      exact Or.inr (chenXu_attachment_bounds_iso e false (f2_attachment_bounds t))
    · obtain ⟨t, _, ⟨e⟩⟩ := h
      exact Or.inr (chenXu_attachment_bounds_iso e false (f0p_attachment_bounds t))
    · obtain ⟨e⟩ := h
      exact Or.inr (chenXu_attachment_bounds_iso e false h3)
    · obtain ⟨e⟩ := h
      exact Or.inr (chenXu_attachment_bounds_iso e false h4)
    · obtain ⟨e⟩ := h
      exact Or.inr (chenXu_attachment_bounds_iso e false hf7)
    · obtain ⟨e⟩ := h
      exact Or.inr (chenXu_attachment_bounds_iso e false h8)
    · obtain ⟨e⟩ := h
      exact Or.inr (chenXu_attachment_bounds_iso e false h9)
    · obtain ⟨e⟩ := h
      exact Or.inr (chenXu_attachment_bounds_iso e false h10)
    · obtain ⟨e⟩ := h
      exact Or.inr (chenXu_attachment_bounds_iso e false h11)
    · obtain ⟨e⟩ := h
      exact Or.inr (chenXu_attachment_bounds_iso e false h12)

 theorem chenXu_core_attachment_card (hQ : ChenXuSmallCore Q) (A : Finset V)
    (hA : ChenXuAttachmentDisjoint Q A) :
    A.card ≤ (3 * Fintype.card V - 2 * edgeCount Q) + 2 := by
  rcases chenXu_core_attachment_cases hQ with ⟨_,h⟩ | h <;> exact (h A hA).1

 theorem chenXu_core_attachment_edge (hQ : ChenXuSmallCore Q) (A : Finset V)
    (hA : ChenXuAttachmentDisjoint Q A) {u w : V} (hu : u ∈ A) (hw : w ∈ A)
    (huw : Q.Adj u w) :
    A.card + min (Q.degree u) (Q.degree w) ≤
      (3 * Fintype.card V - 2 * edgeCount Q) + 5 := by
  rcases chenXu_core_attachment_cases hQ with ⟨_,h⟩ | h
  · exact (h A hA).2 u hu w hw huw
  · have hh := (h A hA).2 u hu w hw huw
    simp only [Bool.false_eq_true, ↓reduceIte] at hh
    omega

 theorem chenXu_core_attachment_edge_eq_petersen (hQ : ChenXuSmallCore Q) (A : Finset V)
    (hA : ChenXuAttachmentDisjoint Q A) {u w : V} (hu : u ∈ A) (hw : w ∈ A)
    (huw : Q.Adj u w)
    (heq : A.card + min (Q.degree u) (Q.degree w) =
      (3 * Fintype.card V - 2 * edgeCount Q) + 5) : Nonempty (Q ≃g petersenGraph) := by
  rcases chenXu_core_attachment_cases hQ with ⟨hp,_⟩ | h
  · exact hp
  · have hh := (h A hA).2 u hu w hw huw
    simp only [Bool.false_eq_true, ↓reduceIte] at hh
    omega

end InducedPaths
