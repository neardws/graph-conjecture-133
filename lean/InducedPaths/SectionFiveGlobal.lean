/- Cycle-free helpers for the strict case of Theorem 5.10.
The finite certificates below quantify over the actual Petersen graph; they do
not assume any of the numbered Section Five theorems. -/
module
public import InducedPaths.Basic
public import InducedPaths.PetersenPaths
public meta import InducedPaths.PetersenPaths
public import InducedPaths.ChordalMass
public import InducedPaths.CanonicalMass
public import InducedPaths.Graphs
public meta import Mathlib.Data.Fintype.Powerset
public meta import InducedPaths.Graphs
public meta import InducedPaths.Basic
set_option synthInstance.maxSize 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open Finset SimpleGraph
@[expose] public section
namespace InducedPaths
namespace SectionFiveGlobal

/-- The thirteen-vertex equality configuration in paper 1110–1120. The extra
vertices are respectively the deleted triangle vertex and the two leaves. -/
def petersenTriangleExtension (u w a b : PetersenVertex) :
    SimpleGraph (PetersenVertex ⊕ Fin 3) :=
  simpleOf fun
    | .inl p, .inl q => petersenGraph.Adj p q
    | .inr i, .inl p => if i = 0 then p = u ∨ p = w else
        if i = 1 then p = a else p = b
    | .inl p, .inr i => if i = 0 then p = u ∨ p = w else
        if i = 1 then p = a else p = b
    | .inr i, .inr j => i = 0 ∧ (j = 1 ∨ j = 2) ∨ j = 0 ∧ (i = 1 ∨ i = 2)

instance (u w a b : PetersenVertex) :
    DecidableRel (petersenTriangleExtension u w a b).Adj := by
  intro x y
  cases x <;> cases y <;> unfold petersenTriangleExtension simpleOf <;> dsimp <;> infer_instance

def nonedgeSeven (a b c d e : PetersenVertex) : Fin 7 → PetersenVertex ⊕ Fin 3 :=
  ![.inr 1, .inl a, .inl c, .inl d, .inl e, .inl b, .inr 2]

def edgeSeven (a b c d e : PetersenVertex) : Fin 7 → PetersenVertex ⊕ Fin 3 :=
  ![.inr 0, .inr 1, .inl a, .inl b, .inl c, .inl d, .inl e]

/-- Complete finite Petersen endgame. The two alternatives are exactly the
nonadjacent-support and adjacent-support witnesses of paper 1114 and 1118.
This searches only three Petersen vertices, never arbitrary seven-tuples. -/
theorem petersen_extension_certificate : ∀ u w a b : PetersenVertex,
    petersenGraph.Adj u w → a ≠ b →
    a ≠ u → a ≠ w → b ≠ u → b ≠ w →
    ¬ petersenGraph.Adj a u → ¬ petersenGraph.Adj a w →
    ¬ petersenGraph.Adj b u → ¬ petersenGraph.Adj b w →
    ∃ c d e : PetersenVertex,
      PathCertificate (petersenTriangleExtension u w a b) (nonedgeSeven a b c d e) ∨
      PathCertificate (petersenTriangleExtension u w a b) (edgeSeven a b c d e) := by
  native_decide

/-- The final equality configuration is impossible in an ambient P7-free graph.
An embedding is an honest structural input, not a disguised mass conclusion. -/
theorem petersen_extension_not_P7free {W : Type*} {H : SimpleGraph W}
    (hp : IsPkFree H 7) {u w a b : PetersenVertex}
    (huw : petersenGraph.Adj u w) (hab : a ≠ b)
    (hau : a ≠ u) (haw : a ≠ w) (hbu : b ≠ u) (hbw : b ≠ w)
    (hanu : ¬ petersenGraph.Adj a u) (hanw : ¬ petersenGraph.Adj a w)
    (hbnu : ¬ petersenGraph.Adj b u) (hbnw : ¬ petersenGraph.Adj b w)
    (f : petersenTriangleExtension u w a b ↪g H) : False := by
  obtain ⟨c, d, e, hc | hc⟩ := petersen_extension_certificate u w a b huw hab
    hau haw hbu hbw hanu hanw hbnu hbnw
  · exact hp (hc.isIndContained.trans f.isIndContained)
  · exact hp (hc.isIndContained.trans f.isIndContained)

/-- Paper 1110: the equality slack and the two disjoint outside-neighbour
sets collapse all remaining arithmetic. No truncated subtraction is used. -/
theorem petersen_equality_arithmetic {c cu cw d t : ℕ}
    (hdu : d ≤ 4 + cu) (hdw : d ≤ 4 + cw)
    (hdisj : cu + cw ≤ c) (hslack : d = 4 + c)
    (ht : t + 2 = d + c) : c = 0 ∧ cu = 0 ∧ cw = 0 ∧ d = 4 ∧ t = 2 := by
  omega

/-- Arithmetic form of paper 1097: the improved attachment inequality
excludes equality when either remaining triangle vertex is outside the core. -/
theorem outside_core_strict {S n e eH eQ d h t a c eta : ℕ}
    (hS : S + 3 = 2 * e) (he : e = eH + d)
    (hstrip : eH = eQ + t) (hdef : 2 * eQ + eta = 3 * h)
    (hn : n = h + t + 1) (ht : t + a = d + c)
    (hd : d ≤ c + 3) (ha : a ≤ eta + 2) : S < 3 * n := by
  omega

/-- Arithmetic form of paper 1101: equality forces both degree and core slack
bounds to be tight. -/
theorem inside_core_equality_slack {S n e eH eQ d h t a c eta k : ℕ}
    (hS : S + 3 = 2 * e) (he : e = eH + d)
    (hstrip : eH = eQ + t) (hdef : 2 * eQ + eta = 3 * h)
    (hn : n = h + t + 1) (ht : t + a = d + c)
    (hd : d ≤ 1 + c + k) (ha : a + k ≤ eta + 5)
    (heq : S = 3 * n) : d = 1 + c + k ∧ a + k = eta + 5 := by
  omega

/-- Paper 1089: neighbours of a new vertex in an induced Petersen graph
must form a clique, since every Petersen nonedge has a common neighbour. -/
theorem petersen_extension_neighbors_clique {W : Type*} {H : SimpleGraph W}
    (hC : StrongC4Free H) (f : petersenGraph ↪g H) (v : W)
    (hv : ∀ p, v ≠ f p) {a b : PetersenVertex} (hab : a ≠ b)
    (ha : H.Adj v (f a)) (hb : H.Adj v (f b)) : petersenGraph.Adj a b := by
  by_contra hn
  obtain ⟨c, hac, hbc⟩ := petersen_common_neighbor a b hab hn
  have hac' : H.Adj (f a) (f c) := f.map_rel_iff.mpr hac
  have hbc' : H.Adj (f b) (f c) := f.map_rel_iff.mpr hbc
  exact hC (fourCycle_isContained ha hac' hbc'.symm hb.symm (hv c)
    (fun he => hab (f.injective he)))

/-- The component partition expressed as a genuine equivalence of finite
vertex types. This is also the bookkeeping map for componentwise induction. -/
noncomputable def componentEquiv {W : Type*} (H : SimpleGraph W) :
    (Σ C : H.ConnectedComponent, C.supp) ≃ W where
  toFun x := x.2.val
  invFun x := ⟨H.connectedComponentMk x, ⟨x, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨C, x, hx⟩
    have he : H.connectedComponentMk x = C := hx
    subst C
    rfl
  right_inv _ := rfl

noncomputable local instance {W : Type*} [Fintype W] (H : SimpleGraph W) :
    Fintype H.ConnectedComponent := Fintype.ofFinite _
noncomputable local instance {W : Type*} [Fintype W] (H : SimpleGraph W)
    (C : H.ConnectedComponent) : Fintype C.supp := by classical exact Subtype.fintype _

/-- Any vertex weight sums componentwise. -/
theorem sum_components {W : Type*} [Fintype W] (H : SimpleGraph W) (f : W → ℕ) :
    ∑ x, f x = ∑ C : H.ConnectedComponent, ∑ x : C.supp, f x := by
  classical
  rw [← Equiv.sum_comp (componentEquiv H), Fintype.sum_sigma]
  rfl

/-- Componentwise vertex-cardinality additivity. -/
theorem card_components {W : Type*} [Fintype W] (H : SimpleGraph W) :
    Fintype.card W = ∑ C : H.ConnectedComponent, Fintype.card C.supp := by
  classical
  simpa using sum_components H (fun _ => 1)

/-- The neighbourhood-independence mass is additive on connected components. -/
theorem mass_components {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] : neighbourhoodIndependenceSum H =
      ∑ C : H.ConnectedComponent, neighbourhoodIndependenceSum (H.induce C.supp) := by
  classical
  rw [neighbourhoodIndependenceSum, sum_components H]
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro x _
  exact (lambda_induce_eq x.property (fun y hy =>
    C.mem_supp_of_adj_mem_supp x.property hy)).symm

/-- Summing the induction hypotheses works even when a deletion disconnects
the graph; a single strict component is enough for strictness of the total. -/
theorem mass_lt_of_component_bounds {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hle : ∀ C : H.ConnectedComponent,
      neighbourhoodIndependenceSum (H.induce C.supp) ≤ 3 * Fintype.card C.supp)
    (hlt : ∃ C : H.ConnectedComponent,
      neighbourhoodIndependenceSum (H.induce C.supp) < 3 * Fintype.card C.supp) :
    neighbourhoodIndependenceSum H < 3 * Fintype.card W := by
  classical
  rw [mass_components H, card_components H, Finset.mul_sum]
  obtain ⟨C, hC⟩ := hlt
  exact Finset.sum_lt_sum (fun D _ => hle D) ⟨C, mem_univ C, hC⟩

/-- Non-strict componentwise version, also valid for the empty graph. -/
theorem mass_le_of_component_bounds {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hle : ∀ C : H.ConnectedComponent,
      neighbourhoodIndependenceSum (H.induce C.supp) ≤ 3 * Fintype.card C.supp) :
    neighbourhoodIndependenceSum H ≤ 3 * Fintype.card W := by
  classical
  rw [mass_components H, card_components H, Finset.mul_sum]
  exact Finset.sum_le_sum (fun D _ => hle D)

/-- A two-vertex deletion removing three edges and no triangles costs exactly
six units of mass. This statement separates the structural deletion witness
from the mass identity and applies even if the remainder is disconnected. -/
theorem two_vertex_mass_identity {W Z : Type*} [Fintype W] [DecidableEq W]
    [Fintype Z] [DecidableEq Z] {H : SimpleGraph W} {K : SimpleGraph Z}
    [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hH : StrongC4Free H) (hK : StrongC4Free K)
    (he : edgeCount K + 3 = edgeCount H) (ht : triangleCount K = triangleCount H) :
    neighbourhoodIndependenceSum K + 6 = neighbourhoodIndependenceSum H := by
  have hsH := strongC4Free_S_identity hH
  have hsK := strongC4Free_S_identity hK
  have hnonneg := three_mul_triangleCount_le_two_edge hK
  omega

/-- The final arithmetic contradiction of paper 1091, after componentwise
strictness on the two-vertex deletion has been established. -/
theorem two_vertex_deletion_strict {S S' n n' : ℕ}
    (hmass : S' + 6 = S) (hcard : n' + 2 = n) (hsmall : S' < 3 * n') :
    S < 3 * n := by omega

/-- Deleting an adjacent vertex decreases degree by exactly one. -/
theorem degree_delete_adjacent {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {u w : W} (huw : H.Adj u w) :
    (H.induce {u}ᶜ).degree ⟨w, by simpa using huw.ne.symm⟩ + 1 = H.degree w := by
  classical
  let w' : ({u}ᶜ : Set W) := ⟨w, by simpa using huw.ne.symm⟩
  have hm := H.map_neighborFinset_induce w'
  have hsets : H.neighborFinset w ∩ ({u}ᶜ : Set W).toFinset =
      (H.neighborFinset w).erase u := by
    ext x
    simp [and_comm]
  rw [hsets] at hm
  have hc := congrArg Finset.card hm
  rw [Finset.card_map, Finset.card_erase_of_mem (by simpa using huw.symm)] at hc
  have hpos : 0 < H.degree w := by
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_pos.mpr ⟨u, by simpa using huw.symm⟩
  change (H.induce {u}ᶜ).degree w' + 1 = H.degree w
  rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hc
  omega

/-- The structural edge-count step for deleting adjacent degree-two vertices.
The remainder is represented by two successive induced deletions; no
connectivity hypothesis is imposed. -/
theorem adjacent_degree_two_edge_count {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] {u w : W} (huw : H.Adj u w)
    (hdu : H.degree u = 2) (hdw : H.degree w = 2) :
    edgeCount ((H.induce {u}ᶜ).induce
      {⟨w, by simpa using huw.ne.symm⟩}ᶜ) + 3 = edgeCount H := by
  classical
  have h1 := edgeCount_induce_compl_add (G := H) u
  have h2 := edgeCount_induce_compl_add (G := H.induce {u}ᶜ)
    (⟨w, by simpa using huw.ne.symm⟩ : ({u}ᶜ : Set W))
  have hd := degree_delete_adjacent huw
  omega

/-- The structural triangle-count step of paper 1091: large deletion loss
at a degree-two endpoint precludes its triangle; the second endpoint has
degree one after deletion and therefore belongs to no triangle either. -/
theorem adjacent_degree_two_triangle_count {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (hC : StrongC4Free H)
    {u w : W} (huw : H.Adj u w) (hdu : H.degree u = 2) (hdw : H.degree w = 2)
    (hlu : 4 ≤ deletionLoss H u) :
    triangleCount ((H.induce {u}ᶜ).induce
      {⟨w, by simpa using huw.ne.symm⟩}ᶜ) = triangleCount H := by
  classical
  have hl := deletionLoss_eq_degree_sub_trianglesAt hC u
  have htu : trianglesAt H u = 0 := by omega
  have h1 := triangleCount_induce_compl_add (G := H) u
  have h2 := triangleCount_induce_compl_add (G := H.induce {u}ᶜ)
    (⟨w, by simpa using huw.ne.symm⟩ : ({u}ᶜ : Set W))
  have hd := degree_delete_adjacent huw
  have ht := two_mul_trianglesAt_le_degree (strongC4Free_induce (s := {u}ᶜ) hC)
    (⟨w, by simpa using huw.ne.symm⟩ : ({u}ᶜ : Set W))
  omega

/-- Triangle incidence is unchanged on passing to a whole connected component. -/
theorem trianglesAt_component {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (hC : StrongC4Free H)
    (C : H.ConnectedComponent) (x : C.supp) :
    trianglesAt (H.induce C.supp) x = trianglesAt H x := by
  classical
  have hn : H.neighborSet x.val ⊆ C.supp := fun y hy =>
    C.mem_supp_of_adj_mem_supp x.property hy
  have hd : (H.induce C.supp).degree x = H.degree x.val := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    exact Fintype.card_congr
      { toFun := fun y => ⟨y.val.val, y.property⟩
        invFun := fun y => ⟨⟨y.val, hn y.property⟩, y.property⟩
        left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
        right_inv := fun _ => Subtype.ext rfl }
  have hl : lambda (H.induce C.supp) x = lambda H x.val :=
    lambda_induce_eq (G := H) x.property hn
  have h1 := lambda_add_trianglesAt hC x.val
  have h2 := lambda_add_trianglesAt (strongC4Free_induce (s := C.supp) hC) x
  omega

/-- A surviving triangle belongs to an actual connected component. -/
theorem exists_triangle_component {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (hC : StrongC4Free H)
    (ht : 0 < triangleCount H) :
    ∃ C : H.ConnectedComponent, 0 < triangleCount (H.induce C.supp) := by
  classical
  have hs := sum_trianglesAt (G := H)
  have hx : ∃ x : W, 0 < trianglesAt H x := by
    by_contra hn
    push Not at hn
    have hz : ∀ x, trianglesAt H x = 0 := fun x => Nat.eq_zero_of_le_zero (hn x)
    simp [hz] at hs
    omega
  obtain ⟨x, hx⟩ := hx
  let C := H.connectedComponentMk x
  let x' : C.supp := ⟨x, rfl⟩
  refine ⟨C, ?_⟩
  have he : trianglesAt (H.induce C.supp) x' = trianglesAt H x :=
    trianglesAt_component hC C x'
  have hle : trianglesAt (H.induce C.supp) x' ≤ triangleCount (H.induce C.supp) :=
    Finset.card_le_card (Finset.filter_subset _ _)
  omega

/-- Concrete disconnected induction step: the existence of a triangle makes
one of the component bounds strict. -/
theorem mass_lt_of_triangle_component_induction {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (hC : StrongC4Free H)
    (ht : 0 < triangleCount H)
    (ih : ∀ C : H.ConnectedComponent,
      neighbourhoodIndependenceSum (H.induce C.supp) ≤ 3 * Fintype.card C.supp ∧
      (0 < triangleCount (H.induce C.supp) →
        neighbourhoodIndependenceSum (H.induce C.supp) < 3 * Fintype.card C.supp)) :
    neighbourhoodIndependenceSum H < 3 * Fintype.card W := by
  obtain ⟨C, hCt⟩ := exists_triangle_component hC ht
  exact mass_lt_of_component_bounds H (fun D => (ih D).1) ⟨C, (ih C).2 hCt⟩

/-- Cardinality bookkeeping for successive deletion of two distinct vertices. -/
theorem two_vertex_card {W : Type*} [Fintype W] [DecidableEq W]
    {u w : W} (huw : u ≠ w) :
    Fintype.card ({⟨w, by simpa using huw.symm⟩}ᶜ :
      Set ({u}ᶜ : Set W)) + 2 = Fintype.card W := by
  classical
  let w' : ({u}ᶜ : Set W) := ⟨w, by simpa using huw.symm⟩
  have h1 : Fintype.card ({u}ᶜ : Set W) = Fintype.card W - 1 := by
    calc
      _ = Fintype.card {x : W // ¬ x = u} := Fintype.card_congr
        (Equiv.subtypeEquivRight (fun x => by simp))
      _ = _ := by rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have h2 : Fintype.card ({w'}ᶜ : Set ({u}ᶜ : Set W)) =
      Fintype.card ({u}ᶜ : Set W) - 1 := by
    calc
      _ = Fintype.card {x : ({u}ᶜ : Set W) // ¬ x = w'} := Fintype.card_congr
        (Equiv.subtypeEquivRight (fun x => by simp))
      _ = _ := by rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have hp : 0 < Fintype.card ({u}ᶜ : Set W) := Fintype.card_pos_iff.mpr ⟨w'⟩
  change Fintype.card ({w'}ᶜ : Set ({u}ᶜ : Set W)) + 2 = Fintype.card W
  omega

/-- Paper 1091 as a reusable structural reduction. The supplied strict bound
is on the actual disconnected remainder and can be obtained by
`mass_lt_of_triangle_component_induction`; it is not a bound on the original graph. -/
theorem adjacent_degree_two_strict_reduction {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (hC : StrongC4Free H)
    {u w : W} (huw : H.Adj u w) (hdu : H.degree u = 2) (hdw : H.degree w = 2)
    (hlu : 4 ≤ deletionLoss H u)
    (ih : neighbourhoodIndependenceSum ((H.induce {u}ᶜ).induce
        {⟨w, by simpa using huw.ne.symm⟩}ᶜ) <
      3 * Fintype.card ({⟨w, by simpa using huw.ne.symm⟩}ᶜ :
        Set ({u}ᶜ : Set W))) :
    neighbourhoodIndependenceSum H < 3 * Fintype.card W := by
  classical
  have he := adjacent_degree_two_edge_count huw hdu hdw
  have ht := adjacent_degree_two_triangle_count hC huw hdu hdw hlu
  have hm := two_vertex_mass_identity hC
    (strongC4Free_induce (strongC4Free_induce (s := {u}ᶜ) hC)) he ht
  exact two_vertex_deletion_strict hm (two_vertex_card huw.ne) ih

/-- A clique of the triangle-free Petersen graph has at most two vertices. -/
theorem petersen_clique_card_le_two (A : Finset PetersenVertex)
    (hA : petersenGraph.IsClique A) : A.card ≤ 2 := by
  have htri : ∀ a b c : PetersenVertex, petersenGraph.Adj a b →
      petersenGraph.Adj a c → ¬ petersenGraph.Adj b c := by native_decide
  by_contra hn
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp (by omega : 2 < A.card)
  exact htri a b c (hA ha hb hab) (hA ha hc hac) (hA hb hc hbc)

/-- Paper 1089, structural part: if deleting one vertex leaves Petersen,
strong C4-freeness forces the deleted vertex to have degree at most two. -/
theorem degree_le_two_of_delete_petersen {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (hC : StrongC4Free H) (v : W)
    (e : H.induce {v}ᶜ ≃g petersenGraph) : H.degree v ≤ 2 := by
  classical
  let f : petersenGraph ↪g H := e.symm.toEmbedding.trans (SimpleGraph.Embedding.induce {v}ᶜ)
  let A : Finset PetersenVertex := univ.filter (fun p => H.Adj v (f p))
  have hcl : petersenGraph.IsClique A := by
    intro a ha b hb hab
    exact petersen_extension_neighbors_clique hC f v
      (fun p => by exact (e.symm p).property ∘ Eq.symm) hab
      (mem_filter.mp ha).2 (mem_filter.mp hb).2
  have hc := petersen_clique_card_le_two A hcl
  have he : H.neighborSet v ≃ {p : PetersenVertex // p ∈ A} :=
    { toFun := fun x => ⟨e ⟨x.val, by simpa using x.property.ne.symm⟩, by
        simp only [A, mem_filter, mem_univ, true_and]
        change H.Adj v ((e.symm (e ⟨x.val, _⟩)).val)
        rw [e.symm_apply_apply]
        exact x.property⟩
      invFun := fun p => ⟨f p.val, (mem_filter.mp p.property).2⟩
      left_inv := by intro x; apply Subtype.ext; simp [f]
      right_inv := by intro p; apply Subtype.ext; simp [f] }
  have hcard := Fintype.card_congr he
  rw [H.card_neighborSet_eq_degree] at hcard
  have hcard' : H.degree v = A.card := by simpa only [Fintype.card_coe] using hcard
  omega

/-- Paper 1089: a strongly C4-free one-vertex extension of Petersen with a
triangle through the added vertex has strictly subextremal mass. -/
theorem mass_lt_of_delete_petersen {W : Type*} [Fintype W] [DecidableEq W]
    {H : SimpleGraph W} [DecidableRel H.Adj] (hC : StrongC4Free H) (v : W)
    (htv : 0 < trianglesAt H v) (e : H.induce {v}ᶜ ≃g petersenGraph) :
    neighbourhoodIndependenceSum H < 3 * Fintype.card W := by
  classical
  have hd := degree_le_two_of_delete_petersen hC v e
  have hm : neighbourhoodIndependenceSum (H.induce {v}ᶜ) = 30 := by
    rw [neighbourhoodIndependenceSum_iso e, petersen_mass]
  have hs := strongC4Free_S_identity hC
  have hs' := strongC4Free_S_identity (strongC4Free_induce (s := {v}ᶜ) hC)
  have he := edgeCount_induce_compl_add (G := H) v
  have ht := triangleCount_induce_compl_add (G := H) v
  have hnonneg := three_mul_triangleCount_le_two_edge (strongC4Free_induce (s := {v}ᶜ) hC)
  have hc : Fintype.card ({v}ᶜ : Set W) = 10 :=
    (Fintype.card_congr e.toEquiv).trans petersen_vertex_card
  have hcard : Fintype.card ({v}ᶜ : Set W) = Fintype.card W - 1 := by
    calc
      _ = Fintype.card {x : W // ¬ x = v} := Fintype.card_congr
        (Equiv.subtypeEquivRight (fun x => by simp))
      _ = _ := by rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  omega

end SectionFiveGlobal
end InducedPaths
