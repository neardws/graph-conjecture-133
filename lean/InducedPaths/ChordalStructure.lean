/-
Case 3 of Theorem 3.6 (paper/main.tex, lines 583–584).
A longest induced path proves simplicial existence directly in the strong
C₄-free, P₆-free, induced-C₅-free, induced-C₆-free class. Hereditary
simplicial elimination and the local ChordalMass bound give S ≤ 2n - 2.
-/
module

public import InducedPaths.ChordalMass

open Finset SimpleGraph

@[expose] public section
namespace InducedPaths

universe u

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Every nonempty induced subgraph has a vertex with clique neighbourhood.
This is the elimination property needed for the chordal mass bound. -/
def HasHereditarySimplicialVertex {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ s : Set V, s.Nonempty → ∃ v : s,
    (G.induce s).IsClique ((G.induce s).neighborSet v)

/-- The elimination property is preserved by restriction to any vertex set. -/
lemma HasHereditarySimplicialVertex.induce {V : Type*} {G : SimpleGraph V}
    (h : HasHereditarySimplicialVertex G) (s : Set V) :
    HasHereditarySimplicialVertex (G.induce s) := by
  intro t ht
  let u : Set V := {x | ∃ hx : x ∈ s, (⟨x, hx⟩ : s) ∈ t}
  have hu : u.Nonempty := by
    obtain ⟨x, hx⟩ := ht
    exact ⟨x.val, x.property, hx⟩
  obtain ⟨v, hv⟩ := h u hu
  obtain ⟨hvs, hvt⟩ := v.property
  let w : t := ⟨⟨v.val, hvs⟩, hvt⟩
  refine ⟨w, ?_⟩
  intro a ha b hb hab
  have hau : a.val.val ∈ u := ⟨a.val.property, a.property⟩
  have hbu : b.val.val ∈ u := ⟨b.val.property, b.property⟩
  exact hv (show (G.induce u).Adj v ⟨a.val.val, hau⟩ from ha)
    (show (G.induce u).Adj v ⟨b.val.val, hbu⟩ from hb)
    (by
      intro he
      have hev : a.val.val = b.val.val := congrArg (fun z : u => z.val) he
      exact hab (Subtype.ext (Subtype.ext hev)))

/-- A nonempty graph satisfying the hereditary elimination property has a
simplicial vertex in the original graph, not just in an isomorphic restriction. -/
lemma HasHereditarySimplicialVertex.exists_vertex {V : Type*} {G : SimpleGraph V}
    (h : HasHereditarySimplicialVertex G) [Nonempty V] :
    ∃ v, G.IsClique (G.neighborSet v) := by
  obtain ⟨v, hv⟩ := h Set.univ (Set.univ_nonempty)
  refine ⟨v.val, ?_⟩
  intro a ha b hb hab
  exact hv (show (G.induce Set.univ).Adj v ⟨a, Set.mem_univ _⟩ from ha)
    (show (G.induce Set.univ).Adj v ⟨b, Set.mem_univ _⟩ from hb)
    (by simpa using hab)

/-- A simplicial vertex of a strong `C₄`-free graph has degree at most two. -/
lemma degree_le_two_of_neighbor_clique {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hC : StrongC4Free G)
    (v : V) (hcl : G.IsClique (G.neighborSet v)) : G.degree v ≤ 2 := by
  have hlam := lambda_le_one_of_neighbor_clique v hcl
  have hsum := lambda_add_trianglesAt hC v
  have ht := two_mul_trianglesAt_le_degree hC v
  omega

/-- The one-vertex (and empty) base case for elimination. -/
lemma neighbourhoodIndependenceSum_eq_zero_of_subsingleton {V : Type*}
    [Fintype V] [Subsingleton V] (G : SimpleGraph V) :
    neighbourhoodIndependenceSum G = 0 := by
  classical
  unfold neighbourhoodIndependenceSum
  apply Finset.sum_eq_zero
  intro v _
  have hn : G.neighborSet v = ∅ := by
    ext w
    simp only [mem_neighborSet, Set.mem_empty_iff_false, iff_false]
    intro hadj
    exact hadj.ne (Subsingleton.elim _ _)
  change (G.induce (G.neighborSet v)).indepNum = 0
  obtain ⟨s, hs⟩ := (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum
  have he : s = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x _
    have hx := x.property
    exact (Set.eq_empty_iff_forall_notMem.mp hn x.val) hx
  have hc := hs.card_eq
  rw [he] at hc
  simpa using hc.symm

/-- Simplicial elimination gives the sharp chordal-branch mass bound.
Connectivity is unnecessary: the hereditary elimination property alone is
sufficient. No existence theorem for simplicial vertices is hidden here. -/
theorem mass_le_two_mul_card_sub_two_of_hereditary_simplicial
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (hC : StrongC4Free G)
    (h : HasHereditarySimplicialVertex G) :
    neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V - 2 := by
  classical
  suffices hall : ∀ n : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], Fintype.card W = n →
      StrongC4Free H → HasHereditarySimplicialVertex H →
      neighbourhoodIndependenceSum H ≤ 2 * Fintype.card W - 2 by
    exact hall (Fintype.card V) G rfl hC h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W _ _ H _ hcard hC h
    by_cases hn : Fintype.card W ≤ 1
    · haveI : Subsingleton W := ⟨Fintype.card_le_one_iff.mp hn⟩
      rw [neighbourhoodIndependenceSum_eq_zero_of_subsingleton]
      exact Nat.zero_le _
    · have hpos : 0 < Fintype.card W := by omega
      haveI : Nonempty W := Fintype.card_pos_iff.mp hpos
      obtain ⟨v, hv⟩ := h.exists_vertex
      let s : Set W := {v}ᶜ
      have hs : Fintype.card s = Fintype.card W - 1 := by
        simpa [s] using Fintype.card_compl_set ({v} : Set W)
      have hslt : Fintype.card s < n := by omega
      have hsmall := ih (Fintype.card s) hslt (H.induce s) rfl
        (strongC4Free_induce hC) (h.induce s)
      have hstep := simplicial_mass_le_deleted_add_two hC v hv
      change neighbourhoodIndependenceSum H ≤ 2 * Fintype.card W - 2
      change neighbourhoodIndependenceSum H ≤
        neighbourhoodIndependenceSum (H.induce s) + 2 at hstep
      omega

/-- In the matching neighbourhood of a strong `C₄`-free graph, failure
of simpliciality supplies a neighbour nonadjacent to any prescribed neighbour.
This is the endpoint-extension step in a longest induced path argument. -/
lemma exists_neighbor_nonadjacent_of_not_simplicial {V : Type*}
    {G : SimpleGraph V} (hC : StrongC4Free G) {v a : V} (hva : G.Adj v a)
    (hnot : ¬ G.IsClique (G.neighborSet v)) :
    ∃ y, G.Adj v y ∧ y ≠ a ∧ ¬ G.Adj a y := by
  classical
  by_contra hex
  have hall : ∀ y, G.Adj v y → y ≠ a → G.Adj a y := by
    intro y hy hya
    by_contra hay
    exact hex ⟨y, hy, hya, hay⟩
  apply hnot
  intro x hx y hy hxy
  by_cases hxa : x = a
  · subst x
    exact hall y hy (Ne.symm hxy)
  by_cases hya : y = a
  · subst y
    exact (hall x hx hxa).symm
  exact False.elim (hC (fourCycle_isContained hx (hall x hx hxa).symm
    (hall y hy hya) hy.symm hva.ne hxy))

/-- An outside vertex attached to the first vertex of an induced path cannot
also meet its third vertex in a strong `C₄`-free graph. -/
lemma endpoint_extension_nonadj_two {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) {n : ℕ} (hn : 2 < n) (f : pathGraph n ↪g G)
    {y : V} (hy : G.Adj y (f ⟨0, by omega⟩))
    (hy1 : y ≠ f ⟨1, by omega⟩) : ¬ G.Adj y (f ⟨2, hn⟩) := by
  intro hy2
  have h01 : G.Adj (f ⟨0, by omega⟩) (f ⟨1, by omega⟩) :=
    f.map_rel_iff.mpr (by simp [pathGraph_adj])
  have h12 : G.Adj (f ⟨1, by omega⟩) (f ⟨2, hn⟩) :=
    f.map_rel_iff.mpr (by simp [pathGraph_adj])
  exact hC (fourCycle_isContained hy h01 h12 hy2.symm hy1
    (f.injective.ne (by simp)))

/-- A first new contact at the fourth path vertex closes an induced `C₅`. -/
lemma endpoint_extension_nonadj_three {V : Type*} {G : SimpleGraph V}
    (h5 : ¬ cycleGraph 5 ⊴ G) {n : ℕ} (hn : 3 < n) (f : pathGraph n ↪g G)
    {y : V} (hy : G.Adj y (f ⟨0, by omega⟩))
    (hyoff : ∀ i, y ≠ f i)
    (hy1 : ¬ G.Adj y (f ⟨1, by omega⟩))
    (hy2 : ¬ G.Adj y (f ⟨2, by omega⟩)) :
    ¬ G.Adj y (f ⟨3, hn⟩) := by
  intro hy3
  let verts : Fin 5 → V := ![y, f ⟨0, by omega⟩, f ⟨1, by omega⟩,
    f ⟨2, by omega⟩, f ⟨3, hn⟩]
  apply h5
  refine ⟨{ toFun := verts, inj' := ?_, map_rel_iff' := ?_ }⟩
  · intro i j he
    fin_cases i <;> fin_cases j <;>
      simp_all [verts, hyoff, f.injective.eq_iff] <;>
      exact (hyoff _ he.symm).elim
  · intro i j
    change G.Adj (verts i) (verts j) ↔ (cycleGraph 5).Adj i j
    fin_cases i <;> fin_cases j <;>
      simp [verts, cycleGraph_adj, Fin.reduceSub,
        hy, hy.symm, hy1, hy2, hy3, hy3.symm,
        f.map_adj_iff, pathGraph_adj] <;>
      first
      | decide
      | exact iff_of_false (fun hh => hy1 hh.symm) (by decide)
      | exact iff_of_false (fun hh => hy2 hh.symm) (by decide)

/-- A first new contact at the fifth path vertex closes an induced `C₆`. -/
lemma endpoint_extension_nonadj_four {V : Type*} {G : SimpleGraph V}
    (h6 : ¬ cycleGraph 6 ⊴ G) {n : ℕ} (hn : 4 < n) (f : pathGraph n ↪g G)
    {y : V} (hy : G.Adj y (f ⟨0, by omega⟩))
    (hyoff : ∀ i, y ≠ f i)
    (hy1 : ¬ G.Adj y (f ⟨1, by omega⟩))
    (hy2 : ¬ G.Adj y (f ⟨2, by omega⟩))
    (hy3 : ¬ G.Adj y (f ⟨3, by omega⟩)) :
    ¬ G.Adj y (f ⟨4, hn⟩) := by
  intro hy4
  let verts : Fin 6 → V := ![y, f ⟨0, by omega⟩, f ⟨1, by omega⟩,
    f ⟨2, by omega⟩, f ⟨3, by omega⟩, f ⟨4, hn⟩]
  apply h6
  refine ⟨{ toFun := verts, inj' := ?_, map_rel_iff' := ?_ }⟩
  · intro i j he
    fin_cases i <;> fin_cases j <;>
      simp_all [verts, hyoff, f.injective.eq_iff] <;>
      exact (hyoff _ he.symm).elim
  · intro i j
    change G.Adj (verts i) (verts j) ↔ (cycleGraph 6).Adj i j
    fin_cases i <;> fin_cases j <;>
      simp [verts, cycleGraph_adj, Fin.reduceSub,
        hy, hy.symm, hy1, hy2, hy3, hy4, hy4.symm,
        f.map_adj_iff, pathGraph_adj] <;>
      first
      | decide
      | exact iff_of_false (fun hh => hy1 hh.symm) (by decide)
      | exact iff_of_false (fun hh => hy2 hh.symm) (by decide)
      | exact iff_of_false (fun hh => hy3 hh.symm) (by decide)

/-- Prepending a fresh vertex with exactly one contact extends an induced path. -/
def prependInducedPath {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (_hn : 0 < n) (f : pathGraph n ↪g G) (y : V)
    (hoff : ∀ i, y ≠ f i) (hcontact : ∀ i, G.Adj y (f i) ↔ i.val = 0) :
    pathGraph (n + 1) ↪g G where
  toFun := Fin.cases y (fun i => f i)
  inj' := by
    intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro _; rfl
      · intro he; exact (hoff _ he).elim
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro he; exact (hoff _ he.symm).elim
      · intro he; exact congrArg Fin.succ (f.injective he)
  map_rel_iff' := by
    intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b => ?_) j
      · simp [pathGraph_adj]
      · simpa [pathGraph_adj] using hcontact b
    · refine Fin.cases ?_ (fun b => ?_) j
      · simpa [pathGraph_adj, G.adj_comm] using hcontact a
      · simp [pathGraph_adj]

/-- In the no-`C₅`, no-`C₆`, `P₆`-free branch, the first vertex of a
longest induced path is simplicial. This proves existence without importing
a general chordal graph theorem. -/
theorem exists_simplicial_of_no_induced_five_six {V : Type*} [Fintype V]
    [Nonempty V] {G : SimpleGraph V} (hC : StrongC4Free G)
    (hp : IsPkFree G 6) (h5 : ¬ cycleGraph 5 ⊴ G) (h6 : ¬ cycleGraph 6 ⊴ G) :
    ∃ v, G.IsClique (G.neighborSet v) := by
  classical
  let n := inducedPathOrder G
  obtain ⟨f⟩ := inducedPathOrder_witness G
  have hn6 : n < 6 := (isPkFree_iff_inducedPathOrder_lt G 6).mp hp
  have hnpos : 0 < n := by
    obtain ⟨v⟩ := ‹Nonempty V›
    have hc : pathGraph 1 ⊴ G := ⟨{
      toFun := fun _ => v
      inj' := fun _ _ _ => Subsingleton.elim _ _
      map_rel_iff' := by intro i j; fin_cases i; fin_cases j; simp [pathGraph_adj] }⟩
    have hh := le_csSup (inducedPathOrder_bddAbove G) hc
    change 1 ≤ n at hh
    omega
  let z : Fin n := ⟨0, hnpos⟩
  refine ⟨f z, ?_⟩
  by_contra hnot
  have hn2 : 2 ≤ n := by
    by_contra hn2
    have hn1 : n = 1 := by omega
    obtain ⟨x, hx, y, hy, hxy, hnxy⟩ :
        ∃ x ∈ G.neighborSet (f z), ∃ y ∈ G.neighborSet (f z), x ≠ y ∧ ¬ G.Adj x y := by
      change ¬ Set.Pairwise (G.neighborSet (f z)) G.Adj at hnot
      simp only [Set.Pairwise, not_forall, not_imp] at hnot
      obtain ⟨x, hx, y, hy, hxy, hnxy⟩ := hnot
      exact ⟨x, hx, y, hy, hxy, hnxy⟩
    have hxoff : ∀ i, x ≠ f i := by
      intro i
      have hi : i = z := Fin.ext (by have := i.isLt; omega)
      rw [hi]
      exact (show G.Adj (f z) x from hx).ne.symm
    have hc : ∀ i, G.Adj x (f i) ↔ i.val = 0 := by
      intro i
      have hi : i = z := Fin.ext (by have := i.isLt; omega)
      rw [hi]
      simpa [z] using (show G.Adj (f z) x from hx).symm
    have hh := le_csSup (inducedPathOrder_bddAbove G)
      (show pathGraph (n + 1) ⊴ G from ⟨prependInducedPath hnpos f x hxoff hc⟩)
    change n + 1 ≤ n at hh
    omega
  let a : Fin n := ⟨1, by omega⟩
  have hza : G.Adj (f z) (f a) := f.map_rel_iff.mpr (by simp [z, a, pathGraph_adj])
  obtain ⟨y, hy, hya, hnya⟩ :=
    exists_neighbor_nonadjacent_of_not_simplicial hC hza hnot
  have hyoff : ∀ i, y ≠ f i := by
    intro i he
    have hzi : (pathGraph n).Adj z i := f.map_rel_iff.mp (he ▸ hy)
    have hi : i = a := by
      apply Fin.ext
      have hh : 1 = i.val := by simpa [z, pathGraph_adj] using hzi
      exact hh.symm
    exact hya (he.trans (congrArg f hi))
  have hy0 : G.Adj y (f ⟨0, hnpos⟩) := hy.symm
  have hy1 : ¬ G.Adj y (f ⟨1, by omega⟩) := fun hh => hnya hh.symm
  have hcontact : ∀ i, G.Adj y (f i) ↔ i.val = 0 := by
    intro i
    by_cases hi0 : i.val = 0
    · have hi : i = z := Fin.ext hi0
      subst i
      simpa [z] using hy0
    · simp only [hi0, iff_false]
      have hi := i.isLt
      have hiCases : i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
      rcases hiCases with hi1 | hi2 | hi3 | hi4
      · have he : i = a := Fin.ext hi1
        subst i
        exact hy1
      · have h2 : 2 < n := by omega
        have he : i = ⟨2, h2⟩ := Fin.ext hi2
        rw [he]
        exact endpoint_extension_nonadj_two hC h2 f hy0 hya
      · have h3 : 3 < n := by omega
        have he : i = ⟨3, h3⟩ := Fin.ext hi3
        rw [he]
        exact endpoint_extension_nonadj_three h5 h3 f hy0 hyoff hy1
          (endpoint_extension_nonadj_two hC (by omega) f hy0 hya)
      · have h4 : 4 < n := by omega
        have he : i = ⟨4, h4⟩ := Fin.ext hi4
        rw [he]
        have hy2 := endpoint_extension_nonadj_two hC (by omega : 2 < n) f hy0 hya
        have hy3 := endpoint_extension_nonadj_three h5 (by omega : 3 < n) f hy0 hyoff hy1 hy2
        exact endpoint_extension_nonadj_four h6 h4 f hy0 hyoff hy1 hy2 hy3
  have hh := le_csSup (inducedPathOrder_bddAbove G)
    (show pathGraph (n + 1) ⊴ G from ⟨prependInducedPath hnpos f y hyoff hcontact⟩)
  change n + 1 ≤ n at hh
  omega

/-- The no-hole branch has the hereditary simplicial elimination property.
Here `P₆`-freeness makes the direct longest-path proof finite. -/
theorem hereditary_simplicial_of_no_induced_five_six {V : Type*} [Fintype V]
    {G : SimpleGraph V} (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (h5 : ¬ cycleGraph 5 ⊴ G) (h6 : ¬ cycleGraph 6 ⊴ G) :
    HasHereditarySimplicialVertex G := by
  classical
  intro s hs
  haveI : Nonempty s := hs.to_subtype
  have hp' : IsPkFree (G.induce s) 6 := by
    intro hc
    exact hp (hc.trans (SimpleGraph.Embedding.induce s).isIndContained)
  have h5' : ¬ cycleGraph 5 ⊴ G.induce s := by
    intro hc
    exact h5 (hc.trans (SimpleGraph.Embedding.induce s).isIndContained)
  have h6' : ¬ cycleGraph 6 ⊴ G.induce s := by
    intro hc
    exact h6 (hc.trans (SimpleGraph.Embedding.induce s).isIndContained)
  exact exists_simplicial_of_no_induced_five_six (strongC4Free_induce hC) hp' h5' h6'

/-- Case 3 of Theorem 3.6: a strong `C₄`-free, `P₆`-free graph with
no induced five- or six-cycle satisfies `S ≤ 2n - 2`. The result even
holds without the connectedness assumption in the paper. -/
theorem chordal_branch_mass_bound {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hC : StrongC4Free G)
    (hp : IsPkFree G 6) (h5 : ¬ cycleGraph 5 ⊴ G) (h6 : ¬ cycleGraph 6 ⊴ G) :
    neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V - 2 := by
  exact mass_le_two_mul_card_sub_two_of_hereditary_simplicial hC
    (hereditary_simplicial_of_no_induced_five_six hC hp h5 h6)

end InducedPaths
