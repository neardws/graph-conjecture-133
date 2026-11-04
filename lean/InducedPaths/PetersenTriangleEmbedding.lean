/- Concrete induced embeddings for the thirteen-vertex Petersen endgame.
This support module does not import GlobalInduction. -/
module
public import InducedPaths.Basic
public import InducedPaths.Graphs
public import InducedPaths.SectionFiveGlobal
public import InducedPaths.OneTriangleMass

open SimpleGraph
@[expose] public section
namespace InducedPaths
namespace SectionFiveGlobal

variable {V : Type*} {G : SimpleGraph V}

/-- Map the Petersen core and the three explicitly named outside vertices.
No exhaustion hypothesis on the ambient graph is needed. -/
def petersenTriangleMap (e : petersenGraph ↪g G) (v x y : V) :
    PetersenVertex ⊕ Fin 3 → V
  | .inl p => e p
  | .inr i => if i = 0 then v else if i = 1 then x else y

/-- Full adjacency traces give an actual induced embedding, rather than just
an edge-preserving map. The outside vertices need not exhaust the ambient graph. -/
def petersenTriangleEmbedding (e : petersenGraph ↪g G) (v x y : V)
    (hv : ∀ p, v ≠ e p) (hx : ∀ p, x ≠ e p) (hy : ∀ p, y ≠ e p)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y)
    (u w a b : PetersenVertex)
    (hvcore : ∀ p, G.Adj v (e p) ↔ p = u ∨ p = w)
    (hxcore : ∀ p, G.Adj x (e p) ↔ p = a)
    (hycore : ∀ p, G.Adj y (e p) ↔ p = b)
    (hvxAdj : G.Adj v x) (hvyAdj : G.Adj v y) (hxyNon : ¬ G.Adj x y) :
    petersenTriangleExtension u w a b ↪g G where
  toFun := petersenTriangleMap e v x y
  inj' := by
    intro s t h
    cases s with
    | inl p =>
      cases t with
      | inl q => exact congrArg Sum.inl (e.injective h)
      | inr j =>
        fin_cases j <;> simp_all [petersenTriangleMap, Ne.symm]
    | inr i =>
      cases t with
      | inl q =>
        fin_cases i <;> simp_all [petersenTriangleMap]
      | inr j =>
        fin_cases i <;> fin_cases j <;>
          simp_all [petersenTriangleMap, Ne.symm]
  map_rel_iff' := by
    intro s t
    cases s with
    | inl p =>
      cases t with
      | inl q =>
        change G.Adj (e p) (e q) ↔ _
        rw [e.map_rel_iff]
        simp only [petersenTriangleExtension, simpleOf]
        exact ⟨fun h => ⟨fun he => h.ne (Sum.inl.inj he), Or.inl h⟩,
          fun h => h.2.elim id Adj.symm⟩
      | inr j =>
        fin_cases j <;>
          simp [petersenTriangleMap, petersenTriangleExtension, simpleOf,
            G.adj_comm, hvcore, hxcore, hycore]
    | inr i =>
      cases t with
      | inl q =>
        fin_cases i <;>
          simp [petersenTriangleMap, petersenTriangleExtension, simpleOf,
            hvcore, hxcore, hycore]
      | inr j =>
        fin_cases i <;> fin_cases j <;>
          simp [petersenTriangleMap, petersenTriangleExtension, simpleOf,
            hvxAdj, hvyAdj, hxyNon, G.adj_comm]

/-- Strong C4-freeness supplies the nonadjacency of each leaf support to
both endpoints of the core triangle edge, and separates the two supports. -/
theorem petersenTriangle_support_constraints
    (hC : StrongC4Free G) (e : petersenGraph ↪g G) (v x y : V)
    (hv : ∀ p, v ≠ e p) (hx : ∀ p, x ≠ e p) (hy : ∀ p, y ≠ e p)
    (hxy : x ≠ y) (u w a b : PetersenVertex)
    (hvu : G.Adj v (e u)) (hvw : G.Adj v (e w))
    (hvx : G.Adj v x) (hvy : G.Adj v y)
    (hxa : G.Adj x (e a)) (hyb : G.Adj y (e b)) :
    a ≠ b ∧ ¬ petersenGraph.Adj a u ∧ ¬ petersenGraph.Adj a w ∧
      ¬ petersenGraph.Adj b u ∧ ¬ petersenGraph.Adj b w := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hab
    subst b
    exact hC (fourCycle_isContained hvx hxa hyb.symm hvy.symm (hv a) hxy)
  · intro h
    exact hC (fourCycle_isContained hvx hxa (e.map_rel_iff.mpr h) hvu.symm
      (hv a) (hx u))
  · intro h
    exact hC (fourCycle_isContained hvx hxa (e.map_rel_iff.mpr h) hvw.symm
      (hv a) (hx w))
  · intro h
    exact hC (fourCycle_isContained hvy hyb (e.map_rel_iff.mpr h) hvu.symm
      (hv b) (hy u))
  · intro h
    exact hC (fourCycle_isContained hvy hyb (e.map_rel_iff.mpr h) hvw.symm
      (hv b) (hy w))

/-- The concrete trace data directly contradict P7-freeness. -/
theorem petersenTriangle_traces_not_P7free
    (hp : IsPkFree G 7) (e : petersenGraph ↪g G) (v x y : V)
    (hv : ∀ p, v ≠ e p) (hx : ∀ p, x ≠ e p) (hy : ∀ p, y ≠ e p)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y)
    (u w a b : PetersenVertex)
    (hvcore : ∀ p, G.Adj v (e p) ↔ p = u ∨ p = w)
    (hxcore : ∀ p, G.Adj x (e p) ↔ p = a)
    (hycore : ∀ p, G.Adj y (e p) ↔ p = b)
    (hvxAdj : G.Adj v x) (hvyAdj : G.Adj v y) (hxyNon : ¬ G.Adj x y)
    (huw : petersenGraph.Adj u w) (hab : a ≠ b)
    (hau : a ≠ u) (haw : a ≠ w) (hbu : b ≠ u) (hbw : b ≠ w)
    (hanu : ¬ petersenGraph.Adj a u) (hanw : ¬ petersenGraph.Adj a w)
    (hbnu : ¬ petersenGraph.Adj b u) (hbnw : ¬ petersenGraph.Adj b w) : False := by
  exact petersen_extension_not_P7free hp huw hab hau haw hbu hbw hanu hanw hbnu hbnw
    (petersenTriangleEmbedding e v x y hv hx hy hvx hvy hxy u w a b
      hvcore hxcore hycore hvxAdj hvyAdj hxyNon)

/-- No cut at `v` forces an outside vertex to attach to the core once the
other outside vertex is known nonadjacent. This is the leaf-exclusion step. -/
theorem petersenTriangle_exists_support
    (e : petersenGraph ↪g G) (v x y : V)
    (hv : ∀ p, v ≠ e p) (hx : ∀ p, x ≠ e p) (hvx : v ≠ x)
    (hpartition : ∀ z, (∃ p, z = e p) ∨ z = v ∨ z = x ∨ z = y)
    (hnocut : ¬ IsCutVertex G v) (hxy : ¬ G.Adj x y) :
    ∃ a, G.Adj x (e a) := by
  classical
  have hpre : (G.induce {z | z ≠ v}).Preconnected := by
    simpa only [IsCutVertex, not_not] using hnocut
  let x' : {z : V | z ≠ v} := ⟨x, hvx.symm⟩
  let p' : {z : V | z ≠ v} := ⟨e petersenHub, (hv petersenHub).symm⟩
  have hne : x' ≠ p' := fun h => hx petersenHub (congrArg Subtype.val h)
  obtain ⟨z, hz⟩ := (hpre x' p').nonempty_neighborSet_left hne
  have hadj : G.Adj x z.val := hz
  rcases hpartition z.val with ⟨a, ha⟩ | hzv | hzx | hzy
  · exact ⟨a, ha ▸ hadj⟩
  · exact (z.property hzv).elim
  · exact (hadj.ne hzx.symm).elim
  · exact (hxy (hzy ▸ hadj)).elim

section Concrete
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The actual thirteen-vertex configuration is impossible: the partition and
no-cut hypothesis produce supports, uniqueness of the triangle rules out the
outside edge and support endpoints, and strong C4-freeness supplies all remaining
finite-obstruction constraints. Connectivity is not needed beyond no-cut. -/
theorem petersenTriangle_partition_not_P7free
    (hC : StrongC4Free G) (hp : IsPkFree G 7) (hT : triangleCount G ≤ 1)
    (e : petersenGraph ↪g G) (v x y : V)
    (hv : ∀ p, v ≠ e p) (hx : ∀ p, x ≠ e p) (hy : ∀ p, y ≠ e p)
    (hvx : v ≠ x) (hvy : v ≠ y) (hxy : x ≠ y)
    (hpartition : ∀ z, (∃ p, z = e p) ∨ z = v ∨ z = x ∨ z = y)
    (hnocut : ¬ IsCutVertex G v) (u w : PetersenVertex)
    (huw : petersenGraph.Adj u w)
    (hvcore : ∀ p, G.Adj v (e p) ↔ p = u ∨ p = w)
    (hvxAdj : G.Adj v x) (hvyAdj : G.Adj v y)
    (hxunique : ∀ p q, G.Adj x (e p) → G.Adj x (e q) → p = q)
    (hyunique : ∀ p q, G.Adj y (e p) → G.Adj y (e q) → p = q) : False := by
  have hvu := (hvcore u).mpr (Or.inl rfl)
  have hvw := (hvcore w).mpr (Or.inr rfl)
  have heuw := e.map_rel_iff.mpr huw
  have hxyNon : ¬ G.Adj x y := by
    intro h
    have heq := oneTriangle_clique_eq hT hvu hvw heuw
      (is3Clique_triple_iff.mpr ⟨hvxAdj, hvyAdj, h⟩)
    have hxm : x ∈ ({v, e u, e w} : Finset V) := by rw [← heq]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxm
    exact hxm.elim (fun h => hvx h.symm) (fun h => h.elim (hx u) (hx w))
  obtain ⟨a, hxa⟩ := petersenTriangle_exists_support e v x y hv hx hvx
    hpartition hnocut hxyNon
  have hpartition' : ∀ z, (∃ p, z = e p) ∨ z = v ∨ z = y ∨ z = x := by
    intro z
    rcases hpartition z with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))
  obtain ⟨b, hyb⟩ := petersenTriangle_exists_support e v y x hv hy hvy
    hpartition' hnocut (fun h => hxyNon h.symm)
  have hxcore : ∀ p, G.Adj x (e p) ↔ p = a := by
    intro p; exact ⟨fun h => hxunique p a h hxa, fun h => h ▸ hxa⟩
  have hycore : ∀ p, G.Adj y (e p) ↔ p = b := by
    intro p; exact ⟨fun h => hyunique p b h hyb, fun h => h ▸ hyb⟩
  have haway : ∀ z : V, (∀ p, z ≠ e p) → G.Adj v z →
      ∀ c, G.Adj z (e c) → c ≠ u ∧ c ≠ w := by
    intro z hz hvz c hzc
    constructor
    · intro hc
      have hzu : G.Adj (e u) z := hc ▸ hzc.symm
      exact hz w (oneTriangle_common_neighbor hT hvu hvw heuw hvz hzu)
    · intro hc
      have hzw : G.Adj (e w) z := hc ▸ hzc.symm
      exact hz u (oneTriangle_common_neighbor hT hvw hvu heuw.symm hvz hzw)
  obtain ⟨hau, haw⟩ := haway x hx hvxAdj a hxa
  obtain ⟨hbu, hbw⟩ := haway y hy hvyAdj b hyb
  obtain ⟨hab, hanu, hanw, hbnu, hbnw⟩ :=
    petersenTriangle_support_constraints hC e v x y hv hx hy hxy u w a b
      hvu hvw hvxAdj hvyAdj hxa hyb
  exact petersenTriangle_traces_not_P7free hp e v x y hv hx hy hvx hvy hxy u w a b
    hvcore hxcore hycore hvxAdj hvyAdj hxyNon huw hab hau haw hbu hbw hanu hanw hbnu hbnw
end Concrete

end SectionFiveGlobal
end InducedPaths
