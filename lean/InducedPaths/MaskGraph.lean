/-
A graph interpretation of the actual certificate adjacency masks.

This is a foundation for checker semantics, not a correctness theorem for the
extension enumerator or its induced-P7 test.
-/
module

public import InducedPaths.Certificate
public import InducedPaths.Basic

@[expose] public section

namespace InducedPaths.Certificate

/-- Only in-range adjacency matters to the decoded graph. High mask bits need
not be normalized for this interpretation. -/
structure WellFormed (g : List ℕ) : Prop where
  symm : ∀ i j : Fin g.length, edge g i.val j.val = edge g j.val i.val
  loopless : ∀ i : Fin g.length, edge g i.val i.val = false

/-- Decode mask adjacency on the vertex set actually present in the list. -/
def toSimpleGraph (g : List ℕ) (h : WellFormed g) : SimpleGraph (Fin g.length) where
  Adj i j := edge g i.val j.val = true
  symm.symm := by
    intro i j hij
    rw [← h.symm i j]
    exact hij
  loopless.irrefl := by
    intro i hi
    rw [h.loopless i] at hi
    contradiction

instance (g : List ℕ) (h : WellFormed g) : DecidableRel (toSimpleGraph g h).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ = true))

@[simp] theorem toSimpleGraph_adj (g : List ℕ) (h : WellFormed g)
    (i j : Fin g.length) :
    (toSimpleGraph g h).Adj i j ↔ edge g i.val j.val = true := Iff.rfl

/-- The filtered list whose length is the degree term used by `loss`. -/
def maskNeighbors (g : List ℕ) (v : ℕ) : List ℕ :=
  (List.range g.length).filter fun i => Nat.testBit (g.getD v 0) i

@[simp] theorem mem_maskNeighbors (g : List ℕ) (v i : ℕ) :
    i ∈ maskNeighbors g v ↔ i < g.length ∧ edge g v i = true := by
  simp [maskNeighbors, edge]

/-- The certificate's degree count agrees with the degree of the decoded graph.
No popcount correctness is needed: `loss` itself counts a filtered range. -/
theorem degree_toSimpleGraph (g : List ℕ) (h : WellFormed g)
    (v : Fin g.length) :
    (toSimpleGraph g h).degree v = (maskNeighbors g v.val).length := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hn : (maskNeighbors g v.val).Nodup :=
    (List.nodup_range (n := g.length)).filter _
  rw [← List.toFinset_card_of_nodup hn]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    have hadj : (toSimpleGraph g h).Adj v i := by simpa using hi
    simpa using And.intro i.isLt hadj
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro i hi
    have hm : i < g.length ∧ edge g v.val i = true := by simpa using hi
    refine ⟨⟨i, hm.1⟩, ?_, rfl⟩
    simpa using hm.2

/-- The triangle term actually accumulated by the executable checker. This is
an ordered-pair count with `a < b`, so each neighbour edge is counted once. -/
def maskTriangles (g : List ℕ) (v : ℕ) : ℕ :=
  let ns := maskNeighbors g v
  ns.foldl (fun acc a =>
    acc + (ns.filter fun b => decide (a < b) && edge g a b).length) 0

/-- First loss decomposition, separating the degree interpretation from the
triangle-accumulator identification proved below. -/
theorem loss_eq_degree_sub_maskTriangles (g : List ℕ) (h : WellFormed g)
    (v : Fin g.length) :
    loss g v.val = 2 * (toSimpleGraph g h).degree v - 3 * maskTriangles g v.val := by
  rw [degree_toSimpleGraph]
  rfl

def neighborPairs (g : List ℕ) (v : ℕ) : Finset (ℕ × ℕ) :=
  ((maskNeighbors g v).toFinset ×ˢ (maskNeighbors g v).toFinset).filter
    (fun p => p.1 < p.2 ∧ edge g p.1 p.2 = true)

@[simp] theorem mem_neighborPairs (g : List ℕ) (v a b : ℕ) :
    (a, b) ∈ neighborPairs g v ↔
      (a < g.length ∧ edge g v a = true) ∧
      (b < g.length ∧ edge g v b = true) ∧ a < b ∧ edge g a b = true := by
  simp [neighborPairs, and_assoc]

/-- Exact finite-set interpretation of the executable triangle accumulator. -/
theorem maskTriangles_eq_card_neighborPairs (g : List ℕ) (v : ℕ) :
    maskTriangles g v = (neighborPairs g v).card := by
  classical
  let ns := maskNeighbors g v
  have hn : ns.Nodup := (List.nodup_range (n := g.length)).filter _
  have inner (a : ℕ) :
      (ns.filter fun b => decide (a < b) && edge g a b).length =
        ∑ b ∈ ns.toFinset, if a < b ∧ edge g a b = true then 1 else 0 := by
    rw [← List.toFinset_card_of_nodup (hn.filter _)]
    have hf : (ns.filter fun b => decide (a < b) && edge g a b).toFinset =
        ns.toFinset.filter (fun b => a < b ∧ edge g a b = true) := by ext; simp
    rw [hf, Finset.card_filter]
  unfold maskTriangles
  change ns.foldl _ 0 = _
  rw [← List.foldl_map, ← List.sum_eq_foldl, ← List.sum_toFinset _ hn]
  change (∑ a ∈ ns.toFinset,
    (ns.filter fun b => decide (a < b) && edge g a b).length) = _
  simp_rw [inner]
  symm
  unfold neighborPairs
  rw [Finset.card_filter, Finset.sum_product]

/-- Count the ordered mask neighbour pairs as actual neighbourhood edges. -/
theorem card_neighborPairs_eq_trianglesAt (g : List ℕ) (h : WellFormed g)
    (v : Fin g.length) :
    (neighborPairs g v.val).card = InducedPaths.trianglesAt (toSimpleGraph g h) v := by
  classical
  let G := toSimpleGraph g h
  let es := G.edgeFinset.filter (fun e => e.toFinset ⊆ G.neighborFinset v)
  have hes : es.card = InducedPaths.trianglesAt G v := by
    rw [InducedPaths.trianglesAt_eq_neighborEdges]
    have hmap := SimpleGraph.map_edgeFinset_induce (G := G) (s := G.neighborSet v)
    have hc := congrArg Finset.card hmap
    rw [Finset.card_map] at hc
    have hf := SimpleGraph.filter_edgeFinset_toFinset_subset (G := G)
      ((G.neighborSet v).toFinset)
    have heq : es = G.edgeFinset ∩ (G.neighborSet v).toFinset.sym2 := by
      dsimp [es]
      rw [SimpleGraph.neighborFinset_def]
      exact hf
    rw [heq, InducedPaths.edgeCount]
    exact hc.symm
  rw [← hes]
  let f (p : ℕ × ℕ) (hp : p ∈ neighborPairs g v.val) : Sym2 (Fin g.length) :=
    s(⟨p.1, (mem_neighborPairs g v.val p.1 p.2).mp hp |>.1.1⟩,
      ⟨p.2, (mem_neighborPairs g v.val p.1 p.2).mp hp |>.2.1.1⟩)
  apply Finset.card_bij f
  · intro p hp
    rcases (mem_neighborPairs g v.val p.1 p.2).mp hp with ⟨ha, hb, hab, he⟩
    simp only [es, Finset.mem_filter, SimpleGraph.mem_edgeFinset]
    constructor
    · exact he
    · intro x hx
      have hx' : x = ⟨p.1, ha.1⟩ ∨ x = ⟨p.2, hb.1⟩ := by
        simpa [f, Sym2.toFinset_mk_eq] using hx
      rcases hx' with rfl | rfl
      · exact (G.mem_neighborFinset _ _).mpr ha.2
      · exact (G.mem_neighborFinset _ _).mpr hb.2
  · intro p hp q hq heq
    have hp' := (mem_neighborPairs g v.val p.1 p.2).mp hp
    have hq' := (mem_neighborPairs g v.val q.1 q.2).mp hq
    have heq' := Sym2.eq_iff.mp heq
    rcases heq' with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · exact Prod.ext (congrArg Fin.val ha) (congrArg Fin.val hb)
    · have ha' := congrArg Fin.val ha
      have hb' := congrArg Fin.val hb
      dsimp at ha' hb'
      omega
  · intro e he
    have he' := Finset.mem_filter.mp he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : G.Adj a b := (SimpleGraph.mem_edgeFinset.mp he'.1)
      have hva : G.Adj v a := (G.mem_neighborFinset _ _).mp (he'.2 (by simp))
      have hvb : G.Adj v b := (G.mem_neighborFinset _ _).mp (he'.2 (by simp))
      have hne : a.val ≠ b.val := fun hh => hab.ne (Fin.ext hh)
      rcases lt_or_gt_of_ne hne with hablt | hbalt
      · have hp : (a.val, b.val) ∈ neighborPairs g v.val :=
          (mem_neighborPairs g v.val a.val b.val).mpr
            ⟨⟨a.isLt, hva⟩, ⟨b.isLt, hvb⟩, hablt, hab⟩
        exact ⟨(a.val, b.val), hp, rfl⟩
      · have hp : (b.val, a.val) ∈ neighborPairs g v.val :=
          (mem_neighborPairs g v.val b.val a.val).mpr
            ⟨⟨b.isLt, hvb⟩, ⟨a.isLt, hva⟩, hbalt, hab.symm⟩
        exact ⟨(b.val, a.val), hp, Sym2.eq_swap⟩

/-- The actual mask loss equals the usual degree-and-triangle formula. -/
theorem loss_eq_degree_sub_trianglesAt (g : List ℕ) (h : WellFormed g)
    (v : Fin g.length) :
    loss g v.val = 2 * (toSimpleGraph g h).degree v -
      3 * InducedPaths.trianglesAt (toSimpleGraph g h) v := by
  rw [loss_eq_degree_sub_maskTriangles, maskTriangles_eq_card_neighborPairs,
    card_neighborPairs_eq_trianglesAt]

end InducedPaths.Certificate
