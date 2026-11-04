/-
The local trace calculation for an induced hexagon.  Unlike Lemma 3.4,
this calculation does not assume that the hexagon dominates the graph.
-/
module

public import InducedPaths.Basic
public meta import Mathlib.Data.Fintype.Defs
public meta import Mathlib.Combinatorics.SimpleGraph.CycleGraph

open scoped SimpleGraph
open SimpleGraph

@[expose] public section

namespace InducedPaths

/-- Adjacency on a hexagon together with one extra vertex of prescribed trace. -/
def hexTraceAdj (t : Fin 6 → Bool) : Option (Fin 6) → Option (Fin 6) → Prop
  | none, none => False
  | none, some j => t j = true
  | some i, none => t i = true
  | some i, some j => (cycleGraph 6).Adj i j

instance (t : Fin 6 → Bool) : DecidableRel (hexTraceAdj t) := fun a b => by
  cases a <;> cases b <;> unfold hexTraceAdj <;> infer_instance

/-- A candidate forbidden path: the extra vertex followed by five consecutive
vertices of the hexagon. -/
def hexTracePath (start : Fin 6) (k : Fin 6) : Option (Fin 6) :=
  if k = 0 then none else some (start + (k - 1))

/-- The entire finite trace calculation.  Only 64 traces are considered; the
certificate contains actual injective induced-path maps, not graph counts. -/
theorem hexTrace_certificate : ∀ t : Fin 6 → Bool,
    (∃ i, t i = true) →
    (∀ i, ¬ (t i = true ∧ t (i + 2) = true)) →
    (∃ i, ∀ j, t j = true ↔ j = i ∨ j = i + 3) ∨
    (∃ start, Function.Injective (hexTracePath start) ∧
      ∀ a b, hexTraceAdj t (hexTracePath start a) (hexTracePath start b) ↔
        (pathGraph 6).Adj a b) := by
  native_decide

/-- In a strong `C₄`-free graph, a vertex outside an induced hexagon cannot
meet two hexagon vertices separated by two steps. -/
theorem hexTrace_no_distance_two {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 6 ↪g G) {w : V}
    (hw : ∀ i, c i ≠ w) (i : Fin 6) :
    ¬ (G.Adj w (c i) ∧ G.Adj w (c (i + 2))) := by
  rintro ⟨h₁, h₂⟩
  have hcycle : ∀ i : Fin 6,
      (cycleGraph 6).Adj i (i + 1) ∧
      (cycleGraph 6).Adj (i + 1) (i + 2) ∧ i ≠ i + 2 := by
    native_decide
  obtain ⟨ha, hb, hne⟩ := hcycle i
  exact hC (fourCycle_isContained h₁ ((c.map_rel_iff).2 ha) ((c.map_rel_iff).2 hb)
    h₂.symm (hw (i + 1)).symm (fun h => hne (c.injective h)))

/-- Every nonempty trace on an induced hexagon in a strong `C₄`-free,
`P₆`-free graph is exactly an antipodal pair. -/
theorem hexTrace_antipodal {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    {w : V} (hw : ∀ i, c i ≠ w) (hne : ∃ i, G.Adj w (c i)) :
    ∃ i : Fin 6, ∀ j, G.Adj w (c j) ↔ j = i ∨ j = i + 3 := by
  classical
  let t : Fin 6 → Bool := fun i => decide (G.Adj w (c i))
  have ht : ∃ i, t i = true := by simpa [t] using hne
  have htwo : ∀ i, ¬ (t i = true ∧ t (i + 2) = true) := by
    simpa [t] using hexTrace_no_distance_two hC c hw
  rcases hexTrace_certificate t ht htwo with hant | ⟨start, hinj, hpath⟩
  · simpa [t] using hant
  · exfalso
    apply hp
    let f : Option (Fin 6) → V := fun x => x.elim w c
    have hf : Function.Injective f := by
      intro a b hab
      cases a with
      | none =>
          cases b with
          | none => rfl
          | some j => exact False.elim (hw j hab.symm)
      | some i =>
          cases b with
          | none => exact False.elim (hw i hab)
          | some j => exact congrArg some (c.injective hab)
    have hadj : ∀ a b, G.Adj (f a) (f b) ↔ hexTraceAdj t a b := by
      intro a b
      cases a <;> cases b <;> simp [f, hexTraceAdj, t, adj_comm]
    exact ⟨{
      toEmbedding := ⟨f ∘ hexTracePath start, hf.comp hinj⟩
      map_rel_iff' := by
        intro a b
        exact (hadj _ _).trans (hpath a b)
    }⟩

/-- Antipodal traces are closed under taking the opposite index. -/
theorem hexTrace_opposite {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    {w : V} (hw : ∀ i, c i ≠ w) {j : Fin 6} (hj : G.Adj w (c j)) :
    G.Adj w (c (j + 3)) := by
  obtain ⟨i, hi⟩ := hexTrace_antipodal hC hp c hw ⟨j, hj⟩
  have hfin : ∀ i j : Fin 6,
      (j = i ∨ j = i + 3) → (j + 3 = i ∨ j + 3 = i + 3) := by
    native_decide
  exact (hi _).2 (hfin i j ((hi j).1 hj))

/-- Distinct external vertices with nonempty traces cannot share a hexagon
neighbour.  This conclusion, too, does not require domination. -/
theorem hexTrace_disjoint {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    {w w' : V} (hw : ∀ i, c i ≠ w) (hw' : ∀ i, c i ≠ w')
    (hww' : w ≠ w') (i : Fin 6) :
    ¬ (G.Adj w (c i) ∧ G.Adj w' (c i)) := by
  rintro ⟨ha, hb⟩
  have ha' := hexTrace_opposite hC hp c hw ha
  have hb' := hexTrace_opposite hC hp c hw' hb
  have heq : c i = c (i + 3) :=
    commonNeighbors_subsingleton hC hww' ⟨ha, hb⟩ ⟨ha', hb'⟩
  have hfin : ∀ i : Fin 6, i ≠ i + 3 := by native_decide
  exact hfin i (c.injective heq)

/-- External vertices which meet the hexagon form an independent set. -/
theorem hexTrace_nonadjacent {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    {w w' : V} (hw : ∀ i, c i ≠ w) (hw' : ∀ i, c i ≠ w')
    (hne : ∃ i, G.Adj w (c i)) (hne' : ∃ i, G.Adj w' (c i)) :
    ¬ G.Adj w w' := by
  intro hedge
  obtain ⟨i, hi⟩ := hexTrace_antipodal hC hp c hw hne
  obtain ⟨j, hj⟩ := hexTrace_antipodal hC hp c hw' hne'
  have hfin : ∀ i j : Fin 6,
      (∃ a, (a = i ∨ a = i + 3) ∧ (a = j ∨ a = j + 3)) ∨
      (∃ a b, (a = i ∨ a = i + 3) ∧ (b = j ∨ b = j + 3) ∧
        (cycleGraph 6).Adj a b) := by native_decide
  rcases hfin i j with ⟨a, hai, haj⟩ | ⟨a, b, hai, hbj, hab⟩
  · exact hexTrace_disjoint hC hp c hw hw' hedge.ne a ⟨(hi a).2 hai, (hj a).2 haj⟩
  · exact hC (fourCycle_isContained ((hi a).2 hai) ((c.map_rel_iff).2 hab)
      ((hj b).2 hbj).symm hedge.symm (hw b).symm (hw' a))

/-- At most three vertices outside an induced hexagon can meet it.  This
bound applies even when there are additional vertices in the second layer. -/
theorem hexTrace_card_le_three {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (s : Set V) (hout : ∀ w ∈ s, ∀ i, c i ≠ w)
    (hmeet : ∀ w ∈ s, ∃ i, G.Adj w (c i)) : Nat.card s ≤ 3 := by
  classical
  have htrace : ∀ w : s, ∃ i : Fin 6,
      ∀ j, G.Adj w.val (c j) ↔ j = i ∨ j = i + 3 :=
    fun w => hexTrace_antipodal hC hp c (hout w.val w.property) (hmeet w.val w.property)
  choose idx hidx using htrace
  let label : s → Fin 3 := fun w => ⟨(idx w).val % 3, Nat.mod_lt _ (by decide)⟩
  have hlabel : Function.Injective label := by
    intro w w' heq
    by_contra hne
    have hmod : (idx w).val % 3 = (idx w').val % 3 := congrArg Fin.val heq
    have hfin : ∀ i j : Fin 6, i.val % 3 = j.val % 3 → i = j ∨ i = j + 3 := by
      native_decide
    have ha : G.Adj w.val (c (idx w)) := (hidx w _).2 (Or.inl rfl)
    have hb : G.Adj w'.val (c (idx w)) := (hidx w' _).2 (hfin _ _ hmod)
    exact hexTrace_disjoint hC hp c (hout w.val w.property) (hout w'.val w'.property)
      (fun h => hne (Subtype.ext h)) (idx w) ⟨ha, hb⟩
  simpa using Nat.card_le_card_of_injective label hlabel

/-- If a hexagon dominates and has an external neighbour, it has a cycle
vertex of eccentricity at most two. -/
theorem hexTrace_eccent_le_two {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i))
    {w : V} (hw : ∀ i, c i ≠ w) : ∃ i : Fin 6, G.eccent (c i) ≤ 2 := by
  classical
  obtain ⟨i, hi⟩ := hdom w
  have hwi : G.Adj w (c i) := hi.resolve_left (hw i).symm
  have hwopp := hexTrace_opposite hC hp c hw hwi
  have hcycle : ∀ j : Fin 6, G.edist (c i) (c j) ≤ 2 := by
    intro j
    have hfin : ∀ i j : Fin 6,
        i = j ∨ (cycleGraph 6).Adj i j ∨ j = i + 3 ∨
        ∃ k, (cycleGraph 6).Adj i k ∧ (cycleGraph 6).Adj k j := by
      native_decide
    rcases hfin i j with h | h | h | ⟨k, ha, hb⟩
    · subst j; simp
    · exact ((c.map_rel_iff).2 h).toWalk.edist_le.trans (by simp)
    · subst j
      let p := hwi.symm.toWalk.append hwopp.toWalk
      exact p.edist_le.trans (by simp [p])
    · let p := ((c.map_rel_iff).2 ha).toWalk.append ((c.map_rel_iff).2 hb).toWalk
      exact p.edist_le.trans (by simp [p])
  refine ⟨i, ?_⟩
  rw [eccent_le_iff]
  intro v
  by_cases hv : ∃ j, c j = v
  · obtain ⟨j, rfl⟩ := hv
    exact hcycle j
  · have hvout : ∀ j, c j ≠ v := by simpa using hv
    obtain ⟨j, hj⟩ := hdom v
    have hvj : G.Adj v (c j) := hj.resolve_left (hvout j).symm
    obtain ⟨a, ha⟩ := hexTrace_antipodal hC hp c hvout ⟨j, hvj⟩
    have hfin : ∀ i a : Fin 6, ∃ b,
        (b = a ∨ b = a + 3) ∧ (i = b ∨ (cycleGraph 6).Adj i b) := by
      native_decide
    obtain ⟨b, hba, hib⟩ := hfin i a
    have hbc : G.Adj (c b) v := ((ha b).2 hba).symm
    rcases hib with h | h
    · subst b
      exact hbc.toWalk.edist_le.trans (by simp)
    · let p := ((c.map_rel_iff).2 h).toWalk.append hbc.toWalk
      exact p.edist_le.trans (by simp [p])

end InducedPaths
