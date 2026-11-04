/-
Local pentagon branch of Theorem 3.6. Finite certificates below enumerate
Boolean traces and carry actual induced-path witnesses, not graph counts.
-/
module

public import InducedPaths.Basic
public meta import Mathlib.Data.Fintype.Defs
public meta import Mathlib.Combinatorics.SimpleGraph.CycleGraph

open scoped SimpleGraph
open SimpleGraph

@[expose] public section
namespace InducedPaths

/-- A nonempty trace avoiding distance-two pairs is a singleton or a cycle edge. -/
theorem pentTrace_certificate : ∀ t : Fin 5 → Bool,
    (∃ i, t i = true) →
    (∀ i, ¬ (t i = true ∧ t (i + 2) = true)) →
    (∃ i, ∀ j, t j = true ↔ j = i) ∨
    (∃ i, ∀ j, t j = true ↔ j = i ∨ j = i + 1) := by
  native_decide

/-- Strong `C₄`-freeness forbids distance-two contacts on an induced pentagon. -/
theorem pentTrace_no_distance_two {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 5 ↪g G) {w : V}
    (hw : ∀ i, c i ≠ w) (i : Fin 5) :
    ¬ (G.Adj w (c i) ∧ G.Adj w (c (i + 2))) := by
  rintro ⟨h₁, h₂⟩
  have hcycle : ∀ i : Fin 5,
      (cycleGraph 5).Adj i (i + 1) ∧
      (cycleGraph 5).Adj (i + 1) (i + 2) ∧ i ≠ i + 2 := by native_decide
  obtain ⟨ha, hb, hne⟩ := hcycle i
  exact hC (fourCycle_isContained h₁ ((c.map_rel_iff).2 ha) ((c.map_rel_iff).2 hb)
    h₂.symm (hw (i + 1)).symm (fun h => hne (c.injective h)))

/-- Classification does not require `P₆`-freeness or absence of an induced `C₆`. -/
theorem pentTrace_singleton_or_pair {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 5 ↪g G) {w : V}
    (hw : ∀ i, c i ≠ w) (hne : ∃ i, G.Adj w (c i)) :
    (∃ i : Fin 5, ∀ j, G.Adj w (c j) ↔ j = i) ∨
    (∃ i : Fin 5, ∀ j, G.Adj w (c j) ↔ j = i ∨ j = i + 1) := by
  classical
  let t : Fin 5 → Bool := fun i => decide (G.Adj w (c i))
  have ht : ∃ i, t i = true := by simpa [t] using hne
  have htwo : ∀ i, ¬ (t i = true ∧ t (i + 2) = true) := by
    simpa [t] using pentTrace_no_distance_two hC c hw
  simpa [t] using pentTrace_certificate t ht htwo

/-- The seven-vertex local model: `none` is the second-layer vertex,
`some none` its first-layer neighbour, and `some (some i)` the cycle. -/
def pentLayerAdj (t : Fin 5 → Bool) :
    Option (Option (Fin 5)) → Option (Option (Fin 5)) → Prop
  | none, none => False
  | none, some none => True
  | some none, none => True
  | none, some (some _) => False
  | some (some _), none => False
  | some none, some none => False
  | some none, some (some j) => t j = true
  | some (some i), some none => t i = true
  | some (some i), some (some j) => (cycleGraph 5).Adj i j

instance (t : Fin 5 → Bool) : DecidableRel (pentLayerAdj t) := fun a b => by
  cases a with
  | none => cases b with
    | none => unfold pentLayerAdj; infer_instance
    | some b => cases b <;> unfold pentLayerAdj <;> infer_instance
  | some a => cases a <;> cases b with
    | none => unfold pentLayerAdj; infer_instance
    | some b => cases b <;> unfold pentLayerAdj <;> infer_instance

/-- Two outside vertices followed by four consecutive cycle vertices, in
one of the two orientations. -/
def pentLayerPath (start : Fin 5) (reverse : Bool) (k : Fin 6) :
    Option (Option (Fin 5)) :=
  if k = 0 then none else if k = 1 then some none else
    some (some (if reverse then start - (⟨k.val - 2, by omega⟩ : Fin 5)
      else start + (⟨k.val - 2, by omega⟩ : Fin 5)))

/-- The local path certificate checks all 32 possible pentagon traces. -/
theorem pentLayer_certificate : ∀ t : Fin 5 → Bool,
    (∃ i, t i = true) →
    (∀ i, ¬ (t i = true ∧ t (i + 2) = true)) →
    ∃ start reverse, Function.Injective (pentLayerPath start reverse) ∧
      ∀ a b, pentLayerAdj t (pentLayerPath start reverse a)
        (pentLayerPath start reverse b) ↔ (pathGraph 6).Adj a b := by
  native_decide

/-- A vertex missing the pentagon cannot meet a vertex which meets it.
This is the local obstruction proving domination in connected graphs. -/
theorem pentTrace_no_second_layer {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 5 ↪g G)
    {a x : V} (ha : ∀ i, c i ≠ a) (hx : ∀ i, ¬ G.Adj x (c i))
    (hax : G.Adj a x) (hmeet : ∃ i, G.Adj a (c i)) : False := by
  classical
  let t : Fin 5 → Bool := fun i => decide (G.Adj a (c i))
  have ht : ∃ i, t i = true := by simpa [t] using hmeet
  have htwo : ∀ i, ¬ (t i = true ∧ t (i + 2) = true) := by
    simpa [t] using pentTrace_no_distance_two hC c ha
  obtain ⟨start, reverse, hinj, hpath⟩ := pentLayer_certificate t ht htwo
  have hnext : ∀ i : Fin 5, (cycleGraph 5).Adj i (i + 1) := by native_decide
  have hxc : ∀ i, c i ≠ x := by
    intro i heq
    apply hx (i + 1)
    rw [← heq]
    exact (c.map_rel_iff).2 (hnext i)
  let f : Option (Option (Fin 5)) → V := fun v => v.elim x (fun v => v.elim a c)
  have hf : Function.Injective f := by
    intro u v huv
    cases u with
    | none => cases v with
      | none => rfl
      | some v => cases v with
        | none => exact False.elim (hax.ne huv.symm)
        | some j => exact False.elim (hxc j huv.symm)
    | some u => cases u with
      | none => cases v with
        | none => exact False.elim (hax.ne huv)
        | some v => cases v with
          | none => rfl
          | some j => exact False.elim (ha j huv.symm)
      | some i => cases v with
        | none => exact False.elim (hxc i huv)
        | some v => cases v with
          | none => exact False.elim (ha i huv)
          | some j => exact congrArg (some ∘ some) (c.injective huv)
  have hadj : ∀ u v, G.Adj (f u) (f v) ↔ pentLayerAdj t u v := by
    intro u v
    cases u with
    | none => cases v with
      | none => simp [f, pentLayerAdj]
      | some v => cases v <;> simp [f, pentLayerAdj, hax.symm, hx]
    | some u => cases u <;> cases v with
      | none => simp [f, pentLayerAdj, hax, hx, adj_comm]
      | some v => cases v <;> simp [f, pentLayerAdj, t, adj_comm]
  apply hp
  exact ⟨{
    toEmbedding := ⟨f ∘ pentLayerPath start reverse, hf.comp hinj⟩
    map_rel_iff' := by intro u v; exact (hadj _ _).trans (hpath u v)
  }⟩

/-- Every induced pentagon dominates a connected strong `C₄`-free,
`P₆`-free graph, with no finiteness assumption. -/
theorem pentTrace_dominates {V : Type*} {G : SimpleGraph V}
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 5 ↪g G) :
    ∀ v, ∃ i, v = c i ∨ G.Adj v (c i) := by
  classical
  intro v
  have hr := (reachable_iff_reflTransGen (c 0) v).1 (hconn (c 0) v)
  induction hr with
  | refl => exact ⟨0, Or.inl rfl⟩
  | @tail w u rest hadj ih =>
    have hadj := hadj.symm
    by_cases hu : ∃ i, u = c i
    · obtain ⟨i, hi⟩ := hu; exact ⟨i, Or.inl hi⟩
    by_cases humeet : ∃ i, G.Adj u (c i)
    · obtain ⟨i, hi⟩ := humeet; exact ⟨i, Or.inr hi⟩
    exfalso
    obtain ⟨i, hi | hi⟩ := ih
    · exact humeet ⟨i, hi ▸ hadj⟩
    · have hw : ∀ j, c j ≠ w := by
        intro j heq
        exact humeet ⟨j, heq ▸ hadj⟩
      exact pentTrace_no_second_layer hC hp c hw
        (by simpa using humeet) hadj.symm ⟨i, hi⟩

/-- The local trace classification in the notation of the cited
Karthick–Maffray theorem. -/
theorem pentTrace_mem_kmW_or_kmX {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 5 ↪g G) {w : V}
    (hw : w ∈ outsideCycle c) (hne : ∃ i, G.Adj w (c i)) :
    (∃ i, w ∈ kmW G c i) ∨ (∃ i, w ∈ kmX G c i) := by
  rcases pentTrace_singleton_or_pair hC c hw hne with ⟨i, hi⟩ | ⟨i, hi⟩
  · left; refine ⟨i, hw, ?_⟩; ext j; simpa [cycleTrace] using hi j
  · right; refine ⟨i, hw, ?_⟩; ext j; simpa [cycleTrace] using hi j

/-- Each consecutive-pair class has at most one vertex. -/
theorem pentTrace_pair_subsingleton {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 5 ↪g G) (i : Fin 5) :
    (kmX G c i).Subsingleton := by
  intro a ha b hb
  by_contra hab
  have htracea : ∀ j, G.Adj a (c j) ↔ j = i ∨ j = i + 1 := by
    intro j; have := Set.ext_iff.mp ha.2 j; simpa [cycleTrace] using this
  have htraceb : ∀ j, G.Adj b (c j) ↔ j = i ∨ j = i + 1 := by
    intro j; have := Set.ext_iff.mp hb.2 j; simpa [cycleTrace] using this
  have heq := commonNeighbors_subsingleton hC hab
    ⟨(htracea i).2 (Or.inl rfl), (htraceb i).2 (Or.inl rfl)⟩
    ⟨(htracea (i + 1)).2 (Or.inr rfl), (htraceb (i + 1)).2 (Or.inr rfl)⟩
  have hfin : ∀ i : Fin 5, i ≠ i + 1 := by native_decide
  exact hfin i (c.injective heq)

/-- At most five vertices have consecutive-pair traces. -/
theorem pentTrace_pair_card_le_five {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 5 ↪g G) :
    Nat.card {w : V // ∃ i, w ∈ kmX G c i} ≤ 5 := by
  classical
  let idx : {w : V // ∃ i, w ∈ kmX G c i} → Fin 5 :=
    fun w => Classical.choose w.property
  have hi : ∀ w, w.val ∈ kmX G c (idx w) := fun w => Classical.choose_spec w.property
  have hinj : Function.Injective idx := by
    intro w w' heq
    apply Subtype.ext
    exact pentTrace_pair_subsingleton hC c (idx w) (hi w) (heq.symm ▸ hi w')
  simpa using Nat.card_le_card_of_injective idx hinj

/-- Pair-trace vertices form an independent set. -/
theorem pentTrace_pair_nonadjacent {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 5 ↪g G) {a b : V} {i j : Fin 5}
    (ha : a ∈ kmX G c i) (hb : b ∈ kmX G c j) : ¬ G.Adj a b := by
  intro hab
  have htracea : ∀ k, G.Adj a (c k) ↔ k = i ∨ k = i + 1 := by
    intro k; have := Set.ext_iff.mp ha.2 k; simpa [cycleTrace] using this
  have htraceb : ∀ k, G.Adj b (c k) ↔ k = j ∨ k = j + 1 := by
    intro k; have := Set.ext_iff.mp hb.2 k; simpa [cycleTrace] using this
  have hfin : ∀ i j : Fin 5, ∃ k l,
      (k = i ∨ k = i + 1) ∧ (l = j ∨ l = j + 1) ∧
      (cycleGraph 5).Adj k l := by native_decide
  obtain ⟨k, l, hk, hl, hkl⟩ := hfin i j
  exact hC (fourCycle_isContained ((htracea k).2 hk) ((c.map_rel_iff).2 hkl)
    ((htraceb l).2 hl).symm hab.symm (ha.1 l).symm (hb.1 k))

/-- A singleton--pair edge can use only the opposite cycle edge. -/
theorem pentTrace_singleton_pair_opposite {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 5 ↪g G) {a b : V} {i j : Fin 5}
    (ha : a ∈ kmW G c i) (hb : b ∈ kmX G c j) (hab : G.Adj a b) :
    j = i + 2 := by
  have hai : G.Adj a (c i) := by
    have := Set.ext_iff.mp ha.2 i; simpa [cycleTrace] using this.mpr (by simp)
  have htraceb : ∀ k, G.Adj b (c k) ↔ k = j ∨ k = j + 1 := by
    intro k; have := Set.ext_iff.mp hb.2 k; simpa [cycleTrace] using this
  have hfin : ∀ i j : Fin 5, j ≠ i + 2 → ∃ k,
      (k = j ∨ k = j + 1) ∧ (cycleGraph 5).Adj i k := by native_decide
  by_contra hne
  obtain ⟨k, hk, hik⟩ := hfin i j hne
  exact hC (fourCycle_isContained hai ((c.map_rel_iff).2 hik)
    ((htraceb k).2 hk).symm hab.symm (ha.1 k).symm (hb.1 i))

/-- The Karthick–Maffray emptiness conclusions force every singleton--pair
edge to have the same singleton support. -/
theorem pentTrace_cross_support_unique {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (hc6 : ¬ cycleGraph 6 ⊴ G)
    (c : cycleGraph 5 ↪g G) {a b a' b' : V} {i j i' j' : Fin 5}
    (ha : a ∈ kmW G c i) (hb : b ∈ kmX G c j) (hab : G.Adj a b)
    (ha' : a' ∈ kmW G c i') (hb' : b' ∈ kmX G c j') (hab' : G.Adj a' b') :
    i = i' := by
  have hj := pentTrace_singleton_pair_opposite hC c ha hb hab
  have hj' := pentTrace_singleton_pair_opposite hC c ha' hb' hab'
  subst j; subst j'
  have hkm := karthick_maffray_C5 G hp (strongC4Free_no_induced_C4 hC) hc6 c
  have hW : ∀ r s : Fin 5, s = r + 2 →
      ∀ x ∈ kmW G c r, ∀ y ∈ kmW G c s, False := by
    intro r s hrs x hx y hy
    subst s
    rcases (hkm r).2.1 with he | he
    · simp [he] at hx
    · simp [he] at hy
  have hX : ∀ r s : Fin 5, s = r + 1 →
      ∀ x ∈ kmX G c r, ∀ y ∈ kmX G c s, False := by
    intro r s hrs x hx y hy
    subst s
    rcases (hkm r).1 with he | he
    · simp [he] at hx
    · simp [he] at hy
  have hfin : ∀ i k : Fin 5, i ≠ k →
      k = i + 2 ∨ i = k + 2 ∨
      k + 2 = (i + 2) + 1 ∨ i + 2 = (k + 2) + 1 := by native_decide
  by_contra hne
  rcases hfin i i' hne with h | h | h | h
  · exact hW i i' h a ha a' ha'
  · exact hW i' i h a' ha' a ha
  · exact hX (i + 2) (i' + 2) h b hb b' hb'
  · exact hX (i' + 2) (i + 2) h b' hb' b hb

/-- There is at most one singleton--pair edge (with the singleton endpoint
first). This is the structural assertion `b ≤ 1` in the pentagon branch. -/
theorem pentTrace_cross_edge_unique {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (hc6 : ¬ cycleGraph 6 ⊴ G)
    (c : cycleGraph 5 ↪g G) {a b a' b' : V} {i j i' j' : Fin 5}
    (ha : a ∈ kmW G c i) (hb : b ∈ kmX G c j) (hab : G.Adj a b)
    (ha' : a' ∈ kmW G c i') (hb' : b' ∈ kmX G c j') (hab' : G.Adj a' b') :
    a = a' ∧ b = b' := by
  have hi := pentTrace_cross_support_unique hC hp hc6 c ha hb hab ha' hb' hab'
  have hj := pentTrace_singleton_pair_opposite hC c ha hb hab
  have hj' := pentTrace_singleton_pair_opposite hC c ha' hb' hab'
  subst i'; subst j; subst j'
  have hbb := pentTrace_pair_subsingleton hC c (i + 2) hb hb'
  subst b'
  have hai : G.Adj a (c i) := by
    have := Set.ext_iff.mp ha.2 i; simpa [cycleTrace] using this.mpr (by simp)
  have hai' : G.Adj a' (c i) := by
    have := Set.ext_iff.mp ha'.2 i; simpa [cycleTrace] using this.mpr (by simp)
  exact ⟨commonNeighbors_subsingleton hC (hb.1 i).symm
    ⟨hab.symm, hai.symm⟩ ⟨hab'.symm, hai'.symm⟩, rfl⟩

/-- Local model for two adjacent singleton vertices and their pentagon. -/
def pentSingletonAdj (i j : Fin 5) :
    Option (Option (Fin 5)) → Option (Option (Fin 5)) → Prop
  | none, some (some k) => k = j
  | some (some k), none => k = j
  | u, v => pentLayerAdj (fun k => decide (k = i)) u v

instance (i j : Fin 5) : DecidableRel (pentSingletonAdj i j) := fun a b => by
  cases a with
  | none => cases b with
    | none => unfold pentSingletonAdj; infer_instance
    | some b => cases b <;> unfold pentSingletonAdj <;> infer_instance
  | some a => cases a <;> cases b with
    | none => unfold pentSingletonAdj; infer_instance
    | some b => cases b <;> unfold pentSingletonAdj <;> infer_instance

/-- Distance-two singleton supports joined by an edge give an actual induced
hexagon, using the longer pentagon arc. -/
theorem pentSingleton_cycle_certificate : ∀ i j : Fin 5,
    i ≠ j → ¬ (cycleGraph 5).Adj i j →
    ∃ start reverse, Function.Injective (pentLayerPath start reverse) ∧
      ∀ a b, pentSingletonAdj i j (pentLayerPath start reverse a)
        (pentLayerPath start reverse b) ↔ (cycleGraph 6).Adj a b := by
  native_decide

/-- Singleton vertices with distinct cycle supports cannot be adjacent in
the no-induced-hexagon branch. -/
theorem pentTrace_singleton_nonadjacent {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (hc6 : ¬ cycleGraph 6 ⊴ G)
    (c : cycleGraph 5 ↪g G) {a b : V} {i j : Fin 5}
    (ha : a ∈ kmW G c i) (hb : b ∈ kmW G c j) (hij : i ≠ j) :
    ¬ G.Adj a b := by
  classical
  intro hab
  have hta : ∀ k, G.Adj a (c k) ↔ k = i := by
    intro k; have := Set.ext_iff.mp ha.2 k; simpa [cycleTrace] using this
  have htb : ∀ k, G.Adj b (c k) ↔ k = j := by
    intro k; have := Set.ext_iff.mp hb.2 k; simpa [cycleTrace] using this
  have hnc : ¬ (cycleGraph 5).Adj i j := by
    intro hadj
    exact hC (fourCycle_isContained ((hta i).2 rfl) ((c.map_rel_iff).2 hadj)
      ((htb j).2 rfl).symm hab.symm (ha.1 j).symm (hb.1 i))
  obtain ⟨start, reverse, hinj, hcycle⟩ := pentSingleton_cycle_certificate i j hij hnc
  let f : Option (Option (Fin 5)) → V := fun v => v.elim b (fun v => v.elim a c)
  have hf : Function.Injective f := by
    intro u v huv
    cases u with
    | none => cases v with
      | none => rfl
      | some v => cases v with
        | none => exact False.elim (hab.ne huv.symm)
        | some k => exact False.elim (hb.1 k huv.symm)
    | some u => cases u with
      | none => cases v with
        | none => exact False.elim (hab.ne huv)
        | some v => cases v with
          | none => rfl
          | some k => exact False.elim (ha.1 k huv.symm)
      | some k => cases v with
        | none => exact False.elim (hb.1 k huv)
        | some v => cases v with
          | none => exact False.elim (ha.1 k huv)
          | some l => exact congrArg (some ∘ some) (c.injective huv)
  have hadj : ∀ u v, G.Adj (f u) (f v) ↔ pentSingletonAdj i j u v := by
    intro u v
    cases u with
    | none => cases v with
      | none => simp [f, pentSingletonAdj, pentLayerAdj]
      | some v => cases v <;>
          simp [f, pentSingletonAdj, pentLayerAdj, hab.symm, htb]
    | some u => cases u <;> cases v with
      | none => simp [f, pentSingletonAdj, pentLayerAdj, hab, htb, adj_comm]
      | some v => cases v <;>
          simp [f, pentSingletonAdj, pentLayerAdj, hta, adj_comm]
  apply hc6
  exact ⟨{
    toEmbedding := ⟨f ∘ pentLayerPath start reverse, hf.comp hinj⟩
    map_rel_iff' := by intro u v; exact (hadj _ _).trans (hcycle u v)
  }⟩

/-- Within a singleton class, each vertex has at most one neighbour in that
class: its edges therefore form a matching. -/
theorem pentTrace_singleton_matching {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 5 ↪g G) {a b d : V} {i : Fin 5}
    (ha : a ∈ kmW G c i) (hb : b ∈ kmW G c i) (hd : d ∈ kmW G c i)
    (hab : G.Adj a b) (had : G.Adj a d) : b = d := by
  have hbi : G.Adj b (c i) := by
    have := Set.ext_iff.mp hb.2 i; simpa [cycleTrace] using this.mpr (by simp)
  have hdi : G.Adj d (c i) := by
    have := Set.ext_iff.mp hd.2 i; simpa [cycleTrace] using this.mpr (by simp)
  exact commonNeighbors_subsingleton hC (ha.1 i).symm
    ⟨hab, hbi.symm⟩ ⟨had, hdi.symm⟩

end InducedPaths
