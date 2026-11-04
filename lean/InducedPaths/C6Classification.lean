module

public import InducedPaths.C6Layers
public import InducedPaths.C6Mass
public import InducedPaths.Graphs
public import InducedPaths.CanonicalMass
public meta import InducedPaths.Graphs

open scoped SimpleGraph
open Finset SimpleGraph

@[expose] public section
namespace InducedPaths

variable {V : Type*} {G : SimpleGraph V}

/-- The first distance layer of the designated hexagon. -/
def hexFirst (c : cycleGraph 6 ↪g G) : Set V :=
  {v | (∀ i, c i ≠ v) ∧ ∃ i, G.Adj v (c i)}

/-- Vertices outside the hexagon with empty trace. In the connected case these
are exactly the second distance layer. -/
def hexSecond (c : cycleGraph 6 ↪g G) : Set V :=
  {v | (∀ i, c i ≠ v) ∧ ∀ i, ¬ G.Adj v (c i)}

theorem hexFirst_independent (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a b : hexFirst c) : ¬ G.Adj a.val b.val :=
  hexTrace_nonadjacent hC hp c a.property.1 b.property.1 a.property.2 b.property.2

theorem hexFirst_card_le_three (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) : Nat.card (hexFirst c) ≤ 3 :=
  hexTrace_card_le_three hC hp c (hexFirst c) (fun _ h => h.1) (fun _ h => h.2)

theorem hexSecond_complete (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (x : hexSecond c) (a : hexFirst c) : G.Adj x.val a.val := by
  obtain h | h | ⟨b, hb, hmb, hxb⟩ := hexTrace_two_layers hconn hC hp c x.val
  · obtain ⟨i, hi⟩ := h; exact False.elim (x.property.1 i hi.symm)
  · obtain ⟨i, hi⟩ := h; exact False.elim (x.property.2 i hi)
  · exact hexTrace_second_layer_complete hC hp c hb a.property.1 hmb a.property.2
      x.property.2 hxb

/-- Every vertex belongs to exactly one of the cycle and its two layers. -/
noncomputable def hexLayerPartition (c : cycleGraph 6 ↪g G) :
    Fin 6 ⊕ (hexFirst c ⊕ hexSecond c) ≃ V :=
  Equiv.ofBijective (Sum.elim c (Sum.elim Subtype.val Subtype.val)) (by
    classical
    constructor
    · intro u v huv
      cases u with
      | inl i =>
        cases v with
        | inl j => exact congrArg Sum.inl (c.injective huv)
        | inr v =>
          cases v with
          | inl a => exact False.elim (a.property.1 i huv)
          | inr x => exact False.elim (x.property.1 i huv)
      | inr u =>
        cases v with
        | inl j =>
          cases u with
          | inl a => exact False.elim (a.property.1 j huv.symm)
          | inr x => exact False.elim (x.property.1 j huv.symm)
        | inr v =>
          cases u with
          | inl a =>
            cases v with
            | inl b => exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext huv)
            | inr x =>
              obtain ⟨i, hi⟩ := a.property.2
              change a.val = x.val at huv
              exact False.elim (x.property.2 i (huv ▸ hi))
          | inr x =>
            cases v with
            | inl a =>
              obtain ⟨i, hi⟩ := a.property.2
              change x.val = a.val at huv
              exact False.elim (x.property.2 i (huv.symm ▸ hi))
            | inr y => exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext huv)
    · intro v
      by_cases hc : ∃ i, c i = v
      · obtain ⟨i, rfl⟩ := hc; exact ⟨Sum.inl i, rfl⟩
      · have ho : ∀ i, c i ≠ v := by simpa using hc
        by_cases hm : ∃ i, G.Adj v (c i)
        · exact ⟨Sum.inr (Sum.inl ⟨v, ho, hm⟩), rfl⟩
        · exact ⟨Sum.inr (Sum.inr ⟨v, ho, by simpa using hm⟩), rfl⟩)

theorem hexLayer_card [Fintype V] (c : cycleGraph 6 ↪g G) :
    Fintype.card V = 6 + Nat.card (hexFirst c) + Nat.card (hexSecond c) := by
  classical
  have := Fintype.card_congr (hexLayerPartition c)
  simpa only [Fintype.card_sum, Fintype.card_fin, Nat.card_eq_fintype_card,
    Nat.add_assoc] using this.symm

/-- Two distinct first-layer vertices force the entire second layer to have
at most one vertex. -/
theorem hexSecond_subsingleton (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (a b : hexFirst c) (hab : a ≠ b) : (hexSecond c).Subsingleton := by
  intro x hx y hy
  have hne : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  exact commonNeighbors_subsingleton hC hne
    ⟨(hexSecond_complete hconn hC hp c ⟨x, hx⟩ a).symm,
     (hexSecond_complete hconn hC hp c ⟨x, hx⟩ b).symm⟩
    ⟨(hexSecond_complete hconn hC hp c ⟨y, hy⟩ a).symm,
     (hexSecond_complete hconn hC hp c ⟨y, hy⟩ b).symm⟩

/-- Every vertex of the second layer has at most one neighbour within that
layer: this is the matching assertion in the one-apex case. -/
theorem hexSecond_matching (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (a : hexFirst c) (x y z : hexSecond c)
    (hxy : G.Adj x.val y.val) (hxz : G.Adj x.val z.val) : y = z := by
  apply Subtype.ext
  have hxa : x.val ≠ a.val := by
    obtain ⟨i, hi⟩ := a.property.2
    intro h
    exact x.property.2 i (h.symm ▸ hi)
  exact commonNeighbors_subsingleton hC hxa
    ⟨hxy, hexSecond_complete hconn hC hp c y a |>.symm⟩
    ⟨hxz, hexSecond_complete hconn hC hp c z a |>.symm⟩

/-- A nonempty first layer is forced whenever the second layer is nonempty. -/
theorem hexSecond_first_nonempty (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G) (x : hexSecond c) :
    Nonempty (hexFirst c) := by
  obtain h | h | ⟨a, ha, hma, _⟩ := hexTrace_two_layers hconn hC hp c x.val
  · obtain ⟨i, hi⟩ := h; exact False.elim (x.property.1 i hi.symm)
  · obtain ⟨i, hi⟩ := h; exact False.elim (x.property.2 i hi)
  · exact ⟨⟨a, ha, hma⟩⟩

private theorem hexLayer_sum [Fintype V] (c : cycleGraph 6 ↪g G)
    [Fintype (hexFirst c)] [Fintype (hexSecond c)] (f : V → ℕ) :
    (∑ v, f v) = (∑ i : Fin 6, f (c i)) +
      (∑ a : hexFirst c, f a.val) + ∑ x : hexSecond c, f x.val := by
  classical
  rw [← Fintype.sum_equiv (hexLayerPartition c)
    (fun x => f (hexLayerPartition c x)) f (fun _ => rfl),
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  exact (Nat.add_assoc _ _ _).symm

/-- The second layer is independent as soon as the first layer has two vertices. -/
theorem hexSecond_independent (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (a b : hexFirst c) (hab : a ≠ b) (x y : hexSecond c) :
    ¬ G.Adj x.val y.val := by
  have h := hexSecond_subsingleton hconn hC hp c a b hab x.property y.property
  exact fun hxy => hxy.ne h

/-- The sum of degrees is exact in the two-or-three-apex branch. -/
theorem hexMulti_degree_sum [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a b : hexFirst c) (hab : a ≠ b) :
    (∑ v, G.degree v) = 12 + 4 * Nat.card (hexFirst c) +
      2 * Nat.card (hexFirst c) * Nat.card (hexSecond c) := by
  classical
  have hdeg (v : V) : G.degree v =
      (∑ i : Fin 6, if G.Adj v (c i) then 1 else 0) +
      (∑ a : hexFirst c, if G.Adj v a.val then 1 else 0) +
      ∑ x : hexSecond c, if G.Adj v x.val then 1 else 0 := by
    have hv : G.degree v = ∑ x : V, if G.Adj v x then 1 else 0 := by
      simpa only [Finset.sum_boole, Nat.cast_id, ← G.neighborFinset_eq_filter] using
        (G.card_neighborFinset_eq_degree v).symm
    rw [hv, hexLayer_sum c]
  have htrace (w : hexFirst c) :
      (∑ i : Fin 6, if G.Adj w.val (c i) then 1 else 0) = 2 := by
    obtain ⟨k, hk⟩ := hexTrace_antipodal hC hp c w.property.1 w.property.2
    simp_rw [hk]
    have hf : ∀ k : Fin 6, (∑ i : Fin 6, if i = k ∨ i = k + 3 then 1 else 0) = 2 := by
      native_decide
    exact hf k
  have hcdeg (i : Fin 6) :
      (∑ j : Fin 6, if G.Adj (c i) (c j) then 1 else 0) = 2 := by
    simp_rw [c.map_rel_iff]
    have hf : ∀ i : Fin 6,
        (∑ j : Fin 6, if (cycleGraph 6).Adj i j then 1 else 0) = 2 := by native_decide
    exact hf i
  have hfirst (w : hexFirst c) : G.degree w.val = 2 + Fintype.card (hexSecond c) := by
    rw [hdeg, htrace]
    simp [hexFirst_independent hC hp c, fun x => (hexSecond_complete hconn hC hp c x w).symm]
  have hsecond (x : hexSecond c) : G.degree x.val = Fintype.card (hexFirst c) := by
    rw [hdeg]
    simp [x.property.2, hexSecond_complete hconn hC hp c,
      hexSecond_independent hconn hC hp c a b hab]
  have hcycle : (∑ i : Fin 6, G.degree (c i)) = 12 + 2 * Fintype.card (hexFirst c) := by
    simp_rw [hdeg, hcdeg]
    have hnone (i : Fin 6) (x : hexSecond c) : ¬ G.Adj (c i) x.val :=
      fun h => x.property.2 i h.symm
    simp_rw [if_neg (hnone _ _)]
    simp only [Finset.sum_const_zero, Nat.add_zero]
    rw [Finset.sum_add_distrib, Finset.sum_comm]
    have ht (w : hexFirst c) :
        (∑ i : Fin 6, if G.Adj (c i) w.val then 1 else 0) = 2 := by
      simpa only [G.adj_comm] using htrace w
    simp_rw [ht]
    simp [Nat.mul_comm]
  rw [hexLayer_sum c, hcycle]
  simp_rw [hfirst, hsecond]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  ring

/-- No triangles occur in the branch with at least two first-layer vertices. -/
theorem hexMulti_no_triangle (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (a b : hexFirst c) (hab : a ≠ b) :
    ∀ u v w, G.Adj u v → G.Adj v w → ¬ G.Adj u w := by
  classical
  have hc : ∀ i j k : Fin 6, (cycleGraph 6).Adj i j →
      (cycleGraph 6).Adj j k → ¬ (cycleGraph 6).Adj i k := by native_decide
  have he (w : hexFirst c) (i j : Fin 6) (hij : (cycleGraph 6).Adj i j) :
      ¬ (G.Adj w.val (c i) ∧ G.Adj w.val (c j)) := by
    obtain ⟨k, hk⟩ := hexTrace_antipodal hC hp c w.property.1 w.property.2
    have hf : ∀ i j k : Fin 6, (cycleGraph 6).Adj i j →
        ¬ ((i = k ∨ i = k + 3) ∧ (j = k ∨ j = k + 3)) := by native_decide
    rintro ⟨hi, hj⟩
    exact hf i j k hij ⟨(hk i).1 hi, (hk j).1 hj⟩
  have hn (i : Fin 6) (x : hexSecond c) : ¬ G.Adj (c i) x.val :=
    fun h => x.property.2 i h.symm
  intro u v w huv hvw huw
  obtain ⟨u, rfl⟩ := (hexLayerPartition c).surjective u
  obtain ⟨v, rfl⟩ := (hexLayerPartition c).surjective v
  obtain ⟨w, rfl⟩ := (hexLayerPartition c).surjective w
  rcases u with i | u <;> try rcases u with u | u
  all_goals rcases v with j | v <;> try rcases v with v | v
  all_goals rcases w with k | w <;> try rcases w with w | w
  all_goals change G.Adj _ _ at huv hvw huw
  all_goals first
    | exact hc _ _ _ ((c.map_rel_iff).1 huv) ((c.map_rel_iff).1 hvw) ((c.map_rel_iff).1 huw)
    | exact he _ _ _ ((c.map_rel_iff).1 huv) ⟨huw.symm, hvw.symm⟩
    | exact he _ _ _ ((c.map_rel_iff).1 hvw) ⟨huv, huw⟩
    | exact he _ _ _ ((c.map_rel_iff).1 huw) ⟨huv.symm, hvw⟩
    | exact hexFirst_independent hC hp c _ _ huv
    | exact hexFirst_independent hC hp c _ _ hvw
    | exact hexFirst_independent hC hp c _ _ huw
    | exact hexSecond_independent hconn hC hp c a b hab _ _ huv
    | exact hexSecond_independent hconn hC hp c a b hab _ _ hvw
    | exact hexSecond_independent hconn hC hp c a b hab _ _ huw
    | exact hn _ _ huv
    | exact hn _ _ hvw
    | exact hn _ _ huw
    | exact hn _ _ huv.symm
    | exact hn _ _ hvw.symm
    | exact hn _ _ huw.symm

/-- Exact mass in the two-or-three-apex branch of Theorem 3.6. -/
theorem hexMulti_mass [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a b : hexFirst c) (hab : a ≠ b) :
    neighbourhoodIndependenceSum G = 12 + 4 * Nat.card (hexFirst c) +
      2 * Nat.card (hexFirst c) * Nat.card (hexSecond c) := by
  classical
  have hl (v : V) : lambda G v = G.degree v := by
    have he : (G.induce (G.neighborSet v)).edgeFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      have ha := adj_out_of_mem (G.induce (G.neighborSet v)) e he
      exact hexMulti_no_triangle hconn hC hp c a b hab v e.out.1.val e.out.2.val
        e.out.1.property ha e.out.2.property
    have ht : trianglesAt G v = 0 := by
      rw [trianglesAt_eq_neighborEdges, edgeCount, he, Finset.card_empty]
    have := lambda_add_trianglesAt hC v
    omega
  unfold neighbourhoodIndependenceSum
  simp_rw [hl]
  exact hexMulti_degree_sum hconn hC hp c a b hab

/-- The multi-apex branch has order at most ten, with exactly four possible
layer-size pairs, as in the table in the proof of Theorem 3.6. -/
theorem hexMulti_parameters [Fintype V]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a b : hexFirst c) (hab : a ≠ b) :
    (Nat.card (hexFirst c) = 2 ∨ Nat.card (hexFirst c) = 3) ∧
    Nat.card (hexSecond c) ≤ 1 ∧ Fintype.card V ≤ 10 := by
  classical
  have hk := hexFirst_card_le_three hC hp c
  have hk2 : 2 ≤ Nat.card (hexFirst c) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
  have hs := hexSecond_subsingleton hconn hC hp c a b hab
  letI : Subsingleton (hexSecond c) := ⟨fun x y => Subtype.ext (hs x.property y.property)⟩
  have hh : Nat.card (hexSecond c) ≤ 1 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
  have hn := hexLayer_card c
  omega

/-- The four exact rows of the mass table, without division. -/
theorem hexMulti_mass_table [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a b : hexFirst c) (hab : a ≠ b) :
    (Nat.card (hexFirst c) = 2 ∧ Nat.card (hexSecond c) = 0 ∧
      Fintype.card V = 8 ∧ neighbourhoodIndependenceSum G = 20) ∨
    (Nat.card (hexFirst c) = 2 ∧ Nat.card (hexSecond c) = 1 ∧
      Fintype.card V = 9 ∧ neighbourhoodIndependenceSum G = 24) ∨
    (Nat.card (hexFirst c) = 3 ∧ Nat.card (hexSecond c) = 0 ∧
      Fintype.card V = 9 ∧ neighbourhoodIndependenceSum G = 24) ∨
    (Nat.card (hexFirst c) = 3 ∧ Nat.card (hexSecond c) = 1 ∧
      Fintype.card V = 10 ∧ neighbourhoodIndependenceSum G = 30) := by
  obtain ⟨hk, hh, _⟩ := hexMulti_parameters hconn hC hp c a b hab
  have hn := hexLayer_card c
  have hm := hexMulti_mass hconn hC hp c a b hab
  have hh' : Nat.card (hexSecond c) = 0 ∨ Nat.card (hexSecond c) = 1 := by omega
  rcases hk with hk | hk <;> rcases hh' with hh' | hh' <;>
    rw [hk, hh'] at hm hn <;> simp_all

/-- The multi-apex branch satisfies the sharp global mass bound; equality
occurs precisely for the full three-apex, one-second-layer configuration. -/
theorem hexMulti_mass_le [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a b : hexFirst c) (hab : a ≠ b) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V ∧
    (neighbourhoodIndependenceSum G = 3 * Fintype.card V ↔
      Nat.card (hexFirst c) = 3 ∧ Nat.card (hexSecond c) = 1) := by
  rcases hexMulti_mass_table hconn hC hp c a b hab with h | h | h | h <;>
    rcases h with ⟨hk, hh, hn, hm⟩ <;> simp [hk, hh, hn, hm]

/-- With no first layer, connectedness forces the graph to be just the hexagon. -/
noncomputable def hexNoFirst_iso (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G) (ha : IsEmpty (hexFirst c)) :
    cycleGraph 6 ≃g G := by
  refine { Equiv.ofBijective c ⟨c.injective, ?_⟩ with map_rel_iff' := c.map_rel_iff }
  intro v
  obtain ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨a, ha', hma, _⟩ := hexTrace_two_layers hconn hC hp c v
  · exact ⟨i, hi.symm⟩
  · by_cases hv : ∃ j, c j = v
    · exact hv
    · exact (ha.false ⟨v, by simpa using hv, ⟨i, hi⟩⟩).elim
  · exact (ha.false ⟨a, ha', hma⟩).elim

/-- Each antipodal trace has a unique representative in `Fin 3`. -/
theorem hexFirst_index_exists (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a : hexFirst c) :
    ∃ j : Fin 3, ∀ i : Fin 6, G.Adj a.val (c i) ↔ i.val % 3 = j.val := by
  obtain ⟨k, hk⟩ := hexTrace_antipodal hC hp c a.property.1 a.property.2
  have hf : ∀ k : Fin 6, ∃ j : Fin 3, ∀ i : Fin 6,
      (i = k ∨ i = k + 3) ↔ i.val % 3 = j.val := by native_decide
  obtain ⟨j, hj⟩ := hf k
  exact ⟨j, fun i => (hk i).trans (hj i)⟩

noncomputable def hexFirstIndex (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a : hexFirst c) : Fin 3 :=
  (hexFirst_index_exists hC hp c a).choose

theorem hexFirstIndex_spec (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a : hexFirst c) (i : Fin 6) :
    G.Adj a.val (c i) ↔ i.val % 3 = (hexFirstIndex hC hp c a).val :=
  (hexFirst_index_exists hC hp c a).choose_spec i

theorem hexFirstIndex_injective (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) : Function.Injective (hexFirstIndex hC hp c) := by
  intro a b hab
  by_contra hn
  have hv : a.val ≠ b.val := fun h => hn (Subtype.ext h)
  let j := hexFirstIndex hC hp c a
  let i : Fin 6 := ⟨j.val, by omega⟩
  have hi : i.val % 3 = j.val := Nat.mod_eq_of_lt j.isLt
  have hia := (hexFirstIndex_spec hC hp c a i).2 hi
  have hib := (hexFirstIndex_spec hC hp c b i).2 (by simpa [← hab] using hi)
  exact hexTrace_disjoint hC hp c a.property.1 b.property.1 hv i ⟨hia, hib⟩

/-- If all three antipodal pairs are present, the first layer is canonically
indexed by the three pairs of the designated hexagon. -/
noncomputable def hexFirstEquiv [Fintype V] (hC : StrongC4Free G)
    (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (hk : Nat.card (hexFirst c) = 3) : hexFirst c ≃ Fin 3 := by
  classical
  exact Equiv.ofBijective (hexFirstIndex hC hp c)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨hexFirstIndex_injective hC hp c, by simpa only [Nat.card_eq_fintype_card,
        Fintype.card_fin] using hk⟩)

/-- Coordinates for the full Petersen configuration: cycle, apices, hub. -/
abbrev HexFullV := Fin 6 ⊕ (Fin 3 ⊕ Unit)

def hexFullGraph : SimpleGraph HexFullV := simpleOf fun
  | .inl i, .inl j => (cycleGraph 6).Adj i j
  | .inl i, .inr (.inl j) => i.val % 3 = j.val
  | .inr (.inl j), .inl i => i.val % 3 = j.val
  | .inr (.inl _), .inr (.inr _) => True
  | .inr (.inr _), .inr (.inl _) => True
  | _, _ => False

instance : DecidableRel hexFullGraph.Adj := by
  intro a b
  rcases a with i | a <;> try rcases a with a | x
  all_goals rcases b with j | b <;> try rcases b with b | y
  all_goals unfold hexFullGraph simpleOf
  all_goals dsimp
  all_goals infer_instance

/-- Explicit Kneser coordinates for the full hexagon configuration. -/
def hexFullPetersenMap : HexFullV → PetersenVertex
  | .inl i => (![⟨{0,2}, by decide⟩, ⟨{1,3}, by decide⟩,
      ⟨{0,4}, by decide⟩, ⟨{1,2}, by decide⟩,
      ⟨{0,3}, by decide⟩, ⟨{1,4}, by decide⟩] : Fin 6 → PetersenVertex) i
  | .inr (.inl j) => (![⟨{3,4}, by decide⟩, ⟨{2,4}, by decide⟩,
      ⟨{2,3}, by decide⟩] : Fin 3 → PetersenVertex) j
  | .inr (.inr _) => petersenHub

noncomputable def hexFullPetersenIso : hexFullGraph ≃g petersenGraph :=
  { Equiv.ofBijective hexFullPetersenMap (by native_decide) with
    map_rel_iff' := by
      change ∀ a b, petersenGraph.Adj (hexFullPetersenMap a) (hexFullPetersenMap b) ↔
        hexFullGraph.Adj a b
      native_decide }

/-- The full three-apex, one-second-layer configuration is the Petersen graph. -/
noncomputable def hexFull_iso [Fintype V] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (hk : Nat.card (hexFirst c) = 3) (hh : Nat.card (hexSecond c) = 1) :
    G ≃g petersenGraph := by
  classical
  let ea := hexFirstEquiv hC hp c hk
  let ex : hexSecond c ≃ Unit := Fintype.equivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_unit] using hh)
  let e : V ≃ HexFullV := (hexLayerPartition c).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr ea ex))
  let ac : hexFirst c := ea.symm 0
  let bc : hexFirst c := ea.symm 1
  have hab : ac ≠ bc := by
    intro h
    have := congrArg ea h
    simpa [ac, bc] using this
  have hs (w : hexFirst c) (i : Fin 6) :
      G.Adj w.val (c i) ↔ i.val % 3 = (ea w).val :=
    hexFirstIndex_spec hC hp c w i
  have hn (i : Fin 6) (x : hexSecond c) : ¬ G.Adj (c i) x.val :=
    fun h => x.property.2 i h.symm
  have hadj (u v : V) : hexFullGraph.Adj (e u) (e v) ↔ G.Adj u v := by
    obtain ⟨u, rfl⟩ := (hexLayerPartition c).surjective u
    obtain ⟨v, rfl⟩ := (hexLayerPartition c).surjective v
    change hexFullGraph.Adj
      ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr ea ex))
        ((hexLayerPartition c).symm ((hexLayerPartition c) u)))
      ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr ea ex))
        ((hexLayerPartition c).symm ((hexLayerPartition c) v))) ↔ _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases u with i | u <;> try rcases u with a | x
    all_goals rcases v with j | v <;> try rcases v with b | y
    all_goals simp only [Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, id_eq]
    all_goals change hexFullGraph.Adj _ _ ↔ G.Adj _ _
    all_goals simp only [hexFullGraph, simpleOf, hexLayerPartition,
      Equiv.ofBijective_apply, Sum.elim_inl, Sum.elim_inr]
    all_goals try simp only [Equiv.refl_apply]
    all_goals simp only [ne_eq, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl, not_false_eq_true, true_and,
      or_self, false_or, and_false, and_true, false_iff, true_iff]
    all_goals first
      | (solve | rw [c.map_rel_iff]; exact
          ⟨fun h => h.2.elim id Adj.symm, fun h => ⟨h.ne, Or.inl h⟩⟩)
      | (solve | simp [hexFirst_independent hC hp c])
      | (solve | simp [hexSecond_independent hconn hC hp c ac bc hab])
      | exact hn _ _
      | exact fun h => hn _ _ h.symm
      | exact (hs _ _).symm
      | (solve | simpa only [G.adj_comm] using (hs b i).symm)
      | exact hexSecond_complete hconn hC hp c _ _
      | exact (hexSecond_complete hconn hC hp c _ _).symm
  exact ({ e with map_rel_iff' := fun {u v} => hadj u v } : G ≃g hexFullGraph).trans
    hexFullPetersenIso

/-- Equality in the mass bound in the multi-apex branch identifies the
actual graph, not merely its order or degree sequence. -/
theorem hexMulti_mass_eq_imp_petersen [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G)
    (a b : hexFirst c) (hab : a ≠ b)
    (hm : neighbourhoodIndependenceSum G = 3 * Fintype.card V) :
    Nonempty (G ≃g petersenGraph) := by
  obtain ⟨hk, hh⟩ := (hexMulti_mass_le hconn hC hp c a b hab).2.mp hm
  exact ⟨hexFull_iso hconn hC hp c hk hh⟩

/-- At order ten or above the multi-apex branch consists only of Petersen. -/
theorem hexMulti_large_imp_petersen [Fintype V]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a b : hexFirst c) (hab : a ≠ b)
    (hn : 10 ≤ Fintype.card V) : Nonempty (G ≃g petersenGraph) := by
  obtain ⟨hk, hh, _⟩ := hexMulti_parameters hconn hC hp c a b hab
  have hc := hexLayer_card c
  have hk3 : Nat.card (hexFirst c) = 3 := by omega
  have hh1 : Nat.card (hexSecond c) = 1 := by omega
  exact ⟨hexFull_iso hconn hC hp c hk3 hh1⟩

/-- Beyond order ten there is exactly one first-layer vertex. This is the
structural reduction to the Gamma family with a possible second-layer matching. -/
theorem hexLarge_first_card [Fintype V]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (hn : 11 ≤ Fintype.card V) :
    Nat.card (hexFirst c) = 1 := by
  classical
  by_contra hne
  by_cases hz : IsEmpty (hexFirst c)
  · have hs : IsEmpty (hexSecond c) := ⟨fun x =>
      (hexSecond_first_nonempty hconn hC hp c x).elim hz.false⟩
    have hc := hexLayer_card c
    have ha0 : Nat.card (hexFirst c) = 0 := by
      letI := hz
      simp
    have hx0 : Nat.card (hexSecond c) = 0 := by
      letI := hs
      simp
    omega
  · have htwo : 1 < Fintype.card (hexFirst c) := by
      have hp0 : 0 < Fintype.card (hexFirst c) :=
        Fintype.card_pos_iff.mpr (not_isEmpty_iff.mp hz)
      rw [Nat.card_eq_fintype_card] at hne
      omega
    obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp htwo
    have := (hexMulti_parameters hconn hC hp c a b hab).2.2
    omega

/-- In the one-apex case, an edgeless second layer is exactly a Gamma graph. -/
noncomputable def hexOne_independent_iso_gamma [Fintype V]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a : hexFirst c)
    (ha : ∀ b : hexFirst c, b = a)
    (hind : ∀ x y : hexSecond c, ¬ G.Adj x.val y.val) :
    G ≃g gammaGraph (Nat.card (hexSecond c)) := by
  classical
  let h := Nat.card (hexSecond c)
  let ex : Fin h ≃ hexSecond c := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, h, Nat.card_eq_fintype_card])
  let k := (hexTrace_antipodal hC hp c a.property.1 a.property.2).choose
  have hk := (hexTrace_antipodal hC hp c a.property.1 a.property.2).choose_spec
  let f : GammaV h → V
    | .cycle i => c (i + k)
    | .apex => a.val
    | .leaf i => (ex i).val
  have hinj : Function.Injective f := by
    intro u v huv
    cases u with
    | cycle i =>
      cases v with
      | cycle j => exact congrArg GammaV.cycle (add_right_cancel (c.injective huv))
      | apex => exact False.elim (a.property.1 (i+k) huv)
      | leaf j => exact False.elim ((ex j).property.1 (i+k) huv)
    | apex =>
      cases v with
      | cycle j => exact False.elim (a.property.1 (j+k) huv.symm)
      | apex => rfl
      | leaf j =>
        obtain ⟨i, hi⟩ := a.property.2
        change a.val = (ex j).val at huv
        exact False.elim ((ex j).property.2 i (huv ▸ hi))
    | leaf i =>
      cases v with
      | cycle j => exact False.elim ((ex i).property.1 (j+k) huv.symm)
      | apex =>
        obtain ⟨j, hj⟩ := a.property.2
        change (ex i).val = a.val at huv
        exact False.elim ((ex i).property.2 j (huv.symm ▸ hj))
      | leaf j => exact congrArg GammaV.leaf (ex.injective (Subtype.ext huv))
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨u, rfl⟩ := (hexLayerPartition c).surjective v
    rcases u with i | u
    · refine ⟨.cycle (i-k), ?_⟩
      change c (i-k+k) = c i
      rw [sub_add_cancel]
    · rcases u with b | x
      · exact ⟨.apex, congrArg Subtype.val (ha b).symm⟩
      · exact ⟨.leaf (ex.symm x), congrArg Subtype.val (ex.apply_symm_apply x)⟩
  have hf (u v : GammaV h) : G.Adj (f u) (f v) ↔ (gammaGraph h).Adj u v := by
    have hrot : ∀ i j k : Fin 6,
        (cycleGraph 6).Adj (i+k) (j+k) ↔ (cycleGraph 6).Adj i j := by native_decide
    have hpair : ∀ i k : Fin 6, (i+k=k ∨ i+k=k+3) ↔ (i=0 ∨ i=3) := by native_decide
    cases u with
    | cycle i =>
      cases v with
      | cycle j =>
        change G.Adj (c (i+k)) (c (j+k)) ↔ _
        rw [c.map_rel_iff, hrot]
        simp only [gammaGraph, simpleOf]
        simp only [ne_eq, GammaV.cycle.injEq, (cycleGraph 6).adj_comm, or_self]
        exact ⟨fun h => ⟨h.ne, h⟩, And.right⟩
      | apex =>
        change G.Adj (c (i+k)) a.val ↔ _
        rw [G.adj_comm, hk, hpair]
        simp [gammaGraph, simpleOf]
      | leaf j =>
        have hn : ¬ G.Adj (c (i+k)) (ex j).val := fun h => (ex j).property.2 (i+k) h.symm
        simp [f, gammaGraph, simpleOf, hn]
    | apex =>
      cases v with
      | cycle j =>
        change G.Adj a.val (c (j+k)) ↔ _
        rw [hk, hpair]
        simp [gammaGraph, simpleOf]
      | apex => simp [f, gammaGraph, simpleOf]
      | leaf j =>
        have he := (hexSecond_complete hconn hC hp c (ex j) a).symm
        simp [f, gammaGraph, simpleOf, he]
    | leaf i =>
      cases v with
      | cycle j =>
        have hn := (ex i).property.2 (j+k)
        simp [f, gammaGraph, simpleOf, hn]
      | apex =>
        have he := hexSecond_complete hconn hC hp c (ex i) a
        simp [f, gammaGraph, simpleOf, he]
      | leaf j => simp [f, gammaGraph, simpleOf, hind]
  exact ({ Equiv.ofBijective f ⟨hinj, hsurj⟩ with
    map_rel_iff' := fun {u v} => hf u v } : gammaGraph h ≃g G).symm

private theorem hexOne_neighbor_second (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G) (a : hexFirst c)
    (ha : ∀ b : hexFirst c, b = a) (x : hexSecond c) {v : V}
    (hv : G.Adj x.val v) : v = a.val ∨ ∃ y : hexSecond c, v = y.val := by
  obtain ⟨u, rfl⟩ := (hexLayerPartition c).surjective v
  rcases u with i | u
  · exact False.elim (x.property.2 i hv)
  · rcases u with b | y
    · exact Or.inl (congrArg Subtype.val (ha b))
    · exact Or.inr ⟨y, rfl⟩

/-- Each second-layer vertex contributes exactly one unit of mass in the
one-apex branch, even when it belongs to an edge of the matching. -/
theorem hexOne_second_lambda [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a : hexFirst c) (ha : ∀ b : hexFirst c, b = a)
    (x : hexSecond c) : lambda G x.val = 1 := by
  classical
  let H := G.induce (G.neighborSet x.val)
  have hcl : G.IsClique (G.neighborSet x.val) := by
    intro u hu v hv huv
    obtain rfl | ⟨y, rfl⟩ := hexOne_neighbor_second hconn hC hp c a ha x hu
    · obtain rfl | ⟨z, rfl⟩ := hexOne_neighbor_second hconn hC hp c a ha x hv
      · exact False.elim (huv rfl)
      · exact (hexSecond_complete hconn hC hp c z a).symm
    · obtain rfl | ⟨z, rfl⟩ := hexOne_neighbor_second hconn hC hp c a ha x hv
      · exact hexSecond_complete hconn hC hp c y a
      · have he := hexSecond_matching hconn hC hp c a x y z hu hv
        exact False.elim (huv (congrArg Subtype.val he))
  have hu : G.Adj x.val a.val := hexSecond_complete hconn hC hp c x a
  have hlo : 1 ≤ H.indepNum := by
    let w : G.neighborSet x.val := ⟨a.val, hu⟩
    have hi : H.IsIndepSet ({w} : Finset _) := by simp [isIndepSet_iff]
    simpa using IsIndepSet.card_le_indepNum hi
  have hhi : H.indepNum ≤ 1 := by
    obtain ⟨s, hs⟩ := H.exists_isNIndepSet_indepNum
    have hc : s.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro u hu v hv
      by_contra hne
      exact hs.isIndepSet hu hv hne
        (hcl u.property v.property (Subtype.coe_ne_coe.mpr hne))
    rw [hs.card_eq] at hc
    exact hc
  change H.indepNum = 1
  omega

/-- The first-layer apex has exactly two independent cycle neighbours,
plus the matching induced by the second layer. -/
noncomputable def hexOne_apex_neighbors_iso [Fintype V]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a : hexFirst c) (ha : ∀ b : hexFirst c, b = a) :
    (G.induce (G.neighborSet a.val)) ≃g
      ((⊥ : SimpleGraph (Fin 2)) ⊕g G.induce (hexSecond c)) := by
  classical
  let k := (hexTrace_antipodal hC hp c a.property.1 a.property.2).choose
  have hk := (hexTrace_antipodal hC hp c a.property.1 a.property.2).choose_spec
  let pos : Fin 2 → Fin 6 := fun i => k + 3 * (⟨i.val, by omega⟩ : Fin 6)
  have hpos : ∀ i j : Fin 2, pos i = pos j → i = j := by
    have hf : ∀ k : Fin 6, ∀ i j : Fin 2,
        k + 3 * (⟨i.val, by omega⟩ : Fin 6) = k + 3 * (⟨j.val, by omega⟩ : Fin 6) → i = j := by native_decide
    exact hf k
  have hcontact (i : Fin 2) : G.Adj a.val (c (pos i)) := by
    apply (hk _).2
    fin_cases i <;> simp [pos, k]
  let f : Fin 2 ⊕ hexSecond c → G.neighborSet a.val := Sum.elim
    (fun i => ⟨c (pos i), hcontact i⟩)
    (fun x => ⟨x.val, (hexSecond_complete hconn hC hp c x a).symm⟩)
  have hbij : Function.Bijective f := by
    constructor
    · intro u v huv
      have he := congrArg Subtype.val huv
      cases u with
      | inl i =>
        cases v with
        | inl j => exact congrArg Sum.inl (hpos i j (c.injective he))
        | inr x => exact False.elim (x.property.1 (pos i) he)
      | inr x =>
        cases v with
        | inl j => exact False.elim (x.property.1 (pos j) he.symm)
        | inr y => exact congrArg Sum.inr (Subtype.ext he)
    · intro ⟨v, hv⟩
      obtain ⟨u, rfl⟩ := (hexLayerPartition c).surjective v
      rcases u with i | u
      · have hi := (hk i).1 hv
        rcases hi with hi | hi
        · refine ⟨Sum.inl 0, Subtype.ext ?_⟩
          change c (pos 0) = c i
          apply congrArg c
          simpa [pos, k] using hi.symm
        · refine ⟨Sum.inl 1, Subtype.ext ?_⟩
          change c (pos 1) = c i
          apply congrArg c
          simpa [pos, k] using hi.symm
      · rcases u with b | x
        · have he := ha b
          have hv' : G.Adj a.val b.val := hv
          rw [he] at hv'
          exact False.elim (G.loopless.irrefl _ hv')
        · exact ⟨Sum.inr x, rfl⟩
  refine ({ Equiv.ofBijective f hbij with map_rel_iff' := ?_ } :
    ((⊥ : SimpleGraph (Fin 2)) ⊕g G.induce (hexSecond c)) ≃g
      G.induce (G.neighborSet a.val)).symm
  intro u v
  simp only [sum_adj]
  cases u with
  | inl i =>
    cases v with
    | inl j =>
      change G.Adj (c (pos i)) (c (pos j)) ↔ False
      rw [c.map_rel_iff]
      have hf : ∀ k : Fin 6, ∀ i j : Fin 2,
          ¬ (cycleGraph 6).Adj (k + 3 * (⟨i.val, by omega⟩ : Fin 6)) (k + 3 * (⟨j.val, by omega⟩ : Fin 6)) := by native_decide
      exact iff_false_intro (hf k i j)
    | inr x =>
      change G.Adj (c (pos i)) x.val ↔ False
      exact iff_false_intro (fun h => x.property.2 _ h.symm)
  | inr x =>
    cases v with
    | inl j =>
      change G.Adj x.val (c (pos j)) ↔ False
      exact iff_false_intro (x.property.2 _)
    | inr y => rfl

/-- The number of matching edges in the second layer. -/
noncomputable def hexMatchingEdges [Fintype V] (c : cycleGraph 6 ↪g G) : ℕ :=
  Nat.card (G.induce (hexSecond c)).edgeSet

theorem hexOne_apex_lambda [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a : hexFirst c) (ha : ∀ b : hexFirst c, b = a) :
    lambda G a.val + hexMatchingEdges c = 2 + Nat.card (hexSecond c) := by
  classical
  let H := G.induce (hexSecond c)
  have hd (x : hexSecond c) : H.degree x ≤ 1 := by
    rw [← H.card_neighborFinset_eq_degree]
    apply Finset.card_le_one.mpr
    intro y hy z hz
    exact hexSecond_matching hconn hC hp c a x y z
      ((H.mem_neighborFinset x y).mp hy) ((H.mem_neighborFinset x z).mp hz)
  have hm := indepNum_add_edgeCount_of_degree_le_one (H := H) hd
  have hl : lambda G a.val = 2 + H.indepNum := by
    change (G.induce (G.neighborSet a.val)).indepNum = _
    rw [indepNum_iso (hexOne_apex_neighbors_iso hconn hC hp c a ha), indepNum_sum]
    have hb : (⊥ : SimpleGraph (Fin 2)).indepNum = 2 := by
      apply le_antisymm
      · obtain ⟨s, hs⟩ := (⊥ : SimpleGraph (Fin 2)).exists_isNIndepSet_indepNum
        have hh := Finset.card_le_card (Finset.subset_univ s)
        simpa [hs.card_eq] using hh
      · have hi : (⊥ : SimpleGraph (Fin 2)).IsIndepSet (Finset.univ : Finset (Fin 2)) := by
          intro u hu v hv huv
          exact fun h => h
        simpa using IsIndepSet.card_le_indepNum hi
    rw [hb]
  unfold hexMatchingEdges
  rw [Nat.card_eq_fintype_card, H.card_edgeSet]
  change lambda G a.val + edgeCount H = _
  rw [hl, Nat.add_assoc]
  unfold edgeCount
  rw [hm]
  simp only [Nat.card_eq_fintype_card]

/-- Cycle vertices lie in no triangle, also in the one-apex matching case. -/
theorem hexCycle_no_triangle (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (i : Fin 6) :
    ∀ u v, G.Adj (c i) u → G.Adj u v → ¬ G.Adj (c i) v := by
  classical
  intro u v hiu huv hiv
  obtain ⟨u, rfl⟩ := (hexLayerPartition c).surjective u
  obtain ⟨v, rfl⟩ := (hexLayerPartition c).surjective v
  have hn (j : Fin 6) (x : hexSecond c) : ¬ G.Adj (c j) x.val :=
    fun h => x.property.2 j h.symm
  have he (a : hexFirst c) (j k : Fin 6) (hjk : (cycleGraph 6).Adj j k) :
      ¬ (G.Adj a.val (c j) ∧ G.Adj a.val (c k)) := by
    obtain ⟨l, hl⟩ := hexTrace_antipodal hC hp c a.property.1 a.property.2
    have hf : ∀ j k l : Fin 6, (cycleGraph 6).Adj j k →
        ¬ ((j=l ∨ j=l+3) ∧ (k=l ∨ k=l+3)) := by native_decide
    exact fun h => hf j k l hjk ⟨(hl j).1 h.1, (hl k).1 h.2⟩
  rcases u with j | u <;> try rcases u with a | x
  all_goals rcases v with k | v <;> try rcases v with b | y
  all_goals change G.Adj _ _ at hiu huv hiv
  all_goals first
    | exact hn _ _ hiu
    | exact hn _ _ hiv
    | exact hexFirst_independent hC hp c _ _ huv
    | exact he _ _ _ ((c.map_rel_iff).1 hiu) ⟨hiv.symm, huv.symm⟩
    | exact he _ _ _ ((c.map_rel_iff).1 hiv) ⟨hiu.symm, huv⟩
    | exact (by
        have hf : ∀ i j k : Fin 6, (cycleGraph 6).Adj i j →
          (cycleGraph 6).Adj j k → ¬ (cycleGraph 6).Adj i k := by native_decide
        exact hf i j k ((c.map_rel_iff).1 hiu) ((c.map_rel_iff).1 huv)
          ((c.map_rel_iff).1 hiv))

theorem hexCycle_lambda [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G) (i : Fin 6) :
    lambda G (c i) = G.degree (c i) := by
  classical
  have he : (G.induce (G.neighborSet (c i))).edgeFinset = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    exact hexCycle_no_triangle hC hp c i _ _ e.out.1.property
      (adj_out_of_mem (G.induce (G.neighborSet (c i))) e he) e.out.2.property
  have ht : trianglesAt G (c i) = 0 := by
    rw [trianglesAt_eq_neighborEdges, edgeCount, he, Finset.card_empty]
  have := lambda_add_trianglesAt hC (c i)
  omega

theorem hexCycle_degree_sum [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hC : StrongC4Free G) (hp : IsPkFree G 6) (c : cycleGraph 6 ↪g G) :
    (∑ i : Fin 6, G.degree (c i)) = 12 + 2 * Nat.card (hexFirst c) := by
  classical
  have hdeg (i : Fin 6) : G.degree (c i) =
      (∑ j : Fin 6, if G.Adj (c i) (c j) then 1 else 0) +
      (∑ a : hexFirst c, if G.Adj (c i) a.val then 1 else 0) +
      ∑ x : hexSecond c, if G.Adj (c i) x.val then 1 else 0 := by
    have hv : G.degree (c i) = ∑ x : V, if G.Adj (c i) x then 1 else 0 := by
      simpa only [Finset.sum_boole, Nat.cast_id, ← G.neighborFinset_eq_filter] using
        (G.card_neighborFinset_eq_degree (c i)).symm
    rw [hv, hexLayer_sum c]
  have hcdeg (i : Fin 6) :
      (∑ j : Fin 6, if G.Adj (c i) (c j) then 1 else 0) = 2 := by
    simp_rw [c.map_rel_iff]
    have hf : ∀ i : Fin 6,
        (∑ j : Fin 6, if (cycleGraph 6).Adj i j then 1 else 0) = 2 := by native_decide
    exact hf i
  have htrace (w : hexFirst c) :
      (∑ i : Fin 6, if G.Adj (c i) w.val then 1 else 0) = 2 := by
    obtain ⟨k, hk⟩ := hexTrace_antipodal hC hp c w.property.1 w.property.2
    simp_rw [G.adj_comm (c _) w.val, hk]
    have hf : ∀ k : Fin 6, (∑ i : Fin 6, if i=k ∨ i=k+3 then 1 else 0) = 2 := by native_decide
    exact hf k
  have hn (i : Fin 6) (x : hexSecond c) : ¬ G.Adj (c i) x.val :=
    fun h => x.property.2 i h.symm
  simp_rw [hdeg, hcdeg, if_neg (hn _ _)]
  simp only [Finset.sum_const_zero, Nat.add_zero]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp_rw [htrace]
  simp [Nat.card_eq_fintype_card, Nat.mul_comm]

/-- The exact one-apex mass formula from the paper, in subtraction-free form. -/
theorem hexOne_mass [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a : hexFirst c) (ha : ∀ b : hexFirst c, b = a) :
    neighbourhoodIndependenceSum G + hexMatchingEdges c = 2 * Fintype.card V + 2 := by
  classical
  letI : Unique (hexFirst c) := ⟨⟨a⟩, ha⟩
  have hk : Nat.card (hexFirst c) = 1 := by simp
  have hc := hexLayer_card c
  have hl := hexOne_apex_lambda hconn hC hp c a ha
  have hcy := hexCycle_degree_sum hC hp c
  unfold neighbourhoodIndependenceSum
  rw [hexLayer_sum c]
  simp_rw [hexCycle_lambda hC hp c, hexOne_second_lambda hconn hC hp c a ha]
  rw [hcy]
  simp only [Fintype.sum_unique, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.mul_one]
  change 12 + 2 * Nat.card (hexFirst c) + lambda G a.val +
    Fintype.card (hexSecond c) + hexMatchingEdges c = _
  rw [hk] at *
  simp only [Nat.card_eq_fintype_card] at hl hc
  omega

theorem hexMatchingEdges_eq_zero_iff [Fintype V] (c : cycleGraph 6 ↪g G) :
    hexMatchingEdges c = 0 ↔ ∀ x y : hexSecond c, ¬ G.Adj x.val y.val := by
  classical
  unfold hexMatchingEdges
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff]
  constructor
  · intro he x y hxy
    exact he.false ⟨s(x,y), (G.induce (hexSecond c)).mem_edgeSet.mpr hxy⟩
  · intro he
    refine ⟨fun e => ?_⟩
    have hm : e.val ∈ (G.induce (hexSecond c)).edgeFinset := by
      simpa only [mem_edgeFinset] using e.property
    have ha := adj_out_of_mem (G.induce (hexSecond c)) e.val hm
    exact he _ _ ha

/-- Sharp one-apex bound, with the precise Gamma isomorphism in equality. -/
theorem hexOne_mass_le [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (a : hexFirst c) (ha : ∀ b : hexFirst c, b = a) :
    neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V + 2 ∧
    (neighbourhoodIndependenceSum G = 2 * Fintype.card V + 2 →
      Nonempty (G ≃g gammaGraph (Nat.card (hexSecond c)))) := by
  have hm := hexOne_mass hconn hC hp c a ha
  refine ⟨by omega, fun he => ?_⟩
  have hz : hexMatchingEdges c = 0 := by omega
  exact ⟨hexOne_independent_iso_gamma hconn hC hp c a ha
    ((hexMatchingEdges_eq_zero_iff c).mp hz)⟩

/-- An order-at-least-eleven graph in the hexagon branch satisfies the sharp
Gamma bound, and equality gives the named graph with the correct parameter. -/
theorem hexLarge_mass [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) (hn : 11 ≤ Fintype.card V) :
    neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V + 2 ∧
    (neighbourhoodIndependenceSum G = 2 * Fintype.card V + 2 →
      Nonempty (G ≃g gammaGraph (Fintype.card V - 7))) := by
  classical
  have hk := hexLarge_first_card hconn hC hp c hn
  have ho : Fintype.card (hexFirst c) = 1 := by
    simpa only [Nat.card_eq_fintype_card] using hk
  obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp ho
  have hh : Nat.card (hexSecond c) = Fintype.card V - 7 := by
    have hc := hexLayer_card c
    omega
  obtain ⟨hb, he⟩ := hexOne_mass_le hconn hC hp c a ha
  exact ⟨hb, fun hm => hh ▸ he hm⟩

/-- The hexagon branch satisfies the global density-three bound, with
Petersen as its only equality case. -/
theorem hex_mass_le_three [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 6 ↪g G) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V ∧
    (neighbourhoodIndependenceSum G = 3 * Fintype.card V →
      Nonempty (G ≃g petersenGraph)) := by
  classical
  by_cases ht : 1 < Fintype.card (hexFirst c)
  · obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp ht
    exact ⟨(hexMulti_mass_le hconn hC hp c a b hab).1,
      hexMulti_mass_eq_imp_petersen hconn hC hp c a b hab⟩
  · by_cases ho : Fintype.card (hexFirst c) = 1
    · obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp ho
      have hm := (hexOne_mass_le hconn hC hp c a ha).1
      have hn : 7 ≤ Fintype.card V := by
        have hc := hexLayer_card c
        simp only [Nat.card_eq_fintype_card] at hc
        omega
      exact ⟨by omega, fun he => by omega⟩
    · have hz : Fintype.card (hexFirst c) = 0 := by omega
      haveI : IsEmpty (hexFirst c) := Fintype.card_eq_zero_iff.mp hz
      have hs : IsEmpty (hexSecond c) := ⟨fun x =>
        (hexSecond_first_nonempty hconn hC hp c x).elim isEmptyElim⟩
      have hd : ∀ v, ∃ i, v=c i ∨ G.Adj v (c i) := by
        intro v
        obtain ⟨u, rfl⟩ := (hexLayerPartition c).surjective v
        rcases u with i | u
        · exact ⟨i, Or.inl rfl⟩
        · rcases u with a | x
          · exact isEmptyElim a
          · exact hs.false x |>.elim
      have hm := (hexDominating_mass hC hp c hd).2
      exact ⟨Nat.le_of_lt hm, fun he => False.elim (Nat.ne_of_lt hm he)⟩

noncomputable def gammaPartition (h : ℕ) : Fin 6 ⊕ (Unit ⊕ Fin h) ≃ GammaV h :=
  Equiv.ofBijective (Sum.elim GammaV.cycle (Sum.elim (fun _ => .apex) GammaV.leaf)) (by
    constructor
    · intro u v huv
      rcases u with i | u <;> try rcases u with u | i
      all_goals rcases v with j | v <;> try rcases v with v | j
      all_goals simp_all
    · intro v
      cases v with
      | cycle i => exact ⟨Sum.inl i, rfl⟩
      | apex => exact ⟨Sum.inr (Sum.inl ()), rfl⟩
      | leaf i => exact ⟨Sum.inr (Sum.inr i), rfl⟩)

theorem gamma_card (h : ℕ) : Fintype.card (GammaV h) = 7 + h := by
  have hc := Fintype.card_congr (gammaPartition h)
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at hc
  omega

private theorem gamma_sum (h : ℕ) (f : GammaV h → ℕ) :
    (∑ v, f v) = (∑ i : Fin 6, f (.cycle i)) + f .apex + ∑ i : Fin h, f (.leaf i) := by
  rw [← Fintype.sum_equiv (gammaPartition h) (fun x => f (gammaPartition h x)) f (fun _ => rfl),
    Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [gammaPartition, Equiv.ofBijective_apply, Sum.elim_inl, Sum.elim_inr,
    Fintype.sum_unique]
  omega

theorem gamma_no_triangle (h : ℕ) : ∀ a b c, (gammaGraph h).Adj a b →
    (gammaGraph h).Adj b c → ¬ (gammaGraph h).Adj a c := by
  have hf : ∀ i j k : Fin 6, (cycleGraph 6).Adj i j →
      (cycleGraph 6).Adj j k → ¬ (cycleGraph 6).Adj i k := by native_decide
  have hp : ∀ i j : Fin 6, (cycleGraph 6).Adj i j →
      ¬ ((i=0 ∨ i=3) ∧ (j=0 ∨ j=3)) := by native_decide
  intro a b c
  cases a <;> cases b <;> cases c <;> simp only [gammaGraph, simpleOf]
  all_goals simp only [ne_eq, GammaV.cycle.injEq, GammaV.leaf.injEq,
    reduceCtorEq]
  all_goals try simp_all only [false_or, or_false, or_self, and_false, and_true,
    true_and, not_false_eq_true, not_true_eq_false, false_implies, implies_true]
  all_goals first
    | exact fun h1 h2 h3 => hf _ _ _ (h1.2.elim id Adj.symm)
        (h2.2.elim id Adj.symm) (h3.2.elim id Adj.symm)
    | (solve | intros; apply hp <;> assumption)
    | (solve | intro h1 h2 h3; apply hp; exact h1.2.elim id Adj.symm; aesop)
    | (solve | intro h1 h2 h3; apply hp; exact h2.2.elim id Adj.symm; aesop)
    | (solve | intro h1 h2 h3; apply hp; exact h3.2.elim id Adj.symm; aesop)

theorem gamma_mass (h : ℕ) : neighbourhoodIndependenceSum (gammaGraph h) = 16 + 2*h := by
  classical
  rw [mass_eq_degree_sum_of_no_triangle (gamma_no_triangle h)]
  have hd (v : GammaV h) : (gammaGraph h).degree v =
      (∑ i : Fin 6, if (gammaGraph h).Adj v (.cycle i) then 1 else 0) +
      (if (gammaGraph h).Adj v .apex then 1 else 0) +
      ∑ i : Fin h, if (gammaGraph h).Adj v (.leaf i) then 1 else 0 := by
    have hv : (gammaGraph h).degree v = ∑ x : GammaV h,
        if (gammaGraph h).Adj v x then 1 else 0 := by
      simpa only [Finset.sum_boole, Nat.cast_id, ← (gammaGraph h).neighborFinset_eq_filter] using
        ((gammaGraph h).card_neighborFinset_eq_degree v).symm
    rw [hv, gamma_sum]
  have hl (i : Fin h) : (gammaGraph h).degree (.leaf i) = 1 := by
    rw [hd]
    simp [gammaGraph, simpleOf]
  have ha : (gammaGraph h).degree .apex = 2+h := by
    rw [hd]
    simp [gammaGraph, simpleOf]
    decide
  have hc (i : Fin 6) : (gammaGraph h).degree (.cycle i) =
      2 + if i=0 ∨ i=3 then 1 else 0 := by
    rw [hd]
    have he : ∀ i : Fin 6, (∑ j : Fin 6, if
        (i≠j ∧ ((cycleGraph 6).Adj i j ∨ (cycleGraph 6).Adj j i)) then 1 else 0) = 2 := by
      native_decide
    simpa [gammaGraph, simpleOf] using he i
  rw [gamma_sum]
  simp_rw [hl, ha, hc]
  simp [Fin.sum_univ_six]
  omega

end InducedPaths
