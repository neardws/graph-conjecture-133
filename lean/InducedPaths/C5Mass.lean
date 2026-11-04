module

public import InducedPaths.C5Trace
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators

open Finset SimpleGraph
open scoped SimpleGraph

@[expose] public section
namespace InducedPaths

variable {V : Type*} {G : SimpleGraph V}

/-- A clique cover of the neighbourhood bounds its independence number. -/
theorem lambda_le_of_cover [Fintype V] [DecidableEq V] {K : Type*} [Fintype K]
    (v : V) (f : G.neighborSet v → K)
    (hf : ∀ a b, f a = f b → a = b ∨ G.Adj a.val b.val) :
    lambda G v ≤ Fintype.card K := by
  classical
  let H := G.induce (G.neighborSet v)
  obtain ⟨s, hs⟩ := H.exists_isNIndepSet_indepNum
  have hinj : Set.InjOn f s := by
    intro a ha b hb he
    rcases hf a b he with h | h
    · exact h
    · by_contra hn
      exact hs.isIndepSet ha hb hn h
  have hle : s.card ≤ Fintype.card K := Finset.card_le_card_of_injOn f
    (fun _ _ => Finset.mem_univ _) hinj
  have he := hs.card_eq
  change H.indepNum ≤ Fintype.card K
  omega

/-- A star with at most one extra neighbour per leaf has clique fibres. -/
theorem pent_cover_fibre (hC : StrongC4Free G) {v z a b : V}
    (hz : G.Adj v z) (ha : G.Adj v a) (hb : G.Adj v b)
    (ha' : a = z ∨ G.Adj a z) (hb' : b = z ∨ G.Adj b z) :
    a = b ∨ G.Adj a b := by
  rcases ha' with rfl | ha'
  · rcases hb' with rfl | hb'
    · exact Or.inl rfl
    · exact Or.inr hb'.symm
  rcases hb' with rfl | hb'
  · exact Or.inr ha'
  · exact Or.inl (commonNeighbors_subsingleton hC hz.ne ⟨ha, ha'.symm⟩ ⟨hb, hb'.symm⟩)

/-- Singleton and pair vertices of the designated pentagon. -/
def pentW (c : cycleGraph 5 ↪g G) : Set V := {v | ∃ i, v ∈ kmW G c i}
def pentX (c : cycleGraph 5 ↪g G) : Set V := {v | ∃ i, v ∈ kmX G c i}

 theorem pentW_trace (c : cycleGraph 5 ↪g G) {v : V} {i : Fin 5}
    (hv : v ∈ kmW G c i) (k : Fin 5) : G.Adj v (c k) ↔ k = i := by
  have := Set.ext_iff.mp hv.2 k
  simpa [cycleTrace] using this

 theorem pentX_trace (c : cycleGraph 5 ↪g G) {v : V} {i : Fin 5}
    (hv : v ∈ kmX G c i) (k : Fin 5) :
    G.Adj v (c k) ↔ k = i ∨ k = i + 1 := by
  have := Set.ext_iff.mp hv.2 k
  simpa [cycleTrace] using this

 theorem pentWX_disjoint (c : cycleGraph 5 ↪g G) : Disjoint (pentW c) (pentX c) := by
  rw [Set.disjoint_left]
  rintro v ⟨i, hi⟩ ⟨j, hj⟩
  have h1 := (pentW_trace c hi j).1 ((pentX_trace c hj j).2 (Or.inl rfl))
  have h2 := (pentW_trace c hi (j+1)).1 ((pentX_trace c hj (j+1)).2 (Or.inr rfl))
  have hn : ∀ j : Fin 5, j ≠ j+1 := by decide
  exact hn j (h1.trans h2.symm)

 theorem pent_classify (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 5 ↪g G) (v : V) :
    (∃ i, v = c i) ∨ v ∈ pentW c ∨ v ∈ pentX c := by
  by_cases hv : ∃ i, v = c i
  · exact Or.inl hv
  right
  have hout : v ∈ outsideCycle c := by
    intro i he
    exact hv ⟨i, he.symm⟩
  obtain ⟨i, hi | hi⟩ := pentTrace_dominates hconn hC hp c v
  · exact (hv ⟨i, hi⟩).elim
  exact pentTrace_mem_kmW_or_kmX hC c hout ⟨i, hi⟩

/-- The canonical partition into the cycle, singleton traces, and pair traces. -/
noncomputable def pentPartition (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 6) (c : cycleGraph 5 ↪g G) :
    (Fin 5 ⊕ (pentW c ⊕ pentX c)) ≃ V :=
  Equiv.ofBijective (Sum.elim c (Sum.elim Subtype.val Subtype.val)) (by
    constructor
    · intro a b he
      cases a with
      | inl i =>
        cases b with
        | inl j => exact congrArg Sum.inl (c.injective he)
        | inr b => cases b with
          | inl w => obtain ⟨j,hj⟩ := w.property; exact (hj.1 i he).elim
          | inr x => obtain ⟨j,hj⟩ := x.property; exact (hj.1 i he).elim
      | inr a => cases a with
        | inl w => cases b with
          | inl i => obtain ⟨j,hj⟩ := w.property; exact (hj.1 i he.symm).elim
          | inr b => cases b with
            | inl z => exact congrArg (Sum.inr ∘ Sum.inl) (Subtype.ext he)
            | inr x => exact (Set.disjoint_left.mp (pentWX_disjoint c) w.property ((show w.val = x.val from he).symm ▸ x.property)).elim
        | inr x => cases b with
          | inl i => obtain ⟨j,hj⟩ := x.property; exact (hj.1 i he.symm).elim
          | inr b => cases b with
            | inl w => exact (Set.disjoint_left.mp (pentWX_disjoint c) w.property ((show x.val = w.val from he) ▸ x.property)).elim
            | inr y => exact congrArg (Sum.inr ∘ Sum.inr) (Subtype.ext he)
    · intro v
      rcases pent_classify hconn hC hp c v with ⟨i,hi⟩ | hw | hx
      · exact ⟨Sum.inl i, hi.symm⟩
      · exact ⟨Sum.inr (Sum.inl ⟨v,hw⟩), rfl⟩
      · exact ⟨Sum.inr (Sum.inr ⟨v,hx⟩), rfl⟩)

 theorem pent_card [Fintype V] (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 6) (c : cycleGraph 5 ↪g G) :
    Fintype.card V = 5 + Nat.card (pentW c) + Nat.card (pentX c) := by
  classical
  have := Nat.card_congr (pentPartition hconn hC hp c)
  simpa [Nat.card_sum, Nat.card_eq_fintype_card, add_assoc] using this.symm

/-- The directed singleton-to-pair edges; there is at most one. -/
def pentCross (c : cycleGraph 5 ↪g G) :=
  {p : pentW c × pentX c // G.Adj p.1.val p.2.val}

 theorem pentCross_subsingleton (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (hc6 : ¬ cycleGraph 6 ⊴ G) (c : cycleGraph 5 ↪g G) :
    Subsingleton (pentCross c) := by
  constructor
  intro a b
  obtain ⟨i,hi⟩ := a.val.1.property
  obtain ⟨j,hj⟩ := a.val.2.property
  obtain ⟨k,hk⟩ := b.val.1.property
  obtain ⟨l,hl⟩ := b.val.2.property
  obtain ⟨h1,h2⟩ := pentTrace_cross_edge_unique hC hp hc6 c hi hj a.property hk hl b.property
  exact Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext h2))

 theorem pentCross_card_le_one (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (hc6 : ¬ cycleGraph 6 ⊴ G) (c : cycleGraph 5 ↪g G) :
    Nat.card (pentCross c) ≤ 1 := by
  let := pentCross_subsingleton hC hp hc6 c
  exact (Nat.card_le_card_of_injective (fun _ : pentCross c => ())
    (fun _ _ _ => Subsingleton.elim _ _)).trans (by simp)

/-- A finite set meeting every neighbour by equality or an edge is a clique
cover when its centres themselves neighbour the vertex. -/
theorem lambda_le_centres [Fintype V] [DecidableEq V]
    (hC : StrongC4Free G) (v : V) (s : Finset V)
    (hs : ∀ z ∈ s, G.Adj v z)
    (hcover : ∀ a, G.Adj v a → ∃ z ∈ s, a = z ∨ G.Adj a z) :
    lambda G v ≤ s.card := by
  classical
  let f : G.neighborSet v → s := fun a =>
    ⟨(hcover a.val a.property).choose, (hcover a.val a.property).choose_spec.1⟩
  have hf (a : G.neighborSet v) : a.val = (f a).val ∨ G.Adj a.val (f a).val :=
    (hcover a.val a.property).choose_spec.2
  have hb := lambda_le_of_cover v f (by
    intro a b he
    have h := pent_cover_fibre hC (hs (f a).val (f a).property)
      a.property b.property (hf a) (by simpa [he] using hf b)
    rcases h with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr h)
  simpa using hb

/-- A singleton vertex needs one centre for its support, and one for each
singleton--pair edge incident to it. Matching neighbours are covered by support. -/
theorem pentW_lambda_le [Fintype V] [DecidableEq V]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (hc6 : ¬ cycleGraph 6 ⊴ G) (c : cycleGraph 5 ↪g G)
    (w : pentW c) :
    lambda G w.val ≤ 1 + Nat.card {x : pentX c // G.Adj w.val x.val} := by
  classical
  obtain ⟨i,hi⟩ := w.property
  let t := univ.filter (fun x : pentX c => G.Adj w.val x.val)
  let s := insert (c i) (t.image Subtype.val)
  have hbound := lambda_le_centres hC w.val s (by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact (pentW_trace c hi i).2 rfl
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    exact (mem_filter.mp hx).2) (by
    intro a ha
    rcases pent_classify hconn hC hp c a with ⟨k,rfl⟩ | hw | hx
    · have hk := (pentW_trace c hi k).1 ha
      subst k
      exact ⟨c i, mem_insert_self _ _, Or.inl rfl⟩
    · obtain ⟨k,hk⟩ := hw
      have hki : i = k := by
        by_contra hn
        exact pentTrace_singleton_nonadjacent hC hc6 c hi hk hn ha
      subst k
      exact ⟨c i, mem_insert_self _ _, Or.inr ((pentW_trace c hk i).2 rfl)⟩
    · exact ⟨a, mem_insert_of_mem (mem_image.mpr ⟨⟨a,hx⟩, mem_filter.mpr ⟨mem_univ _,ha⟩,rfl⟩), Or.inl rfl⟩)
  have hc : s.card ≤ 1 + t.card := (card_insert_le _ _).trans (by
    have := card_image_le (f := Subtype.val) (s := t)
    omega)
  simpa [t, Nat.card_eq_fintype_card, Fintype.card_subtype] using hbound.trans hc

/-- Pair vertices need one cycle centre and their singleton neighbours. -/
theorem pentX_lambda_le [Fintype V] [DecidableEq V]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 5 ↪g G) (x : pentX c) :
    lambda G x.val ≤ 1 + Nat.card {w : pentW c // G.Adj w.val x.val} := by
  classical
  obtain ⟨i,hi⟩ := x.property
  let t := univ.filter (fun w : pentW c => G.Adj w.val x.val)
  let s := insert (c i) (t.image Subtype.val)
  have hbound := lambda_le_centres hC x.val s (by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact (pentX_trace c hi i).2 (Or.inl rfl)
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
    exact (mem_filter.mp hw).2.symm) (by
    intro a ha
    rcases pent_classify hconn hC hp c a with ⟨k,rfl⟩ | hw | hx
    · refine ⟨c i, mem_insert_self _ _, ?_⟩
      rcases (pentX_trace c hi k).1 ha with rfl | rfl
      · exact Or.inl rfl
      · right
        apply (c.map_rel_iff).2
        have hh : ∀ i : Fin 5, (cycleGraph 5).Adj (i+1) i := by decide
        exact hh i
    · exact ⟨a, mem_insert_of_mem (mem_image.mpr ⟨⟨a,hw⟩, mem_filter.mpr ⟨mem_univ _,ha.symm⟩,rfl⟩), Or.inl rfl⟩
    · obtain ⟨k,hk⟩ := hx
      exact (pentTrace_pair_nonadjacent hC c hi hk ha).elim)
  have hc : s.card ≤ 1 + t.card := (card_insert_le _ _).trans (by
    have := card_image_le (f := Subtype.val) (s := t)
    omega)
  simpa [t, Nat.card_eq_fintype_card, Fintype.card_subtype] using hbound.trans hc

/-- Cycle neighbourhoods are covered by their two cycle neighbours and the
singleton vertices supported there. Pair triangles require no extra centre. -/
theorem pentCycle_lambda_le [Fintype V] [DecidableEq V]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 5 ↪g G) (i : Fin 5) :
    lambda G (c i) ≤ 2 + Nat.card (kmW G c i) := by
  classical
  let t : Finset V := (kmW G c i).toFinset
  let s := insert (c (i+1)) (insert (c (i-1)) t)
  have hcy : ∀ i : Fin 5, (cycleGraph 5).Adj i (i+1) ∧ (cycleGraph 5).Adj i (i-1) := by decide
  have hb := lambda_le_centres hC (c i) s (by
    intro z hz
    rcases mem_insert.mp hz with rfl | hz
    · exact (c.map_rel_iff).2 (hcy i).1
    rcases mem_insert.mp hz with rfl | hz
    · exact (c.map_rel_iff).2 (hcy i).2
    exact ((pentW_trace c (Set.mem_toFinset.mp hz) i).2 rfl).symm) (by
    intro a ha
    rcases pent_classify hconn hC hp c a with ⟨k,rfl⟩ | hw | hx
    · have hh : ∀ i k : Fin 5, (cycleGraph 5).Adj i k → k = i+1 ∨ k = i-1 := by decide
      rcases hh i k ((c.map_rel_iff).1 ha) with rfl | rfl
      · exact ⟨_, mem_insert_self _ _, Or.inl rfl⟩
      · exact ⟨_, mem_insert_of_mem (mem_insert_self _ _), Or.inl rfl⟩
    · obtain ⟨k,hk⟩ := hw
      have he := (pentW_trace c hk i).1 ha.symm
      subst k
      exact ⟨a, mem_insert_of_mem (mem_insert_of_mem (Set.mem_toFinset.mpr hk)), Or.inl rfl⟩
    · obtain ⟨k,hk⟩ := hx
      have hh : ∀ i k : Fin 5, (i = k ∨ i = k+1) →
          ∃ j, (j = i+1 ∨ j = i-1) ∧ (j = k ∨ j = k+1) := by decide
      obtain ⟨j,hj,hjk⟩ := hh i k ((pentX_trace c hk i).1 ha.symm)
      refine ⟨c j, ?_, Or.inr ((pentX_trace c hk j).2 hjk)⟩
      rcases hj with rfl | rfl
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_insert_self _ _))
  have hc : s.card ≤ 2 + t.card := by
    dsimp [s]
    have h1 := card_insert_le (c (i+1)) (insert (c (i-1)) t)
    have h2 := card_insert_le (c (i-1)) t
    omega
  simpa [t, Nat.card_eq_fintype_card] using hb.trans hc

theorem pentW_support_unique (c : cycleGraph 5 ↪g G) {w : V} {i j : Fin 5}
    (hi : w ∈ kmW G c i) (hj : w ∈ kmW G c j) : i = j :=
  (pentW_trace c hj i).1 ((pentW_trace c hi i).2 rfl)

 theorem pentW_card_sum [Fintype V] (c : cycleGraph 5 ↪g G) :
    (∑ i : Fin 5, Nat.card (kmW G c i)) = Nat.card (pentW c) := by
  classical
  let e : (Σ i : Fin 5, kmW G c i) ≃ pentW c := Equiv.ofBijective
    (fun p => ⟨p.2.val, ⟨p.1,p.2.property⟩⟩) (by
      constructor
      · intro ⟨i,a⟩ ⟨j,b⟩ he
        have hab : a.val = b.val := congrArg Subtype.val he
        have hij := pentW_support_unique c a.property (hab.symm ▸ b.property)
        subst j
        exact congrArg (Sigma.mk i) (Subtype.ext hab)
      · rintro ⟨w,i,hi⟩
        exact ⟨⟨i,⟨w,hi⟩⟩,rfl⟩)
  simpa [Nat.card_eq_fintype_card, Fintype.card_sigma] using Nat.card_congr e

 theorem pentCross_card_sumW [Fintype V] (c : cycleGraph 5 ↪g G)
    [Fintype (pentW c)] :
    (∑ w : pentW c, Nat.card {x : pentX c // G.Adj w.val x.val}) = Nat.card (pentCross c) := by
  classical
  let e : (Σ w : pentW c, {x : pentX c // G.Adj w.val x.val}) ≃ pentCross c :=
    { toFun := fun p => ⟨(p.1,p.2.val),p.2.property⟩
      invFun := fun p => ⟨p.val.1,⟨p.val.2,p.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa [Nat.card_eq_fintype_card, Fintype.card_sigma] using Nat.card_congr e

 theorem pentCross_card_sumX [Fintype V] (c : cycleGraph 5 ↪g G)
    [Fintype (pentX c)] :
    (∑ x : pentX c, Nat.card {w : pentW c // G.Adj w.val x.val}) = Nat.card (pentCross c) := by
  classical
  let e : (Σ x : pentX c, {w : pentW c // G.Adj w.val x.val}) ≃ pentCross c :=
    { toFun := fun p => ⟨(p.2.val,p.1),p.2.property⟩
      invFun := fun p => ⟨p.val.2,⟨p.val.1,p.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa [Nat.card_eq_fintype_card, Fintype.card_sigma] using Nat.card_congr e

/-- Counting the cycle, singleton, pair and cross-edge contributions. The
matching triangles can only improve this inequality. -/
theorem pentagon_mass_count [Fintype V] [DecidableEq V]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (hc6 : ¬ cycleGraph 6 ⊴ G) (c : cycleGraph 5 ↪g G) :
    neighbourhoodIndependenceSum G + Nat.card (pentX c) ≤
      2 * Fintype.card V + 2 * Nat.card (pentCross c) := by
  classical
  have hcy := Finset.sum_le_sum (fun (i : Fin 5) (_ : i ∈ univ) =>
    pentCycle_lambda_le hconn hC hp c i)
  have hw := Finset.sum_le_sum (fun (w : pentW c) (_ : w ∈ univ) =>
    pentW_lambda_le hconn hC hp hc6 c w)
  have hx := Finset.sum_le_sum (fun (x : pentX c) (_ : x ∈ univ) =>
    pentX_lambda_le hconn hC hp c x)
  simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul,
    Fintype.card_fin, pentW_card_sum, pentCross_card_sumW,
    pentCross_card_sumX, mul_one] at hcy hw hx
  have he : neighbourhoodIndependenceSum G =
      (∑ i : Fin 5, lambda G (c i)) +
      (∑ w : pentW c, lambda G w.val) + ∑ x : pentX c, lambda G x.val := by
    unfold neighbourhoodIndependenceSum
    rw [← Fintype.sum_equiv (pentPartition hconn hC hp c)
      (fun x => lambda G (pentPartition hconn hC hp c x)) (lambda G) (fun _ => rfl)]
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    exact (add_assoc _ _ _).symm
  have hn := pent_card hconn hC hp c
  simp only [Nat.card_eq_fintype_card] at hn hcy hw hx ⊢
  omega

/-- The pentagon branch of Theorem 3.6. -/
theorem pentagon_mass_le [Fintype V] [DecidableEq V]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (hc6 : ¬ cycleGraph 6 ⊴ G) (c : cycleGraph 5 ↪g G) :
    neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V + 1 := by
  classical
  have hmass := pentagon_mass_count hconn hC hp hc6 c
  have hb := pentCross_card_le_one hC hp hc6 c
  have hj : Nat.card (pentCross c) ≤ Nat.card (pentX c) := by
    by_cases hh : Nonempty (pentCross c)
    · obtain ⟨p⟩ := hh
      have hpos : 0 < Nat.card (pentX c) := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_pos_iff.mpr ⟨p.val.2⟩
      omega
    · have : IsEmpty (pentCross c) := not_nonempty_iff.mp hh
      simp [Nat.card_eq_fintype_card]
  omega

/-- A cross edge requires two distinct vertices outside the pentagon. -/
theorem pentCross_card_eq_zero_of_order_le_six [Fintype V]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 5 ↪g G) (hn : Fintype.card V ≤ 6) :
    Nat.card (pentCross c) = 0 := by
  classical
  have hc := pent_card hconn hC hp c
  have hempty : IsEmpty (pentCross c) := ⟨by
    intro p
    have hw : 0 < Nat.card (pentW c) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr ⟨p.val.1⟩
    have hx : 0 < Nat.card (pentX c) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_pos_iff.mpr ⟨p.val.2⟩
    omega⟩
  simp [Nat.card_eq_fintype_card]

/-- The sharper small-order pentagon estimate (orders five and six). -/
theorem pentagon_mass_le_small [Fintype V] [DecidableEq V]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (hc6 : ¬ cycleGraph 6 ⊴ G) (c : cycleGraph 5 ↪g G)
    (hn : Fintype.card V ≤ 6) :
    neighbourhoodIndependenceSum G ≤ 2 * Fintype.card V := by
  have hm := pentagon_mass_count hconn hC hp hc6 c
  have hb := pentCross_card_eq_zero_of_order_le_six hconn hC hp c hn
  omega

/-- The singleton-induced graph is a matching, globally across all supports. -/
theorem pentW_degree_le_one [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hC : StrongC4Free G) (hc6 : ¬ cycleGraph 6 ⊴ G)
    (c : cycleGraph 5 ↪g G) [DecidablePred (· ∈ pentW c)] (a : pentW c) :
    (G.induce (pentW c)).degree a ≤ 1 := by
  classical
  rw [← card_neighborFinset_eq_degree]
  apply Finset.card_le_one.mpr
  intro b hb d hd
  have hab : G.Adj a.val b.val := by simpa using hb
  have had : G.Adj a.val d.val := by simpa using hd
  obtain ⟨i,hi⟩ := a.property
  obtain ⟨j,hj⟩ := b.property
  obtain ⟨k,hk⟩ := d.property
  have hij : i = j := by
    by_contra hn
    exact pentTrace_singleton_nonadjacent hC hc6 c hi hj hn hab
  have hik : i = k := by
    by_contra hn
    exact pentTrace_singleton_nonadjacent hC hc6 c hi hk hn had
  subst j; subst k
  exact Subtype.ext (pentTrace_singleton_matching hC c hi hj hk hab had)

/-- At most half of the singleton vertices are matching edges. -/
theorem pentW_matching_count [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hC : StrongC4Free G) (hc6 : ¬ cycleGraph 6 ⊴ G)
    (c : cycleGraph 5 ↪g G) [DecidablePred (· ∈ pentW c)] :
    2 * edgeCount (G.induce (pentW c)) ≤ Nat.card (pentW c) := by
  classical
  simpa [edgeCount, Nat.card_eq_fintype_card] using
    two_mul_edgeFinset_card_le (H := G.induce (pentW c)) (pentW_degree_le_one hC hc6 c)

/-- At order five the induced pentagon already exhausts the graph. -/
theorem pentagon_iso_of_order_five [Fintype V]
    (c : cycleGraph 5 ↪g G) (hn : Fintype.card V = 5) :
    Nonempty (G ≃g cycleGraph 5) := by
  have hs : Function.Surjective c :=
    (Fintype.bijective_iff_injective_and_card c).2 ⟨c.injective, by simpa using hn.symm⟩ |>.surjective
  exact ⟨({ toEquiv := Equiv.ofBijective c ⟨c.injective,hs⟩
            map_rel_iff' := c.map_rel_iff } : cycleGraph 5 ≃g G).symm⟩

/-- Mass equality at order six excludes every pair trace. -/
theorem pentX_empty_of_order_six_equality [Fintype V] [DecidableEq V]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (hc6 : ¬ cycleGraph 6 ⊴ G) (c : cycleGraph 5 ↪g G)
    (hn : Fintype.card V = 6) (hm : neighbourhoodIndependenceSum G = 12) :
    IsEmpty (pentX c) := by
  classical
  have hh := pentagon_mass_count hconn hC hp hc6 c
  have hb := pentCross_card_eq_zero_of_order_le_six hconn hC hp c (by omega)
  have hx : Nat.card (pentX c) = 0 := by omega
  rw [Nat.card_eq_fintype_card] at hx
  exact Fintype.card_eq_zero_iff.mp hx

/-- A unique outside singleton yields the pentagon with one pendant leaf. -/
theorem pentagon_leaf_iso [Fintype V]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (c : cycleGraph 5 ↪g G) (hw : Nat.card (pentW c) = 1)
    (hx : IsEmpty (pentX c)) : Nonempty (G ≃g c5PlusLeaf) := by
  classical
  letI := hx
  have hw' : Fintype.card (pentW c) = 1 := by simpa [Nat.card_eq_fintype_card] using hw
  obtain ⟨w,hu⟩ := Fintype.card_eq_one_iff.mp hw'
  obtain ⟨i,hi⟩ := w.property
  let f : Option (Fin 5) → V := fun a => a.elim w.val (fun j => c (j+i))
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      cases a with
      | none => cases b with
        | none => rfl
        | some k => exact (hi.1 (k+i) hab.symm).elim
      | some j => cases b with
        | none => exact (hi.1 (j+i) hab).elim
        | some k =>
          have hh : j+i = k+i := c.injective hab
          exact congrArg some (add_right_cancel hh)
    · intro a
      rcases pent_classify hconn hC hp c a with ⟨j,rfl⟩ | ha | ha
      · refine ⟨some (j-i), ?_⟩
        dsimp [f]
        rw [sub_add_cancel]
      · have hh := hu ⟨a,ha⟩
        exact ⟨none, congrArg Subtype.val hh.symm⟩
      · exact (hx.false ⟨a,ha⟩).elim
  have hrot : ∀ i j k : Fin 5, (cycleGraph 5).Adj (j+i) (k+i) ↔
      (cycleGraph 5).Adj j k := by decide
  have hadj : ∀ a b, G.Adj (f a) (f b) ↔ c5PlusLeaf.Adj a b := by
    intro a b
    cases a with
    | none => cases b with
      | none => simp [f,c5PlusLeaf,addLeaf,simpleOf]
      | some k =>
        have ht := pentW_trace c hi (k+i)
        have he : k+i = i ↔ k=0 := by constructor <;> intro h <;> simpa using h
        simpa [f,c5PlusLeaf,addLeaf,simpleOf,he] using ht
    | some j => cases b with
      | none =>
        have ht := pentW_trace c hi (j+i)
        have he : j+i = i ↔ j=0 := by constructor <;> intro h <;> simpa using h
        simpa [f,c5PlusLeaf,addLeaf,simpleOf,he,adj_comm] using ht
      | some k =>
        have hh := (c.map_rel_iff (a := j+i) (b := k+i)).trans (hrot i j k)
        have hne : (cycleGraph 5).Adj j k → j ≠ k := fun h => h.ne
        simpa [f,c5PlusLeaf,addLeaf,simpleOf,adj_comm, and_iff_right_of_imp hne] using hh
  exact ⟨({ toEquiv := Equiv.ofBijective f hf
            map_rel_iff' := fun {a b} => hadj a b } : c5PlusLeaf ≃g G).symm⟩

/-- Equality in the order-six pentagon branch has the unique leaf model. -/
theorem pentagon_iso_of_order_six_equality [Fintype V] [DecidableEq V]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 6)
    (hc6 : ¬ cycleGraph 6 ⊴ G) (c : cycleGraph 5 ↪g G)
    (hn : Fintype.card V = 6) (hm : neighbourhoodIndependenceSum G = 12) :
    Nonempty (G ≃g c5PlusLeaf) := by
  classical
  have hx := pentX_empty_of_order_six_equality hconn hC hp hc6 c hn hm
  letI := hx
  have hh := pent_card hconn hC hp c
  have hzero : Nat.card (pentX c) = 0 := by simp
  have hw : Nat.card (pentW c) = 1 := by omega
  exact pentagon_leaf_iso hconn hC hp c hw hx

end InducedPaths
