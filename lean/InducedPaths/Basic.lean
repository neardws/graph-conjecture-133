/-
Proved preliminary facts: induced-path order, the strong `C₄`-free identities of Lemma 2.1,
and the arithmetic remark at radius 4.
-/
module

public import InducedPaths.Axioms
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Chord
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
public import Mathlib.Data.Fin.Embedding
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

open scoped SimpleGraph
open Finset SimpleGraph

set_option linter.style.haveILetI false

@[expose] public section

namespace InducedPaths

variable {V : Type*} {G : SimpleGraph V}

/-! ### Induced paths -/

/-- The initial segment `Fin m ↪ Fin n` is an induced-path embedding. -/
def pathGraph_mono {m n : ℕ} (h : m ≤ n) : pathGraph m ↪g pathGraph n where
  toEmbedding := Fin.castLEEmb h
  map_rel_iff' := by
    intro a b
    simp [pathGraph_adj, Fin.val_castLE]

lemma pathGraph_zero_isIndContained (G : SimpleGraph V) : pathGraph 0 ⊴ G :=
  Nonempty.intro {
    toEmbedding := Function.Embedding.ofIsEmpty (α := Fin 0)
    map_rel_iff' := by
      intro a
      exact a.elim0
  }

lemma isIndContained_path_card_le [Fintype V] {n : ℕ} (h : pathGraph n ⊴ G) :
    n ≤ Fintype.card V := by
  obtain ⟨f⟩ := h
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective (f : Fin n → V) f.injective

lemma isIndContained_path_le {m n : ℕ} (h : m ≤ n) (hg : pathGraph n ⊴ G) :
    pathGraph m ⊴ G := by
  obtain ⟨f⟩ := hg
  exact ⟨(pathGraph_mono h).trans f⟩

lemma inducedPathOrder_bddAbove [Fintype V] (G : SimpleGraph V) :
    BddAbove {n | pathGraph n ⊴ G} :=
  ⟨Fintype.card V, fun _ hn => isIndContained_path_card_le hn⟩

lemma inducedPathOrder_witness [Fintype V] (G : SimpleGraph V) :
    pathGraph (inducedPathOrder G) ⊴ G := by
  have hmem :=
    Nat.sSup_mem ⟨0, pathGraph_zero_isIndContained G⟩ (inducedPathOrder_bddAbove G)
  simpa [inducedPathOrder] using hmem

lemma inducedPathOrder_le_card [Fintype V] (G : SimpleGraph V) :
    inducedPathOrder G ≤ Fintype.card V :=
  csSup_le ⟨0, pathGraph_zero_isIndContained G⟩ fun _ hn => isIndContained_path_card_le hn

/-- `Pₖ`-free means the induced-path order is strictly less than `k`. -/
theorem isPkFree_iff_inducedPathOrder_lt [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    IsPkFree G k ↔ inducedPathOrder G < k := by
  constructor
  · intro h
    rw [lt_iff_not_ge]
    intro hk
    exact h (isIndContained_path_le hk (inducedPathOrder_witness G))
  · intro hk hcont
    exact not_lt_of_ge (le_csSup (inducedPathOrder_bddAbove G) hcont) hk

lemma isIndContained_iff_of_iso {W : Type*} {H : SimpleGraph W} (e : G ≃g H) (n : ℕ) :
    pathGraph n ⊴ G ↔ pathGraph n ⊴ H := by
  constructor
  · intro ⟨f⟩
    exact ⟨f.trans e.toEmbedding⟩
  · intro ⟨f⟩
    exact ⟨f.trans e.symm.toEmbedding⟩

theorem inducedPathOrder_iso {W : Type*} {H : SimpleGraph W} (e : G ≃g H) :
    inducedPathOrder G = inducedPathOrder H := by
  have hset : {n | pathGraph n ⊴ G} = {n | pathGraph n ⊴ H} := by
    ext n
    exact isIndContained_iff_of_iso e n
  simp [inducedPathOrder, hset]

lemma strongC4Free_no_induced_C4 (h : StrongC4Free G) : ¬ cycleGraph 4 ⊴ G := by
  intro ⟨f⟩
  exact h ⟨f.toCopy⟩

/-! ### Lemma 2.1 -/

private def c4Verts {V : Type*} (a b c d : V) : Fin 4 → V := fun i =>
  if i = 0 then a else if i = 1 then b else if i = 2 then c else d

private lemma c4_adj_iff (i j : Fin 4) :
    (cycleGraph 4).Adj i j ↔
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨ (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3) := by
  fin_cases i <;> fin_cases j <;> decide

lemma fourCycle_isContained {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : cycleGraph 4 ⊑ G := by
  have hab' : a ≠ b := hab.ne
  have hbc' : b ≠ c := hbc.ne
  have hcd' : c ≠ d := hcd.ne
  have hda' : d ≠ a := hda.ne
  refine ⟨{
    toHom := {
      toFun := c4Verts a b c d
      map_rel' := by
        intro i j hij
        rcases (c4_adj_iff i j).1 hij with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simpa [c4Verts] using hab
        · simpa [c4Verts] using hab.symm
        · simpa [c4Verts] using hbc
        · simpa [c4Verts] using hbc.symm
        · simpa [c4Verts] using hcd
        · simpa [c4Verts] using hcd.symm
        · simpa [c4Verts] using hda
        · simpa [c4Verts] using hda.symm }
    injective' := by
      intro i j hij
      by_contra hne
      fin_cases i <;> fin_cases j <;> simp [c4Verts] at hij <;> first
        | exact hne rfl
        | exact hab' hij
        | exact hab' hij.symm
        | exact hbc' hij
        | exact hbc' hij.symm
        | exact hcd' hij
        | exact hcd' hij.symm
        | exact hda' hij
        | exact hda' hij.symm
        | exact hac hij
        | exact hac hij.symm
        | exact hbd hij
        | exact hbd hij.symm
  }⟩

/-- Lemma 2.1(1): distinct vertices have at most one common neighbour. -/
theorem commonNeighbors_subsingleton (hG : StrongC4Free G) {x y : V} (hxy : x ≠ y) :
    (G.commonNeighbors x y).Subsingleton := by
  intro w hw w' hw'
  by_contra hne
  apply hG
  have hxw : G.Adj x w := hw.1
  have hyw : G.Adj y w := hw.2
  have hxw' : G.Adj x w' := hw'.1
  have hyw' : G.Adj y w' := hw'.2
  exact fourCycle_isContained hxw hyw.symm hyw' hxw'.symm hxy hne


/-- In a strong `C₄`-free graph every vertex of `G[N(v)]` has degree at most 1,
so that neighbourhood is a matching plus isolated vertices. -/
theorem neighborhood_degree_le_one (hG : StrongC4Free G) (v : V) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (w : G.neighborSet v) :
    (G.induce (G.neighborSet v)).degree w ≤ 1 := by
  let H := G.induce (G.neighborSet v)
  rw [← card_neighborFinset_eq_degree]
  by_contra hlt
  have hcard : 1 < (H.neighborFinset w).card := Nat.lt_of_not_ge hlt
  obtain ⟨a, b, ha, hb, hab⟩ := Finset.one_lt_card_iff.mp hcard
  have hav : G.Adj v ↑a := a.2
  have hbv : G.Adj v ↑b := b.2
  have haw : G.Adj ↑w ↑a := by
    have hH : H.Adj w a := (H.mem_neighborFinset w a).1 ha
    simpa [H, induce_adj] using hH
  have hbw : G.Adj ↑w ↑b := by
    have hH : H.Adj w b := (H.mem_neighborFinset w b).1 hb
    simpa [H, induce_adj] using hH
  have hne : ↑w ≠ v := (show G.Adj v ↑w from w.2).ne.symm
  have hsub := commonNeighbors_subsingleton hG hne.symm
  have hmem : ↑a ∈ G.commonNeighbors v ↑w := by
    rw [mem_commonNeighbors]
    exact ⟨hav, haw⟩
  have hmem' : ↑b ∈ G.commonNeighbors v ↑w := by
    rw [mem_commonNeighbors]
    exact ⟨hbv, hbw⟩
  exact hab (Subtype.ext (hsub hmem hmem'))

lemma sym2_out_ne {e : Sym2 V} (h : ¬ e.IsDiag) : e.out.1 ≠ e.out.2 := by
  intro heq
  apply h
  rw [← Sym2.mk_fst_out_snd_out e]
  exact Sym2.mk_isDiag_iff.mpr heq

lemma sym2_eq_of_outs {e e' : Sym2 V} (h1 : e.out.1 = e'.out.1) (h2 : e.out.2 = e'.out.2) :
    e = e' :=
  (Sym2.mk_fst_out_snd_out e).symm.trans
    (((Sym2.eq_iff).2 (Or.inl ⟨h1, h2⟩)).trans (Sym2.mk_fst_out_snd_out e'))

section Matching

variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

omit [DecidableEq W] in
lemma adj_out_of_mem (e : Sym2 W) (he : e ∈ H.edgeFinset) : H.Adj e.out.1 e.out.2 := by
  have : s(e.out.1, e.out.2) ∈ H.edgeSet := by
    rw [Sym2.mk_fst_out_snd_out e]
    exact (mem_edgeFinset.mp he)
  simpa [mem_edgeSet] using this

lemma pair_degree_ge_two {u a b : W} (h1 : H.Adj u a) (h2 : H.Adj u b) (hab : a ≠ b) :
    2 ≤ H.degree u := by
  have hsub : ({a, b} : Finset W) ⊆ H.neighborFinset u := by
    intro w hw
    rw [mem_insert, mem_singleton] at hw
    rcases hw with hwa | hwb
    · rw [hwa]
      exact (H.mem_neighborFinset u a).2 h1
    · rw [hwb]
      exact (H.mem_neighborFinset u b).2 h2
  have hc : ({a, b} : Finset W).card = 2 := (card_pair_eq_two_iff).2 hab
  have hle : ({a, b} : Finset W).card ≤ (H.neighborFinset u).card := card_le_card hsub
  have hd : (H.neighborFinset u).card = H.degree u :=
    card_neighborFinset_eq_degree (G := H) (v := u)
  omega

/-- The chosen first endpoint of each edge. Injective when every degree is at most 1. -/
noncomputable def endpointImage : Finset W :=
  H.edgeFinset.image fun e => e.out.1

lemma endpointImage_injOn (hdeg : ∀ v, H.degree v ≤ 1) :
    Set.InjOn (fun e : Sym2 W => e.out.1) (H.edgeFinset : Set (Sym2 W)) := by
  intro e he e' he' hEq
  by_contra hne
  have hEq' : e.out.1 = e'.out.1 := hEq
  have h1 : H.Adj e.out.1 e.out.2 := adj_out_of_mem H e he
  have h2 : H.Adj e.out.1 e'.out.2 := hEq'.symm ▸ adj_out_of_mem H e' he'
  have hpartners : e.out.2 ≠ e'.out.2 := by
    intro hp
    exact hne (sym2_eq_of_outs hEq' hp)
  exact (hdeg e.out.1).not_gt <| Nat.lt_of_succ_le <|
    pair_degree_ge_two H h1 h2 hpartners

lemma endpointImage_card (hdeg : ∀ v, H.degree v ≤ 1) :
    (endpointImage H).card = H.edgeFinset.card :=
  card_image_of_injOn (endpointImage_injOn H hdeg)

lemma endpoint_snd_not_mem (hdeg : ∀ v, H.degree v ≤ 1) {e : Sym2 W}
    (he : e ∈ H.edgeFinset) : e.out.2 ∉ endpointImage H := by
  intro hmem
  obtain ⟨f, hf, hfe⟩ := mem_image.mp hmem
  have hfe' : f.out.1 = e.out.2 := hfe
  have hne : e ≠ f := by
    intro hef
    apply sym2_out_ne (H.not_isDiag_of_mem_edgeFinset he)
    exact (congrArg (fun g : Sym2 W => g.out.1) hef).trans hfe'
  have h1 : H.Adj e.out.2 e.out.1 := (adj_out_of_mem H e he).symm
  have h2 : H.Adj e.out.2 f.out.2 := hfe' ▸ adj_out_of_mem H f hf
  have hpartners : e.out.1 ≠ f.out.2 := by
    intro hp
    apply hne
    calc
      e = s(e.out.1, e.out.2) := (Sym2.mk_fst_out_snd_out e).symm
      _ = s(f.out.2, f.out.1) := (Sym2.eq_iff).2 (Or.inl ⟨hp, hfe'.symm⟩)
      _ = s(f.out.1, f.out.2) := Sym2.eq_swap
      _ = f := Sym2.mk_fst_out_snd_out f
  exact (hdeg e.out.2).not_gt <| Nat.lt_of_succ_le <|
    pair_degree_ge_two H h1 h2 hpartners

noncomputable def keptVertices : Finset W :=
  Finset.univ \ endpointImage H

lemma keptVertices_card (hdeg : ∀ v, H.degree v ≤ 1) :
    (keptVertices H).card = Fintype.card W - H.edgeFinset.card := by
  rw [keptVertices, card_sdiff_of_subset (subset_univ _), card_univ, endpointImage_card H hdeg]

lemma keptVertices_indep : H.IsIndepSet (keptVertices H : Set W) := by
  rw [isIndepSet_iff]
  intro x hx y hy hxy hadj
  have he : s(x, y) ∈ H.edgeFinset := by
    rw [mem_edgeFinset, mem_edgeSet]
    exact hadj
  have hmem : s(x, y).out.1 = x ∨ s(x, y).out.1 = y := by
    have := Sym2.out_fst_mem (s(x, y))
    simpa [Sym2.mem_iff] using this
  have hx' : x ∈ keptVertices H := by simpa [keptVertices] using hx
  have hy' : y ∈ keptVertices H := by simpa [keptVertices] using hy
  have hxk : x ∉ endpointImage H := (mem_sdiff.mp (by rw [keptVertices] at hx'; exact hx')).2
  have hyk : y ∉ endpointImage H := (mem_sdiff.mp (by rw [keptVertices] at hy'; exact hy')).2
  rcases hmem with h | h
  · exact hxk (mem_image.mpr ⟨s(x, y), he, h⟩)
  · exact hyk (mem_image.mpr ⟨s(x, y), he, h⟩)

lemma indep_card_le_kept (hdeg : ∀ v, H.degree v ≤ 1) {s : Finset W}
    (hs : H.IsIndepSet (s : Set W)) : s.card ≤ (keptVertices H).card := by
  set excl : Finset W := endpointImage H
  set kept : Finset W := keptVertices H
  set bad : Finset (Sym2 W) := H.edgeFinset.filter fun e => e.out.1 ∈ s
  have hbad : Set.InjOn (fun e : Sym2 W => e.out.1) (bad : Set _) :=
    (endpointImage_injOn H hdeg).mono fun _ he => (mem_filter.mp he).1
  have himage : bad.image (fun e => e.out.1) = s ∩ excl := by
    ext x
    constructor
    · intro hx
      obtain ⟨e, he, heq⟩ := mem_image.mp hx
      have heq' : e.out.1 = x := heq
      rw [mem_inter]
      exact ⟨heq' ▸ (mem_filter.mp he).2, mem_image.mpr ⟨e, (mem_filter.mp he).1, heq'⟩⟩
    · intro hx
      rw [mem_inter] at hx
      obtain ⟨e, he, heq⟩ := mem_image.mp hx.2
      have heq' : e.out.1 = x := heq
      exact mem_image.mpr ⟨e, mem_filter.mpr ⟨he, heq'.symm ▸ hx.1⟩, heq'⟩
  have hbadcard : bad.card = (s ∩ excl).card := by
    rw [← card_image_of_injOn hbad, himage]
  have hpartner : ∀ e ∈ bad, e.out.2 ∈ kept \ s := by
    intro e he
    have heE : e ∈ H.edgeFinset := (mem_filter.mp he).1
    refine mem_sdiff.mpr ⟨?_, ?_⟩
    · rw [show kept = keptVertices H from rfl, keptVertices]
      exact mem_sdiff.mpr ⟨mem_univ _, endpoint_snd_not_mem H hdeg heE⟩
    · intro hsnd
      have hadj : H.Adj e.out.1 e.out.2 := adj_out_of_mem H e heE
      have h1 : e.out.1 ∈ (s : Set W) := by simpa using (mem_filter.mp he).2
      have h2 : e.out.2 ∈ (s : Set W) := by simpa using hsnd
      have hne : e.out.1 ≠ e.out.2 := sym2_out_ne (H.not_isDiag_of_mem_edgeFinset heE)
      rw [isIndepSet_iff] at hs
      exact hs h1 h2 hne hadj
  have hinjP : Set.InjOn (fun e : Sym2 W => e.out.2) (bad : Set _) := by
    intro e he e' he' hEq
    have hEq' : e.out.2 = e'.out.2 := hEq
    have heE : e ∈ H.edgeFinset := (mem_filter.mp he).1
    have heE' : e' ∈ H.edgeFinset := (mem_filter.mp he').1
    by_contra hne
    have hp : e.out.1 ≠ e'.out.1 := by
      intro h
      exact hne (sym2_eq_of_outs h hEq')
    have h1 : H.Adj e.out.2 e.out.1 := (adj_out_of_mem H e heE).symm
    have h2 : H.Adj e.out.2 e'.out.1 := hEq' ▸ (adj_out_of_mem H e' heE').symm
    exact (hdeg e.out.2).not_gt <| Nat.lt_of_succ_le <| pair_degree_ge_two H h1 h2 hp
  have hpartcard : bad.card ≤ (kept \ s).card := by
    rw [← card_image_of_injOn hinjP]
    refine card_le_card ?_
    intro x hx
    obtain ⟨e, he, heq⟩ := mem_image.mp hx
    have heq' : e.out.2 = x := heq
    exact heq' ▸ hpartner e he
  have hunion : (s ∩ excl) ∪ (s ∩ kept) = s := by
    ext x
    constructor
    · intro hx
      rw [mem_union] at hx
      rcases hx with hx | hx
      · exact (mem_inter.mp hx).1
      · exact (mem_inter.mp hx).1
    · intro hx
      by_cases hxe : x ∈ excl
      · exact mem_union.mpr (Or.inl (mem_inter.mpr ⟨hx, hxe⟩))
      · apply mem_union.mpr
        refine Or.inr (mem_inter.mpr ⟨hx, ?_⟩)
        rw [show kept = keptVertices H from rfl, keptVertices]
        exact mem_sdiff.mpr ⟨mem_univ _, hxe⟩
  have hdj : Disjoint (s ∩ excl) (s ∩ kept) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (mem_sdiff.mp (mem_inter.mp hy).2).2 (mem_inter.mp hx).2
  have hsplit : s.card = (s ∩ excl).card + (s ∩ kept).card := by
    have : ((s ∩ excl) ∪ (s ∩ kept)).card = (s ∩ excl).card + (s ∩ kept).card :=
      card_union_of_disjoint hdj
    rw [← this, hunion]
  have hunionK : (kept \ s) ∪ (s ∩ kept) = kept := by
    ext x
    constructor
    · intro hx
      rw [mem_union] at hx
      rcases hx with hx | hx
      · exact (mem_sdiff.mp hx).1
      · exact (mem_inter.mp hx).2
    · intro hk
      by_cases hxs : x ∈ s
      · exact mem_union.mpr (Or.inr (mem_inter.mpr ⟨hxs, hk⟩))
      · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨hk, hxs⟩))
  have hdjK : Disjoint (kept \ s) (s ∩ kept) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (mem_sdiff.mp hx).2 (mem_inter.mp hy).1
  have hkept : (kept \ s).card + (s ∩ kept).card = kept.card := by
    rw [← card_union_of_disjoint hdjK, hunionK]
  calc
    s.card = (s ∩ excl).card + (s ∩ kept).card := hsplit
    _ = bad.card + (s ∩ kept).card := by rw [hbadcard]
    _ ≤ (kept \ s).card + (s ∩ kept).card := Nat.add_le_add_right hpartcard _
    _ = kept.card := hkept

/-- A finite graph of maximum degree at most 1 has `α + e = n`. -/
theorem indepNum_add_edgeCount_of_degree_le_one (hdeg : ∀ v, H.degree v ≤ 1) :
    H.indepNum + H.edgeFinset.card = Fintype.card W := by
  have hle : H.edgeFinset.card ≤ Fintype.card W := by
    rw [← endpointImage_card H hdeg]
    exact card_le_card (subset_univ _)
  have hlow : Fintype.card W - H.edgeFinset.card ≤ H.indepNum := by
    rw [← keptVertices_card H hdeg]
    exact IsIndepSet.card_le_indepNum (keptVertices_indep H)
  have hup : H.indepNum ≤ Fintype.card W - H.edgeFinset.card := by
    obtain ⟨s, hs⟩ := exists_isNIndepSet_indepNum (G := H)
    rw [← hs.card_eq, ← keptVertices_card H hdeg]
    exact indep_card_le_kept H hdeg hs.isIndepSet
  omega

end Matching

private def oppA [DecidableEq V] (v : V) (s : Finset V) (a : V) : Prop :=
  ∃ b, a ≠ b ∧ s.erase v = {a, b}

private def oppB [DecidableEq V] [Nonempty V] (v : V) (s : Finset V) (b : V) : Prop :=
  let a := Classical.epsilon (oppA v s)
  a ≠ b ∧ s.erase v = {a, b}

private noncomputable def oppositeEdge [DecidableEq V] [Nonempty V] (v : V) (s : Finset V) :
    Sym2 V :=
  s(Classical.epsilon (oppA v s), Classical.epsilon (oppB v s))

private lemma oppositeEdge_eq [DecidableEq V] [Nonempty V] {v a b : V} {s : Finset V}
    (hne : a ≠ b) (hs : s.erase v = {a, b}) : oppositeEdge v s = s(a, b) := by
  have hex : ∃ a', oppA v s a' := ⟨a, b, hne, hs⟩
  have ha : oppA v s (Classical.epsilon (oppA v s)) := Classical.epsilon_spec hex
  have hb : oppB v s (Classical.epsilon (oppB v s)) := Classical.epsilon_spec ha
  set a' : V := Classical.epsilon (oppA v s)
  set b' : V := Classical.epsilon (oppB v s)
  change s(a', b') = s(a, b)
  have hset : ({a', b'} : Finset V) = {a, b} := by
    rw [← hb.2, hs]
  have ha_mem : a' = a ∨ a' = b := by
    have : a' ∈ ({a, b} : Finset V) := by rw [← hset]; simp
    simpa [mem_insert, mem_singleton] using this
  have hb_mem : b' = a ∨ b' = b := by
    have : b' ∈ ({a, b} : Finset V) := by rw [← hset]; simp
    simpa [mem_insert, mem_singleton] using this
  cases ha_mem with
  | inl h1 =>
      cases hb_mem with
      | inl h2 => exact False.elim (hb.1 (h1.trans h2.symm))
      | inr h2 => simp [h1, h2]
  | inr h1 =>
      cases hb_mem with
      | inl h2 =>
          rw [h1, h2]
          exact Sym2.eq_swap
      | inr h2 => exact False.elim (hb.1 (h1.trans h2.symm))

lemma cliqueAdj {s : Finset V} (hs : G.IsClique (s : Set V)) {a b : V}
    (ha : a ∈ s) (hb : b ∈ s) (hne : a ≠ b) : G.Adj a b :=
  hs ha hb hne

/-- Triangles at `v` are the edges of `G[N(v)]`. This holds in every simple graph. -/
theorem trianglesAt_eq_neighborEdges [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    trianglesAt G v = edgeCount (G.induce (G.neighborSet v)) := by
  haveI : Nonempty V := ⟨v⟩
  let tris : Finset (Finset V) := {s ∈ G.cliqueFinset 3 | v ∈ s}
  let edges : Finset (Sym2 V) := {e ∈ G.edgeFinset | e.toFinset ⊆ G.neighborFinset v}
  have hinduce : edges.card = edgeCount (G.induce (G.neighborSet v)) := by
    have hmap := map_edgeFinset_induce (G := G) (s := G.neighborSet v)
    have hcard := congrArg Finset.card hmap
    rw [Finset.card_map] at hcard
    have hfilter :=
      filter_edgeFinset_toFinset_subset (G := G) ((G.neighborSet v).toFinset)
    have hedges : edges = G.edgeFinset ∩ (G.neighborSet v).toFinset.sym2 := by
      unfold edges
      rw [neighborFinset_def]
      exact hfilter
    rw [hedges, edgeCount]
    exact hcard.symm
  have hbij : tris.card = edges.card := by
    refine card_bij'
      (fun s _ => oppositeEdge v s)
      (fun e _ => insert v e.toFinset)
      ?_ ?_ ?_ ?_
    · intro s hs
      have hv : v ∈ s := (mem_filter.mp hs).2
      have hcl : G.IsNClique 3 s := mem_cliqueFinset_iff.mp (mem_filter.mp hs).1
      have hcard : (s.erase v).card = 2 := by
        rw [card_erase_of_mem hv, hcl.card_eq]
      obtain ⟨a, b, hne, herase⟩ := card_eq_two.mp hcard
      have ha : a ∈ s.erase v := by simp [herase]
      have hb : b ∈ s.erase v := by simp [herase]
      have has : a ∈ s := mem_of_mem_erase ha
      have hbs : b ∈ s := mem_of_mem_erase hb
      have han : a ≠ v := ne_of_mem_erase ha
      have hbn : b ≠ v := ne_of_mem_erase hb
      have hab : G.Adj a b := cliqueAdj hcl.isClique has hbs hne
      have hav : G.Adj v a := cliqueAdj hcl.isClique hv has han.symm
      have hbv : G.Adj v b := cliqueAdj hcl.isClique hv hbs hbn.symm
      rw [oppositeEdge_eq hne herase]
      refine mem_filter.mpr ⟨?_, ?_⟩
      · rw [mem_edgeFinset, mem_edgeSet]
        exact hab
      · rw [Sym2.toFinset_mk_eq]
        intro x hx
        rw [mem_insert, mem_singleton] at hx
        rcases hx with hxa | hxb
        · rw [hxa]
          exact (G.mem_neighborFinset v a).2 hav
        · rw [hxb]
          exact (G.mem_neighborFinset v b).2 hbv
    · intro e he
      have heE : e ∈ G.edgeFinset := (mem_filter.mp he).1
      have hsub : e.toFinset ⊆ G.neighborFinset v := (mem_filter.mp he).2
      have hne : e.out.1 ≠ e.out.2 := sym2_out_ne (G.not_isDiag_of_mem_edgeFinset heE)
      have hto : e.toFinset = {e.out.1, e.out.2} := by
        conv_lhs => rw [← Sym2.mk_fst_out_snd_out e]
        exact Sym2.toFinset_mk_eq
      have h1 : G.Adj v e.out.1 := (G.mem_neighborFinset v e.out.1).1 <|
        hsub (by simp [hto])
      have h2 : G.Adj v e.out.2 := (G.mem_neighborFinset v e.out.2).1 <|
        hsub (by simp [hto])
      have hadj : G.Adj e.out.1 e.out.2 := adj_out_of_mem G e heE
      have hvmem : v ∉ e.toFinset := by
        intro hv
        exact notMem_neighborFinset_self G v (hsub hv)
      have hcard : (insert v e.toFinset).card = 3 := by
        rw [card_insert_of_notMem hvmem, hto, card_pair_eq_two_iff.mpr hne]
      have hclique : G.IsClique ↑(insert v e.toFinset) := by
        rw [isClique_iff]
        intro x hx y hy hxy
        have hx' : x = v ∨ x ∈ e.toFinset := by
          simpa [mem_coe, mem_insert] using hx
        have hy' : y = v ∨ y ∈ e.toFinset := by
          simpa [mem_coe, mem_insert] using hy
        rcases hx' with rfl | hx'
        · rcases hy' with rfl | hy'
          · exact (hxy rfl).elim
          · rw [hto] at hy'
            rw [mem_insert, mem_singleton] at hy'
            rcases hy' with rfl | rfl
            · exact h1
            · exact h2
        · rcases hy' with rfl | hy'
          · rw [hto] at hx'
            rw [mem_insert, mem_singleton] at hx'
            rcases hx' with rfl | rfl
            · exact h1.symm
            · exact h2.symm
          · rw [hto] at hx' hy'
            rw [mem_insert, mem_singleton] at hx' hy'
            rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
            · exact (hxy rfl).elim
            · exact hadj
            · exact hadj.symm
            · exact (hxy rfl).elim
      exact mem_filter.mpr ⟨mem_cliqueFinset_iff.mpr ⟨hclique, hcard⟩, mem_insert_self _ _⟩
    · intro s hs
      have hv : v ∈ s := (mem_filter.mp hs).2
      have hcl : G.IsNClique 3 s := mem_cliqueFinset_iff.mp (mem_filter.mp hs).1
      have hcard : (s.erase v).card = 2 := by
        rw [card_erase_of_mem hv, hcl.card_eq]
      obtain ⟨a, b, hne, herase⟩ := card_eq_two.mp hcard
      rw [oppositeEdge_eq hne herase, Sym2.toFinset_mk_eq, ← herase, insert_erase hv]
    · intro e he
      have heE : e ∈ G.edgeFinset := (mem_filter.mp he).1
      have hsub : e.toFinset ⊆ G.neighborFinset v := (mem_filter.mp he).2
      have hne : e.out.1 ≠ e.out.2 := sym2_out_ne (G.not_isDiag_of_mem_edgeFinset heE)
      have hvmem : v ∉ e.toFinset := fun hv => notMem_neighborFinset_self G v (hsub hv)
      have herase : (insert v e.toFinset).erase v = e.toFinset := erase_insert hvmem
      have hto : e.toFinset = {e.out.1, e.out.2} := by
        conv_lhs => rw [← Sym2.mk_fst_out_snd_out e]
        exact Sym2.toFinset_mk_eq
      rw [oppositeEdge_eq hne (herase.trans hto), Sym2.mk_fst_out_snd_out]
  simpa [trianglesAt, tris] using hbij.trans hinduce

/-- Lemma 2.1(2): `λ(v) + t(v) = d(v)`. -/
theorem lambda_add_trianglesAt (hG : StrongC4Free G) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (v : V) : lambda G v + trianglesAt G v = G.degree v := by
  let H := G.induce (G.neighborSet v)
  have hdeg : ∀ w, H.degree w ≤ 1 := fun w => neighborhood_degree_le_one hG v w
  have hsum := indepNum_add_edgeCount_of_degree_le_one H hdeg
  have hcard : Fintype.card (G.neighborSet v) = G.degree v := G.card_neighborSet_eq_degree v
  have he : H.edgeFinset.card = trianglesAt G v := (trianglesAt_eq_neighborEdges (G := G) v).symm
  have hlam : H.indepNum = lambda G v := rfl
  simpa [hlam, he, hcard] using hsum

/-- Lemma 2.1(2): `λ(v) = d(v) - t(v)`. -/
theorem lambda_eq_degree_sub_trianglesAt (hG : StrongC4Free G) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (v : V) : lambda G v = G.degree v - trianglesAt G v := by
  have h := lambda_add_trianglesAt hG v
  omega

/-- Lemma 2.1(2), the component-count sentence. `λ(v) = d(v) - t(v)` and the degree bound
are proved; the identification with the number of components of `G[N(v)]` is not. -/
theorem lambda_eq_ncard_components (hG : StrongC4Free G) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (v : V) :
    Nat.card (G.induce (G.neighborSet v)).ConnectedComponent = lambda G v := by
  sorry

lemma sum_trianglesAt [Fintype V] [DecidableEq V] [DecidableRel G.Adj] :
    ∑ v, trianglesAt G v = 3 * triangleCount G := by
  have hstep : ∀ v, trianglesAt G v =
      ∑ s ∈ G.cliqueFinset 3, if v ∈ s then 1 else 0 := by
    intro v
    simp [trianglesAt, sum_boole]
  calc
    ∑ v, trianglesAt G v
        = ∑ v, ∑ s ∈ G.cliqueFinset 3, if v ∈ s then 1 else 0 := by
          simp_rw [hstep]
    _ = ∑ s ∈ G.cliqueFinset 3, ∑ v, if v ∈ s then 1 else 0 := sum_comm
    _ = ∑ s ∈ G.cliqueFinset 3, s.card := by
          refine sum_congr rfl ?_
          intro s _
          rw [sum_boole, filter_univ_mem]
          exact Nat.cast_id _
    _ = ∑ s ∈ G.cliqueFinset 3, 3 := by
          refine sum_congr rfl ?_
          intro s hs
          exact (mem_cliqueFinset_iff.mp hs).card_eq
    _ = (G.cliqueFinset 3).card * 3 := sum_const_nat (fun _ _ => rfl)
    _ = 3 * triangleCount G := by rw [triangleCount, Nat.mul_comm]

/-- Lemma 2.1(3): `S(G) = 2e(G) - 3T(G)`. -/
theorem strongC4Free_S_identity (hG : StrongC4Free G) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] :
    neighbourhoodIndependenceSum G = 2 * edgeCount G - 3 * triangleCount G := by
  have hle : ∀ v ∈ (univ : Finset V), trianglesAt G v ≤ G.degree v := by
    intro v _
    have h := lambda_add_trianglesAt hG v
    omega
  have hlam : ∑ v, lambda G v = ∑ v, (G.degree v - trianglesAt G v) := by
    refine sum_congr rfl ?_
    intro v _
    exact lambda_eq_degree_sub_trianglesAt hG v
  rw [neighbourhoodIndependenceSum, hlam, sum_tsub_distrib _ hle, sum_degrees_eq_twice_card_edges,
    sum_trianglesAt]
  simp [edgeCount, triangleCount]

/-! ### Small consequences -/

/-- Lemma 2.8, the case `k = 6` of Camby–Schaudt. -/
theorem lemma_2_8 (hconn : G.Connected) (hp : IsPkFree G 6) :
    ∃ X : Set V, (G.induce X).Connected ∧
      (∀ v, ∃ x ∈ X, v = x ∨ G.Adj v x) ∧
      (IsPkFree (G.induce X) 4 ∨ Nonempty ((G.induce X) ≃g cycleGraph 6)) :=
  camby_schaudt G 6 (by omega) hconn hp

/-- Remark 4.6. The inequality is arithmetic once `r = 4`, `p ≥ 8` and `ℓ ≤ 4`. -/
theorem remark_4_6 [Fintype V] [DecidableEq V]
    (_hconn : G.Connected) (_hC : StrongC4Free G) (hr : radiusNat G = 4)
    (hp : 8 ≤ inducedPathOrder G) (hell : ell G ≤ 4) :
    (inducedPathOrder G : ℚ) ≥ (radiusNat G : ℚ) + ell G := by
  have hp' : (8 : ℚ) ≤ inducedPathOrder G := by exact_mod_cast hp
  have hr' : (radiusNat G : ℚ) = 4 := by exact_mod_cast hr
  linarith

end InducedPaths
