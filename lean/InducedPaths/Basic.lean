/-
Proved preliminary facts: induced-path order, the strong `C₄`-free identities of Lemma 2.1,
and the arithmetic remark at radius 4.
-/
module

public import InducedPaths.Axioms
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Sum
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
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

/-- A shortest walk is chordless: a chord would be a strictly shorter route. -/
lemma isChordless_of_length_eq_dist [DecidableEq V] {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) : p.IsChordless := by
  rw [Walk.isChordless_iff_forall_mem_edges]
  intro a b ha hb hadj
  have hi : p.support.idxOf a < p.support.length := List.idxOf_lt_length_iff.mpr ha
  have hj : p.support.idxOf b < p.support.length := List.idxOf_lt_length_iff.mpr hb
  have hai : p.getVert (p.support.idxOf a) = a := p.getVert_support_idxOf ha
  have hbj : p.getVert (p.support.idxOf b) = b := p.getVert_support_idxOf hb
  have hlenS : p.support.length = p.length + 1 := p.length_support
  set i := p.support.idxOf a
  set j := p.support.idxOf b
  have hiL : i ≤ p.length := by omega
  have hjL : j ≤ p.length := by omega
  have hij : i ≠ j := by
    intro h
    exact hadj.ne (hai.symm.trans (h ▸ hbj))
  have hconsec {x y : V} {k : ℕ} (hk : k < p.length)
      (hk1 : p.getVert k = x) (hk2 : p.getVert (k + 1) = y) : s(x, y) ∈ p.edges := by
    refine (Walk.mk_mem_edges_iff_exists p).2 ⟨k, hk, ?_⟩
    rw [hk1, hk2]
  by_cases h1 : j = i + 1
  · have hlt : i < p.length := by
      have hle : i + 1 ≤ p.length := by rw [← h1]; exact hjL
      omega
    exact hconsec hlt hai (by rw [← h1]; exact hbj)
  · by_cases h2 : i = j + 1
    · have hlt : j < p.length := by
        have hle : j + 1 ≤ p.length := by rw [← h2]; exact hiL
        omega
      have hmem : s(b, a) ∈ p.edges := hconsec hlt hbj (by rw [← h2]; exact hai)
      rwa [Sym2.eq_swap] at hmem
    · have hfar : i + 2 ≤ j ∨ j + 2 ≤ i := by omega
      rcases hfar with hfar | hfar
      · have htake := length_eq_dist_of_subwalk hp (Walk.isSubwalk_take p i)
        have htakeL : (p.take i).length = i := by
          rw [Walk.take_length]; exact Nat.min_eq_left hiL
        have hdisti : G.dist u a = i := by rw [← hai, ← htake, htakeL]
        have hdrop := length_eq_dist_of_subwalk hp (Walk.isSubwalk_drop p j)
        have hdistj : G.dist b v = p.length - j := by rw [← hbj, ← hdrop, Walk.drop_length]
        have hab : G.dist a b = 1 := dist_eq_one_iff_adj.mpr hadj
        have htri1 := hadj.reachable.dist_triangle_right u
        have htri2 : G.dist u v ≤ G.dist u b + G.dist b v := by
          simpa [hbj] using (p.drop j).reachable.dist_triangle_right u
        have hle : G.dist u v ≤ i + 1 + (p.length - j) := by
          calc
            G.dist u v ≤ G.dist u b + G.dist b v := htri2
            _ ≤ G.dist u a + G.dist a b + G.dist b v :=
              Nat.add_le_add_right htri1 _
            _ = i + 1 + (p.length - j) := by rw [hdisti, hab, hdistj]
        have hlt : i + 1 + (p.length - j) < p.length := by omega
        omega
      · have htake := length_eq_dist_of_subwalk hp (Walk.isSubwalk_take p j)
        have htakeL : (p.take j).length = j := by
          rw [Walk.take_length]; exact Nat.min_eq_left hjL
        have hdistj : G.dist u b = j := by rw [← hbj, ← htake, htakeL]
        have hdrop := length_eq_dist_of_subwalk hp (Walk.isSubwalk_drop p i)
        have hdisti : G.dist a v = p.length - i := by rw [← hai, ← hdrop, Walk.drop_length]
        have hab : G.dist b a = 1 := dist_eq_one_iff_adj.mpr hadj.symm
        have htri1 := hadj.symm.reachable.dist_triangle_right u
        have htri2 : G.dist u v ≤ G.dist u a + G.dist a v := by
          simpa [hai] using (p.drop i).reachable.dist_triangle_right u
        have hle : G.dist u v ≤ j + 1 + (p.length - i) := by
          calc
            G.dist u v ≤ G.dist u a + G.dist a v := htri2
            _ ≤ G.dist u b + G.dist b a + G.dist a v :=
              Nat.add_le_add_right htri1 _
            _ = j + 1 + (p.length - i) := by rw [hdistj, hab, hdisti]
        have hlt : j + 1 + (p.length - i) < p.length := by omega
        omega

/-- A geodesic is an induced path. -/
lemma pathGraph_isIndContained_of_length_eq_dist [DecidableEq V] {u v : V}
    (p : G.Walk u v) (hp : p.length = G.dist u v) :
    pathGraph (p.length + 1) ⊴ G := by
  have hpath := p.isPath_of_length_eq_dist hp
  have hind : p.toSubgraph.IsInduced :=
    Walk.isInduced_toSubgraph.mpr (isChordless_of_length_eq_dist p hp)
  exact hpath.pathGraphIsoToSubgraph.isIndContained.trans hind.isIndContained

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

lemma endpointSnd_injOn (hdeg : ∀ v, H.degree v ≤ 1) :
    Set.InjOn (fun e : Sym2 W => e.out.2) (H.edgeFinset : Set (Sym2 W)) := by
  intro e he e' he' hEq
  by_contra hne
  have hEq' : e.out.2 = e'.out.2 := hEq
  have h1 : H.Adj e.out.2 e.out.1 := (adj_out_of_mem H e he).symm
  have h2 : H.Adj e.out.2 e'.out.1 := hEq' ▸ (adj_out_of_mem H e' he').symm
  have hp : e.out.1 ≠ e'.out.1 := by
    intro h
    exact hne (sym2_eq_of_outs h hEq')
  exact (hdeg e.out.2).not_gt <| Nat.lt_of_succ_le <| pair_degree_ge_two H h1 h2 hp

/-- A matching covers two vertices per edge, so `2e ≤ n`. -/
lemma two_mul_edgeFinset_card_le (hdeg : ∀ v, H.degree v ≤ 1) :
    2 * H.edgeFinset.card ≤ Fintype.card W := by
  have hsub : H.edgeFinset.image (fun e => e.out.2) ⊆ keptVertices H := by
    intro x hx
    obtain ⟨e, he, heq⟩ := mem_image.mp hx
    have heq' : e.out.2 = x := heq
    rw [keptVertices, mem_sdiff]
    exact ⟨mem_univ _, heq' ▸ endpoint_snd_not_mem H hdeg he⟩
  have hcard := card_image_of_injOn (endpointSnd_injOn H hdeg)
  have hle : H.edgeFinset.card ≤ (keptVertices H).card := by
    rw [← hcard]
    exact card_le_card hsub
  rw [keptVertices_card H hdeg] at hle
  omega

/-- In maximum degree at most 1, reachability is equality or adjacency. -/
lemma reachable_eq_or_adj (hdeg : ∀ v, H.degree v ≤ 1) {u w : W} :
    H.Reachable u w ↔ u = w ∨ H.Adj u w := by
  constructor
  · intro h
    refine h.elim_path fun p => ?_
    rcases p with ⟨p, hp⟩
    by_cases hlong : 2 ≤ p.length
    · have hnodup := hp.support_nodup
      have hlen : p.support.length = p.length + 1 := p.length_support
      have h0 : 0 < p.support.length := by omega
      have h2 : 2 < p.support.length := by omega
      have hneS : p.support[0] ≠ p.support[2] := by
        intro heq
        have := (hnodup.getElem_inj_iff (hi := h0) (hj := h2)).mp heq
        omega
      have h01 : H.Adj (p.getVert 0) (p.getVert 1) := p.adj_getVert_succ (by omega)
      have h12 : H.Adj (p.getVert 1) (p.getVert 2) := p.adj_getVert_succ (by omega)
      have hne : p.getVert 0 ≠ p.getVert 2 := by
        rw [p.getVert_eq_support_getElem (by omega : (0 : ℕ) ≤ p.length),
          p.getVert_eq_support_getElem (by omega : (2 : ℕ) ≤ p.length)]
        exact hneS
      exact False.elim <| (hdeg (p.getVert 1)).not_gt <|
        Nat.lt_of_succ_le (pair_degree_ge_two H h01.symm h12 hne)
    · have hshort : p.length = 0 ∨ p.length = 1 := by omega
      rcases hshort with h0 | h1
      · left
        exact (Walk.length_eq_zero_iff.mp h0).eq
      · right
        have hadj := p.adj_getVert_succ (by omega : 0 < p.length)
        have hget : p.getVert 1 = w := by rw [← h1]; exact p.getVert_length
        rw [p.getVert_zero, hget] at hadj
        exact hadj
  · rintro (rfl | hadj)
    · exact ⟨Walk.nil⟩
    · exact hadj.reachable

/-- Vertices of one component. Membership is decidable because reachability is. -/
private def suppFin (c : H.ConnectedComponent) : Finset W :=
  Finset.univ.filter fun w => w ∈ c.supp

private lemma one_le_suppFin_card (c : H.ConnectedComponent) : 1 ≤ (suppFin H c).card := by
  obtain ⟨u, hu⟩ := c.nonempty_supp
  exact (Finset.one_le_card).2 ⟨u, mem_filter.mpr ⟨mem_univ _, hu⟩⟩

private lemma suppFin_card_le_two (hdeg : ∀ v, H.degree v ≤ 1) (c : H.ConnectedComponent) :
    (suppFin H c).card ≤ 2 := by
  obtain ⟨u, hu⟩ := c.nonempty_supp
  have hsub : suppFin H c ⊆ insert u (H.neighborFinset u) := by
    intro w hw
    have hw' : w ∈ c.supp := (mem_filter.mp hw).2
    rcases (reachable_eq_or_adj H hdeg).1 (c.reachable_of_mem_supp hu hw') with rfl | hadj
    · exact mem_insert_self u _
    · exact mem_insert_of_mem ((H.mem_neighborFinset u w).2 hadj)
  have hnot : u ∉ H.neighborFinset u := notMem_neighborFinset_self H u
  have hcard : #(insert u (H.neighborFinset u)) = #(H.neighborFinset u) + 1 :=
    card_insert_of_notMem hnot
  have hdeg1 : (H.neighborFinset u).card ≤ 1 := by
    rw [card_neighborFinset_eq_degree (G := H) (v := u)]
    exact hdeg u
  exact (card_le_card hsub).trans (by omega)

/-- A finite graph of maximum degree at most 1 has one more component than its non-edge count:
`κ + e = n`. Each component is a vertex or an edge. -/
theorem natCard_connectedComponent_add_edgeCount (hdeg : ∀ v, H.degree v ≤ 1) :
    Nat.card H.ConnectedComponent + H.edgeFinset.card = Fintype.card W := by
  have hsplit : ∀ c : H.ConnectedComponent,
      (suppFin H c).card = 1 ∨ (suppFin H c).card = 2 := by
    intro c
    have h1 := one_le_suppFin_card H c
    have h2 := suppFin_card_le_two H hdeg c
    omega
  let big : Finset H.ConnectedComponent :=
    Finset.univ.filter fun c => (suppFin H c).card = 2
  have hbi : (Finset.univ : Finset H.ConnectedComponent).biUnion (suppFin H) = Finset.univ := by
    ext w
    simp only [mem_biUnion, mem_univ, true_and]
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    exact ⟨H.connectedComponentMk w,
      mem_filter.mpr ⟨mem_univ _, ConnectedComponent.connectedComponentMk_mem⟩⟩
  have hdisjB : ((Finset.univ : Finset H.ConnectedComponent) : Set _).PairwiseDisjoint
      (suppFin H) := by
    intro c _ c' _ hne
    change Disjoint (suppFin H c) (suppFin H c')
    rw [Finset.disjoint_left]
    intro w hw hw'
    exact hne (ConnectedComponent.eq_of_common_vertex (mem_filter.mp hw).2 (mem_filter.mp hw').2)
  have hsum : ∑ c : H.ConnectedComponent, (suppFin H c).card = Fintype.card W := by
    rw [← Finset.card_biUnion hdisjB, hbi, card_univ]
  have hpred : ∀ c : H.ConnectedComponent,
      (suppFin H c).card = (if (suppFin H c).card = 2 then 1 else 0) + 1 := by
    intro c
    rcases hsplit c with h | h <;> simp [h]
  have hsumSplit :
      ∑ c : H.ConnectedComponent, (suppFin H c).card =
        (∑ c : H.ConnectedComponent, if (suppFin H c).card = 2 then 1 else 0) +
          Fintype.card H.ConnectedComponent := by
    rw [Finset.sum_congr rfl (fun c _ => hpred c), Finset.sum_add_distrib]
    simp [Finset.sum_const, Finset.card_univ, Nat.cast_id]
  have hbigCount :
      (∑ c : H.ConnectedComponent, if (suppFin H c).card = 2 then 1 else 0) = big.card := by
    simp [big, Nat.cast_id, Finset.sum_boole]
  have hbig : big.card = H.edgeFinset.card := by
    symm
    refine Finset.card_bij (s := H.edgeFinset) (t := big)
      (fun e he => H.connectedComponentMk e.out.1) ?mem ?inj ?surj
    case mem =>
      intro e he
      have hadj := adj_out_of_mem H e he
      have hne := sym2_out_ne (H.not_isDiag_of_mem_edgeFinset he)
      let c := H.connectedComponentMk e.out.1
      have h1 : e.out.1 ∈ suppFin H c :=
        mem_filter.mpr ⟨mem_univ _, ConnectedComponent.connectedComponentMk_mem⟩
      have h2 : e.out.2 ∈ suppFin H c := by
        refine mem_filter.mpr ⟨mem_univ _, ?_⟩
        rw [ConnectedComponent.mem_supp_iff]
        exact (ConnectedComponent.eq).2 hadj.symm.reachable
      have hpair : ({e.out.1, e.out.2} : Finset W) ⊆ suppFin H c := by
        intro x hx
        rw [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact h1
        · exact h2
      have hcard2 : ({e.out.1, e.out.2} : Finset W).card = 2 :=
        (card_pair_eq_two_iff).2 hne
      have hle : 2 ≤ (suppFin H c).card := by
        rw [← hcard2]
        exact card_le_card hpair
      have heq2 : (suppFin H c).card = 2 := by
        have := suppFin_card_le_two H hdeg c
        omega
      exact mem_filter.mpr ⟨mem_univ _, heq2⟩
    case inj =>
      intro e he e' he' hcomp
      let c := H.connectedComponentMk e.out.1
      have hto (f : Sym2 W) (hf : f ∈ H.edgeFinset)
          (hc : H.connectedComponentMk f.out.1 = c) :
          f.toFinset = suppFin H c := by
        have hadj := adj_out_of_mem H f hf
        have hne := sym2_out_ne (H.not_isDiag_of_mem_edgeFinset hf)
        have hfin : f.toFinset = {f.out.1, f.out.2} := by
          conv_lhs => rw [← Sym2.mk_fst_out_snd_out f]
          exact Sym2.toFinset_mk_eq
        have h1 : f.out.1 ∈ suppFin H c := by
          rw [show c = H.connectedComponentMk f.out.1 from hc.symm]
          exact mem_filter.mpr ⟨mem_univ _, ConnectedComponent.connectedComponentMk_mem⟩
        have h2 : f.out.2 ∈ suppFin H c := by
          refine mem_filter.mpr ⟨mem_univ _, ?_⟩
          rw [ConnectedComponent.mem_supp_iff, ← hc]
          exact (ConnectedComponent.eq).2 hadj.symm.reachable
        have hsub : f.toFinset ⊆ suppFin H c := by
          rw [hfin]
          intro x hx
          rw [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact h1
          · exact h2
        have hcardF : f.toFinset.card = 2 := by
          rw [hfin]
          exact (card_pair_eq_two_iff).2 hne
        have hcardS : (suppFin H c).card = 2 := by
          have hle : 2 ≤ (suppFin H c).card := by
            rw [← hcardF]
            exact card_le_card hsub
          have := suppFin_card_le_two H hdeg c
          omega
        exact Finset.eq_of_subset_of_card_le hsub (by rw [hcardF, hcardS])
      have heqF : e.toFinset = e'.toFinset :=
        (hto e he rfl).trans (hto e' he' hcomp.symm).symm
      apply Sym2.ext
      intro x
      rw [← Sym2.mem_toFinset, heqF, Sym2.mem_toFinset]
    case surj =>
      intro c hc
      have hc2 : (suppFin H c).card = 2 := (mem_filter.mp hc).2
      obtain ⟨a, b, hne, hab⟩ := card_eq_two.mp hc2
      have ha : a ∈ c.supp := by
        have : a ∈ suppFin H c := by
          rw [hab]
          exact mem_insert_self _ _
        exact (mem_filter.mp this).2
      have hb : b ∈ c.supp := by
        have : b ∈ suppFin H c := by
          rw [hab]
          exact mem_insert_of_mem (mem_singleton_self _)
        exact (mem_filter.mp this).2
      have hadj : H.Adj a b := by
        rcases (reachable_eq_or_adj H hdeg).1 (c.reachable_of_mem_supp ha hb) with rfl | h
        · exact absurd rfl hne
        · exact h
      have he : s(a, b) ∈ H.edgeFinset := by
        rw [mem_edgeFinset, mem_edgeSet]
        exact hadj
      refine ⟨s(a, b), he, ?_⟩
      have hmem : (s(a, b)).out.1 = a ∨ (s(a, b)).out.1 = b := by
        simpa [Sym2.mem_iff] using Sym2.out_fst_mem (s(a, b))
      rcases hmem with h | h
      · rw [h]
        exact (ConnectedComponent.mem_supp_iff c a).1 ha
      · rw [h]
        exact (ConnectedComponent.mem_supp_iff c b).1 hb
  have hnat : Nat.card H.ConnectedComponent = Fintype.card H.ConnectedComponent :=
    Nat.card_eq_fintype_card
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

/-- Lemma 2.1(2), the component-count sentence: `λ(v)` is the number of components of
`G[N(v)]`. -/
theorem lambda_eq_ncard_components (hG : StrongC4Free G) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (v : V) :
    Nat.card (G.induce (G.neighborSet v)).ConnectedComponent = lambda G v := by
  let H := G.induce (G.neighborSet v)
  have hdeg : ∀ w, H.degree w ≤ 1 := fun w => neighborhood_degree_le_one hG v w
  have hcomp := natCard_connectedComponent_add_edgeCount H hdeg
  have hind := indepNum_add_edgeCount_of_degree_le_one H hdeg
  have hlam : H.indepNum = lambda G v := rfl
  have : Nat.card H.ConnectedComponent = H.indepNum := by omega
  simpa [H, hlam] using this

/-- A vertex dominated by a universal `u` has `λ(v) = 1`: `G[N(v)]` is a star at `u`. -/
lemma lambda_eq_one_of_universal (hG : StrongC4Free G) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {u v : V} (hdom : ∀ w, w = u ∨ G.Adj u w) (hv : v ≠ u) :
    lambda G v = 1 := by
  let H := G.induce (G.neighborSet v)
  have hdeg : ∀ w, H.degree w ≤ 1 := fun w => neighborhood_degree_le_one hG v w
  have hsum := indepNum_add_edgeCount_of_degree_le_one H hdeg
  have huadj : G.Adj u v := (hdom v).resolve_left hv
  have hu : u ∈ G.neighborSet v := by rw [mem_neighborSet]; exact huadj.symm
  have hnbr : H.neighborFinset ⟨u, hu⟩ = Finset.univ.erase ⟨u, hu⟩ := by
    ext ⟨w, hw⟩
    simp only [mem_neighborFinset, mem_erase, mem_univ, and_true]
    constructor
    · exact fun hadj => hadj.ne.symm
    · intro hne
      apply (hdom w).resolve_left
      intro heq
      apply hne
      subst heq
      exact Subtype.ext rfl
  have hdegU : H.degree ⟨u, hu⟩ = Fintype.card (G.neighborSet v) - 1 := by
    rw [← card_neighborFinset_eq_degree, hnbr, card_erase_of_mem (mem_univ _), card_univ]
  have hone : 1 ≤ H.indepNum := by
    let x : G.neighborSet v := ⟨u, hu⟩
    have hI : H.IsIndepSet ({x} : Finset _) := by simp [isIndepSet_iff]
    simpa using IsIndepSet.card_le_indepNum hI
  have hle := H.degree_le_card_edgeFinset (v := ⟨u, hu⟩)
  have : H.indepNum = 1 := by omega
  simpa [H, lambda, alphaIn] using this

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

/-- An induced subgraph of a strong `C₄`-free graph is strong `C₄`-free. -/
lemma strongC4Free_induce {s : Set V} (h : StrongC4Free G) : StrongC4Free (G.induce s) := by
  intro hsub
  exact h (hsub.trans (Embedding.induce s).isContained)

lemma two_mul_trianglesAt_le_degree (hG : StrongC4Free G) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (v : V) : 2 * trianglesAt G v ≤ G.degree v := by
  have h2 := two_mul_edgeFinset_card_le (H := G.induce (G.neighborSet v))
    (fun w => neighborhood_degree_le_one hG v w)
  have htri : trianglesAt G v = (G.induce (G.neighborSet v)).edgeFinset.card := by
    simpa [edgeCount] using (trianglesAt_eq_neighborEdges (G := G) v)
  rw [← htri, G.card_neighborSet_eq_degree v] at h2
  exact h2

lemma three_mul_trianglesAt_le_two_degree (hG : StrongC4Free G) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (v : V) : 3 * trianglesAt G v ≤ 2 * G.degree v := by
  have h2 := two_mul_trianglesAt_le_degree hG v
  have ht : trianglesAt G v ≤ G.degree v := by
    have := lambda_add_trianglesAt hG v
    omega
  omega

lemma three_mul_triangleCount_le_two_edge (hG : StrongC4Free G) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] : 3 * triangleCount G ≤ 2 * edgeCount G := by
  have hle : ∀ v ∈ (univ : Finset V), trianglesAt G v ≤ G.degree v := by
    intro v _
    have := lambda_add_trianglesAt hG v
    omega
  have := Finset.sum_le_sum hle
  simpa [sum_trianglesAt, sum_degrees_eq_twice_card_edges, edgeCount, triangleCount,
    Nat.mul_comm] using this

lemma edgeCount_induce_compl_add [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    edgeCount (G.induce {v}ᶜ) + G.degree v = edgeCount G := by
  have h := card_edgeFinset_induce_compl_singleton (G := G) v
  have h' := card_edgeFinset_deleteIncidenceSet (G := G) v
  have hle : G.degree v ≤ #G.edgeFinset := by
    rw [← card_incidenceFinset_eq_degree]
    exact card_le_card (G.incidenceFinset_subset (v := v))
  rw [edgeCount, edgeCount, h, h']
  omega

lemma triangleCount_induce_compl_add [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    triangleCount (G.induce {v}ᶜ) + trianglesAt G v = triangleCount G := by
  let G' := G.induce {v}ᶜ
  let emb := Function.Embedding.subtype (fun x : V => x ∈ ({v}ᶜ : Set V))
  let embS : Finset {x // x ∈ ({v}ᶜ : Set V)} ↪ Finset V :=
    ⟨fun t => t.map emb, Finset.map_injective emb⟩
  have hmap : (G'.cliqueFinset 3).map embS =
      (G.cliqueFinset 3).filter fun s => v ∉ s := by
    ext s
    constructor
    · intro hs
      obtain ⟨t, ht, rfl⟩ := mem_map.mp hs
      have ht' := mem_cliqueFinset_iff.mp ht
      have hclique : G.IsClique ↑(t.map emb) := by
        have hset := (isClique_induce_iff (G := G) (s := {v}ᶜ)).1 ht'.isClique
        have hcoe : (emb : {x // x ∈ ({v}ᶜ : Set V)} → V) = Subtype.val := rfl
        rw [Finset.coe_map, hcoe]
        exact hset
      have hcard : #(t.map emb) = 3 := by rw [card_map]; exact ht'.card_eq
      refine mem_filter.mpr ⟨mem_cliqueFinset_iff.mpr ⟨hclique, hcard⟩, ?_⟩
      intro hv
      obtain ⟨x, _, hx⟩ := mem_map.mp hv
      have hx' : ↑x ≠ v := Set.mem_compl_singleton_iff.mp x.2
      rw [Function.Embedding.subtype_apply] at hx
      exact hx' hx
    · intro hs
      rw [mem_filter] at hs
      have hscl := mem_cliqueFinset_iff.mp hs.1
      have hv : ∀ x ∈ s, x ∈ ({v}ᶜ : Set V) := fun x hx => by
        rw [Set.mem_compl_singleton_iff]
        exact fun hxv => hs.2 (hxv ▸ hx)
      have hsm := Finset.subtype_map_of_mem hv
      have htmem : s.subtype (fun x => x ∈ ({v}ᶜ : Set V)) ∈ G'.cliqueFinset 3 := by
        rw [mem_cliqueFinset_iff]
        refine ⟨?_, ?_⟩
        · let t : Finset {x // x ∈ ({v}ᶜ : Set V)} :=
            s.subtype (fun x => x ∈ ({v}ᶜ : Set V))
          suffices G'.IsClique (t : Set _) by simpa [t] using this
          intro a ha b hb hne
          rw [induce_adj]
          have ha' : (a : V) ∈ (s : Set V) :=
            Finset.mem_coe.mpr (Finset.mem_subtype.mp (Finset.mem_coe.mp ha))
          have hb' : (b : V) ∈ (s : Set V) :=
            Finset.mem_coe.mpr (Finset.mem_subtype.mp (Finset.mem_coe.mp hb))
          exact hscl.isClique ha' hb' (fun heq => hne (Subtype.ext heq))
        · calc #(s.subtype (fun x => x ∈ ({v}ᶜ : Set V)))
              = #((s.subtype (fun x => x ∈ ({v}ᶜ : Set V))).map emb) := (card_map _).symm
            _ = #s := congrArg Finset.card hsm
            _ = 3 := hscl.card_eq
      exact mem_map.mpr ⟨s.subtype (fun x => x ∈ ({v}ᶜ : Set V)), htmem, hsm⟩
  have hunion : ((G.cliqueFinset 3).filter fun s => v ∈ s) ∪
      ((G.cliqueFinset 3).filter fun s => v ∉ s) = G.cliqueFinset 3 := by
    ext s
    constructor
    · intro hs
      rw [mem_union] at hs
      rcases hs with hs | hs
      · exact (mem_filter.mp hs).1
      · exact (mem_filter.mp hs).1
    · intro hs
      by_cases hv : v ∈ s
      · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hs, hv⟩))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hs, hv⟩))
  have hdisj : Disjoint ((G.cliqueFinset 3).filter fun s => v ∈ s)
      ((G.cliqueFinset 3).filter fun s => v ∉ s) := by
    rw [Finset.disjoint_left]
    intro s hs ht
    exact (mem_filter.mp ht).2 (mem_filter.mp hs).2
  have hsplit := card_union_of_disjoint hdisj
  rw [hunion] at hsplit
  have hat : trianglesAt G v = ((G.cliqueFinset 3).filter fun s => v ∈ s).card := by
    simp [trianglesAt]
  have hrest : triangleCount G' =
      ((G.cliqueFinset 3).filter fun s => v ∉ s).card := by
    rw [triangleCount, ← hmap]
    exact (Finset.card_map embS).symm
  have hG : triangleCount G = (G.cliqueFinset 3).card := rfl
  rw [hat, hrest, hG]
  omega

/-! ### Small consequences -/

/-- Lemma 2.8, the case `k = 6` of Camby–Schaudt. -/
theorem lemma_2_8 [Finite V] (hconn : G.Connected) (hp : IsPkFree G 6) :
    ∃ X : Set V, (G.induce X).Connected ∧
      (∀ v, ∃ x ∈ X, v = x ∨ G.Adj v x) ∧
      (IsPkFree (G.induce X) 4 ∨ Nonempty ((G.induce X) ≃g cycleGraph 6)) :=
  camby_schaudt G 6 (by omega) hconn hp

/-! ### Independence number under isomorphisms and disjoint unions -/

lemma indepNum_iso {W : Type*} {H : SimpleGraph W} (e : G ≃g H) : G.indepNum = H.indepNum := by
  have hset : {n | ∃ s : Finset V, G.IsNIndepSet n s} =
      {n | ∃ t : Finset W, H.IsNIndepSet n t} := by
    ext n
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨s.map e.toEquiv.toEmbedding, ?_, ?_⟩
      · rw [isIndepSet_iff, coe_map]
        intro x hx y hy hxy
        rw [Set.mem_image] at hx hy
        obtain ⟨x, hx, rfl⟩ := hx
        obtain ⟨y, hy, rfl⟩ := hy
        intro hadj
        exact hs.isIndepSet hx hy (fun h => hxy (congrArg e h)) ((e.map_rel_iff).1 hadj)
      · rw [card_map, hs.card_eq]
    · rintro ⟨t, ht⟩
      refine ⟨t.map e.symm.toEquiv.toEmbedding, ?_, ?_⟩
      · rw [isIndepSet_iff, coe_map]
        intro x hx y hy hxy
        rw [Set.mem_image] at hx hy
        obtain ⟨x, hx, rfl⟩ := hx
        obtain ⟨y, hy, rfl⟩ := hy
        intro hadj
        exact ht.isIndepSet hx hy (fun h => hxy (congrArg e.symm h))
          ((e.symm.map_rel_iff).1 hadj)
      · rw [card_map, ht.card_eq]
  simp [indepNum, hset]

lemma alphaIn_congr {s t : Set V} (h : s = t) : alphaIn G s = alphaIn G t := by
  subst h
  rfl

/-- Neighbours of `w` inside an induced subgraph are `N(w) ∩ s`. -/
lemma lambda_eq_alphaIn_neighbor_inter {s : Set V} {w : V} (hw : w ∈ s) :
    lambda (G.induce s) ⟨w, hw⟩ = alphaIn G (G.neighborSet w ∩ s) := by
  let e : (G.induce s).neighborSet ⟨w, hw⟩ ≃ {x : V // x ∈ G.neighborSet w ∩ s} :=
    { toFun := fun x => ⟨x.1.1, by
        refine ⟨?_, x.1.2⟩
        simpa [neighborSet_induce, mem_neighborSet] using x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.2⟩, by
        simpa [neighborSet_induce, mem_neighborSet] using x.2.1⟩
      left_inv := fun _ => Subtype.ext (Subtype.ext rfl)
      right_inv := fun _ => Subtype.ext rfl }
  let φ : ((G.induce s).induce ((G.induce s).neighborSet ⟨w, hw⟩)) ≃g
      G.induce (G.neighborSet w ∩ s) :=
    { toEquiv := e
      map_rel_iff' := by
        intro a b
        simp [e] }
  simpa [lambda, alphaIn] using indepNum_iso φ

lemma lambda_induce_eq {s : Set V} {w : V} (hw : w ∈ s) (hN : G.neighborSet w ⊆ s) :
    lambda (G.induce s) ⟨w, hw⟩ = lambda G w := by
  rw [lambda_eq_alphaIn_neighbor_inter hw, lambda]
  exact alphaIn_congr (Set.inter_eq_left.mpr hN)

lemma indepNum_sum {W : Type*} [Finite V] [Finite W] (G : SimpleGraph V) (H : SimpleGraph W) :
    (G ⊕g H).indepNum = G.indepNum + H.indepNum := by
  apply le_antisymm
  · obtain ⟨s, hs⟩ := exists_isNIndepSet_indepNum (G := G ⊕g H)
    have hL : G.IsIndepSet s.toLeft := by
      rw [isIndepSet_iff]
      intro a ha b hb hne hadj
      have ha' : Sum.inl a ∈ (s : Set (V ⊕ W)) := by simpa [mem_toLeft] using ha
      have hb' : Sum.inl b ∈ (s : Set (V ⊕ W)) := by simpa [mem_toLeft] using hb
      exact hs.isIndepSet ha' hb' (by simpa using hne) (by simpa [sum_adj] using hadj)
    have hR : H.IsIndepSet s.toRight := by
      rw [isIndepSet_iff]
      intro a ha b hb hne hadj
      have ha' : Sum.inr a ∈ (s : Set (V ⊕ W)) := by simpa [mem_toRight] using ha
      have hb' : Sum.inr b ∈ (s : Set (V ⊕ W)) := by simpa [mem_toRight] using hb
      exact hs.isIndepSet ha' hb' (by simpa using hne) (by simpa [sum_adj] using hadj)
    have hcard := card_toLeft_add_card_toRight (u := s)
    have hLs := hL.card_le_indepNum
    have hRs := hR.card_le_indepNum
    rw [← hs.card_eq, ← hcard]
    exact add_le_add hLs hRs
  · obtain ⟨s, hs⟩ := exists_isNIndepSet_indepNum (G := G)
    obtain ⟨t, ht⟩ := exists_isNIndepSet_indepNum (G := H)
    let u := s.disjSum t
    have hu : (G ⊕g H).IsIndepSet u := by
      rw [isIndepSet_iff]
      intro a ha b hb hne hadj
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          have ha' : a ∈ s := by simpa [u, inl_mem_disjSum] using ha
          have hb' : b ∈ s := by simpa [u, inl_mem_disjSum] using hb
          exact hs.isIndepSet ha' hb' (by simpa using hne) (by simpa [sum_adj] using hadj)
        | inr _ =>
          simp [sum_adj] at hadj
      | inr a =>
        cases b with
        | inl _ =>
          simp [sum_adj] at hadj
        | inr b =>
          have ha' : a ∈ t := by simpa [u, inr_mem_disjSum] using ha
          have hb' : b ∈ t := by simpa [u, inr_mem_disjSum] using hb
          exact ht.isIndepSet ha' hb' (by simpa using hne) (by simpa [sum_adj] using hadj)
    have hcard : u.card = G.indepNum + H.indepNum := by
      simp [u, card_disjSum, hs.card_eq, ht.card_eq]
    have hle : u.card ≤ (G ⊕g H).indepNum := hu.card_le_indepNum
    rwa [hcard] at hle

/-- No edges between `s` and `t` make `α` additive. -/
lemma alphaIn_union_no_cross {s t : Set V} (hdisj : Disjoint s t)
    (hno : ∀ ⦃a b : V⦄, a ∈ s → b ∈ t → ¬ G.Adj a b) [Finite s] [Finite t] :
    alphaIn G (s ∪ t) = alphaIn G s + alphaIn G t := by
  haveI : DecidablePred (· ∈ s) := fun _ => Classical.propDecidable _
  let e : {x // x ∈ s ∪ t} ≃ ({x // x ∈ s} ⊕ {x // x ∈ t}) := Equiv.Set.union hdisj
  have hadj : ∀ x y,
      (G.induce s ⊕g G.induce t).Adj (e x) (e y) ↔ (G.induce (s ∪ t)).Adj x y := by
    intro x y
    by_cases hx : (x : V) ∈ s <;> by_cases hy : (y : V) ∈ s
    · rw [Equiv.Set.union_apply_left hdisj hx, Equiv.Set.union_apply_left hdisj hy]
      simp [sum_adj]
    · have hyt : (y : V) ∈ t :=
        ((Set.mem_union (y : V) s t).mp y.2).resolve_left hy
      rw [Equiv.Set.union_apply_left hdisj hx, Equiv.Set.union_apply_right hdisj hyt, sum_adj]
      change False ↔ (G.induce (s ∪ t)).Adj x y
      rw [induce_adj]
      exact iff_of_false (fun h => h) (hno hx hyt)
    · have hxt : (x : V) ∈ t :=
        ((Set.mem_union (x : V) s t).mp x.2).resolve_left hx
      rw [Equiv.Set.union_apply_right hdisj hxt, Equiv.Set.union_apply_left hdisj hy, sum_adj]
      change False ↔ (G.induce (s ∪ t)).Adj x y
      rw [induce_adj]
      exact iff_of_false (fun h => h) (fun h => hno hy hxt h.symm)
    · have hxt : (x : V) ∈ t :=
        ((Set.mem_union (x : V) s t).mp x.2).resolve_left hx
      have hyt : (y : V) ∈ t :=
        ((Set.mem_union (y : V) s t).mp y.2).resolve_left hy
      rw [Equiv.Set.union_apply_right hdisj hxt, Equiv.Set.union_apply_right hdisj hyt]
      simp [sum_adj]
  let φ : G.induce (s ∪ t) ≃g G.induce s ⊕g G.induce t :=
    { toEquiv := e
      map_rel_iff' := by
        intro a b
        exact hadj a b }
  rw [alphaIn, alphaIn, alphaIn, indepNum_iso φ, indepNum_sum]

/-- Remark 4.6. The inequality is arithmetic once `r = 4`, `p ≥ 8` and `ℓ ≤ 4`. -/
theorem remark_4_6 [Fintype V] [DecidableEq V]
    (_hconn : G.Connected) (_hC : StrongC4Free G) (hr : radiusNat G = 4)
    (hp : 8 ≤ inducedPathOrder G) (hell : ell G ≤ 4) :
    (inducedPathOrder G : ℚ) ≥ (radiusNat G : ℚ) + ell G := by
  have hp' : (8 : ℚ) ≤ inducedPathOrder G := by exact_mod_cast hp
  have hr' : (radiusNat G : ℚ) = 4 := by exact_mod_cast hr
  linarith

end InducedPaths
