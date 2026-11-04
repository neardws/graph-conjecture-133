/-
Proposition 6.2 for `θₖ`: strong `C₄`-free, order `2k+2`, radius 3,
induced-path order 6, and `S = 6k = 3n - 6`.
-/
module

public import InducedPaths.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.BigOperators

open scoped SimpleGraph
open Finset SimpleGraph

set_option linter.style.haveILetI false

@[expose] public section

namespace InducedPaths

instance thetaGraph.decidableRel (k : ℕ) : DecidableRel (thetaGraph k).Adj := fun u v => by
  cases u <;> cases v
  · exact isFalse (by simp [thetaGraph, simpleOf])
  · exact isFalse (by simp [thetaGraph, simpleOf])
  · exact isTrue (by simp [thetaGraph, simpleOf])
  · exact isFalse (by simp [thetaGraph, simpleOf])
  · exact isFalse (by simp [thetaGraph, simpleOf])
  · exact isFalse (by simp [thetaGraph, simpleOf])
  · exact isFalse (by simp [thetaGraph, simpleOf])
  · exact isTrue (by simp [thetaGraph, simpleOf])
  · exact isTrue (by simp [thetaGraph, simpleOf])
  · exact isFalse (by simp [thetaGraph, simpleOf])
  · exact isFalse (by simp [thetaGraph, simpleOf])
  · rename_i i j
    by_cases h : i = j
    · exact isTrue (by simp [thetaGraph, simpleOf, h])
    · exact isFalse (by simpa [thetaGraph, simpleOf, eq_comm] using h)
  · exact isFalse (by simp [thetaGraph, simpleOf])
  · exact isTrue (by simp [thetaGraph, simpleOf])
  · rename_i i j
    by_cases h : i = j
    · exact isTrue (by simp [thetaGraph, simpleOf, h])
    · exact isFalse (by simpa [thetaGraph, simpleOf, eq_comm] using h)
  · exact isFalse (by simp [thetaGraph, simpleOf])

def thetaSumEquiv (k : ℕ) : ThetaV k ≃ Fin 2 ⊕ Fin k ⊕ Fin k where
  toFun := fun
    | .x => Sum.inl 0
    | .y => Sum.inl 1
    | .a i => Sum.inr (Sum.inl i)
    | .b i => Sum.inr (Sum.inr i)
  invFun := fun
    | Sum.inl i => Fin.cases .x (fun _ => .y) i
    | Sum.inr (Sum.inl i) => .a i
    | Sum.inr (Sum.inr i) => .b i
  left_inv := by
    intro v
    cases v <;> rfl
  right_inv := by
    intro z
    rcases z with i | i | i
    · fin_cases i <;> rfl
    · rfl
    · rfl

lemma theta_card (k : ℕ) : Fintype.card (ThetaV k) = 2 * k + 2 := by
  rw [Fintype.card_congr (thetaSumEquiv k)]
  simp [Fintype.card_sum, Fintype.card_fin]
  omega

lemma theta_adj_xa (k : ℕ) (i : Fin k) : (thetaGraph k).Adj .x (.a i) := by
  simp [thetaGraph, simpleOf]

lemma theta_adj_ab (k : ℕ) (i : Fin k) : (thetaGraph k).Adj (.a i) (.b i) := by
  simp [thetaGraph, simpleOf]

lemma theta_adj_by (k : ℕ) (i : Fin k) : (thetaGraph k).Adj (.b i) .y := by
  simp [thetaGraph, simpleOf]

lemma theta_degree_x (k : ℕ) : (thetaGraph k).degree .x = k := by
  rw [← card_neighborFinset_eq_degree]
  have hfin : (thetaGraph k).neighborFinset .x =
      (univ : Finset (Fin k)).map ⟨ThetaV.a, fun i j h => by injection h⟩ := by
    ext v
    simp only [mem_neighborFinset, mem_map, mem_univ, true_and]
    cases v with
    | a i => exact ⟨fun _ => ⟨i, rfl⟩, fun ⟨_, h⟩ => h ▸ theta_adj_xa k i⟩
    | x =>
      simp [thetaGraph, simpleOf]
    | y =>
      simp [thetaGraph, simpleOf]
    | b i =>
      simp [thetaGraph, simpleOf]
  rw [hfin, card_map, card_univ, Fintype.card_fin]

lemma theta_degree_y (k : ℕ) : (thetaGraph k).degree .y = k := by
  rw [← card_neighborFinset_eq_degree]
  have hfin : (thetaGraph k).neighborFinset .y =
      (univ : Finset (Fin k)).map ⟨ThetaV.b, fun i j h => by injection h⟩ := by
    ext v
    simp only [mem_neighborFinset, mem_map, mem_univ, true_and]
    cases v with
    | b i =>
      refine ⟨fun _ => ⟨i, rfl⟩, ?_⟩
      rintro ⟨_, h⟩
      cases h
      exact (theta_adj_by k i).symm
    | x => simp [thetaGraph, simpleOf]
    | y => simp [thetaGraph, simpleOf]
    | a i => simp [thetaGraph, simpleOf]
  rw [hfin, card_map, card_univ, Fintype.card_fin]

lemma theta_degree_a (k : ℕ) (i : Fin k) : (thetaGraph k).degree (.a i) = 2 := by
  rw [← card_neighborFinset_eq_degree]
  have hne : (ThetaV.x : ThetaV k) ≠ .b i := by intro h; cases h
  have hfin : (thetaGraph k).neighborFinset (.a i) = {.x, .b i} := by
    ext v
    simp only [mem_neighborFinset, mem_insert, mem_singleton]
    cases v with
    | x => simp [thetaGraph, simpleOf]
    | y => simp [thetaGraph, simpleOf]
    | a j => simp [thetaGraph, simpleOf]
    | b j =>
      simp [thetaGraph, simpleOf, ThetaV.b.injEq, eq_comm]
  rw [hfin, card_pair_eq_two_iff]
  exact hne

lemma theta_degree_b (k : ℕ) (i : Fin k) : (thetaGraph k).degree (.b i) = 2 := by
  rw [← card_neighborFinset_eq_degree]
  have hne : (ThetaV.a i : ThetaV k) ≠ .y := by intro h; cases h
  have hfin : (thetaGraph k).neighborFinset (.b i) = {.a i, .y} := by
    ext v
    simp only [mem_neighborFinset, mem_insert, mem_singleton]
    cases v with
    | x => simp [thetaGraph, simpleOf]
    | y => simp [thetaGraph, simpleOf]
    | a j => simp [thetaGraph, simpleOf, ThetaV.a.injEq]
    | b j => simp [thetaGraph, simpleOf]
  rw [hfin, card_pair_eq_two_iff]
  exact hne

lemma theta_degree_sum (k : ℕ) : ∑ v, (thetaGraph k).degree v = 6 * k := by
  have hs : ∑ v, (thetaGraph k).degree v =
      ∑ i : Fin 2 ⊕ Fin k ⊕ Fin k, (thetaGraph k).degree ((thetaSumEquiv k).symm i) :=
    (Equiv.sum_comp (thetaSumEquiv k).symm fun v => (thetaGraph k).degree v).symm
  have hx : (thetaSumEquiv k).symm (Sum.inl 0) = .x := by
    simp [thetaSumEquiv]
  have hy : (thetaSumEquiv k).symm (Sum.inl 1) = .y := by
    show Fin.cases ThetaV.x (fun _ => ThetaV.y) (1 : Fin 2) = ThetaV.y
    rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by decide, Fin.cases_succ]
  have ha : ∀ i, (thetaSumEquiv k).symm (Sum.inr (Sum.inl i)) = .a i := by
    intro i
    simp [thetaSumEquiv]
  have hb : ∀ i, (thetaSumEquiv k).symm (Sum.inr (Sum.inr i)) = .b i := by
    intro i
    simp [thetaSumEquiv]
  have hA : ∑ i : Fin k, (thetaGraph k).degree ((thetaSumEquiv k).symm (Sum.inr (Sum.inl i))) =
      ∑ i : Fin k, (thetaGraph k).degree (.a i) := by
    refine sum_congr rfl ?_
    intro i _
    rw [ha i]
  have hB : ∑ i : Fin k, (thetaGraph k).degree ((thetaSumEquiv k).symm (Sum.inr (Sum.inr i))) =
      ∑ i : Fin k, (thetaGraph k).degree (.b i) := by
    refine sum_congr rfl ?_
    intro i _
    rw [hb i]
  rw [hs, Fintype.sum_sum_type, Fintype.sum_sum_type, Fin.sum_univ_two, hx, hy, hA, hB]
  simp only [theta_degree_x, theta_degree_y, theta_degree_a, theta_degree_b, sum_const,
    card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  omega

lemma theta_edgeCount (k : ℕ) : edgeCount (thetaGraph k) = 3 * k := by
  have hdeg := theta_degree_sum k
  rw [sum_degrees_eq_twice_card_edges] at hdeg
  rw [edgeCount]
  omega

/-- Distinct vertices of `θₖ` have at most one common neighbour, so there is no `C₄`. -/
lemma theta_commonNeighbors_subsingleton {k : ℕ} {u v : ThetaV k} (hne : u ≠ v) :
    ((thetaGraph k).commonNeighbors u v).Subsingleton := by
  intro w hw z hz
  cases u <;> cases v <;> cases w <;> cases z <;>
    simp [mem_commonNeighbors, thetaGraph, simpleOf] at hw hz hne ⊢ <;> grind

lemma theta_strongC4Free (k : ℕ) : StrongC4Free (thetaGraph k) := by
  intro ⟨f⟩
  have h02 : f 0 ≠ f 2 := by
    intro h
    exact absurd (f.injective (by simpa using h)) (by decide : (0 : Fin 4) ≠ 2)
  have h13 : f 1 ≠ f 3 := by
    intro h
    exact absurd (f.injective (by simpa using h)) (by decide : (1 : Fin 4) ≠ 3)
  have h1 : f 1 ∈ (thetaGraph k).commonNeighbors (f 0) (f 2) := by
    refine ⟨?_, ?_⟩
    · exact f.toHom.map_rel (by decide : (cycleGraph 4).Adj 0 1)
    · exact f.toHom.map_rel (by decide : (cycleGraph 4).Adj 2 1)
  have h3 : f 3 ∈ (thetaGraph k).commonNeighbors (f 0) (f 2) := by
    refine ⟨?_, ?_⟩
    · exact f.toHom.map_rel (by decide : (cycleGraph 4).Adj 0 3)
    · exact f.toHom.map_rel (by decide : (cycleGraph 4).Adj 2 3)
  exact h13 ((theta_commonNeighbors_subsingleton h02) h1 h3)

lemma theta_cn_xy (k : ℕ) : (thetaGraph k).commonNeighbors .x .y = ∅ := by
  ext w
  simp [mem_commonNeighbors, thetaGraph, simpleOf]
  cases w <;> simp

lemma theta_cn_ab {k : ℕ} {i j : Fin k} :
    (thetaGraph k).commonNeighbors (.a i) (.b j) = ∅ := by
  ext w
  simp [mem_commonNeighbors, thetaGraph, simpleOf]
  cases w <;> simp

lemma theta_not_xy (k : ℕ) : ¬ (thetaGraph k).Adj .x .y := by
  simp [thetaGraph, simpleOf]

lemma theta_not_ab {k : ℕ} {i j : Fin k} (hij : i ≠ j) : ¬ (thetaGraph k).Adj (.a i) (.b j) := by
  simp [thetaGraph, simpleOf, hij]

lemma theta_triangleCount (k : ℕ) : triangleCount (thetaGraph k) = 0 := by
  rw [triangleCount, card_eq_zero]
  ext s
  simp only [mem_cliqueFinset_iff, notMem_empty, iff_false]
  intro hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hs.card_eq
  let color : ThetaV k → Fin 2
    | .x => 0
    | .y => 1
    | .a _ => 1
    | .b _ => 0
  have hdiff {p q : ThetaV k} (hpq : (thetaGraph k).Adj p q) : color p ≠ color q := by
    cases p <;> cases q <;> simp [thetaGraph, simpleOf, color] at hpq ⊢
  have hadjab : (thetaGraph k).Adj a b :=
    hs.isClique (by simp) (by simp) hab
  have hadjac : (thetaGraph k).Adj a c :=
    hs.isClique (by simp) (by simp) hac
  have hadjbc : (thetaGraph k).Adj b c :=
    hs.isClique (by simp) (by simp) hbc
  have h1 := hdiff hadjab
  have h2 := hdiff hadjac
  have h3 := hdiff hadjbc
  generalize hca : color a = ca
  generalize hcb : color b = cb
  generalize hcc : color c = cc
  fin_cases ca <;> fin_cases cb <;> fin_cases cc <;> simp [hca, hcb, hcc] at h1 h2 h3

lemma theta_S (k : ℕ) : neighbourhoodIndependenceSum (thetaGraph k) = 6 * k := by
  have hC := theta_strongC4Free k
  have hS := strongC4Free_S_identity (G := thetaGraph k) hC
  rw [hS, theta_edgeCount k, theta_triangleCount k]
  omega

private lemma edist_walk_le {k : ℕ} {u v : ThetaV k} (p : (thetaGraph k).Walk u v)
    (hp : p.length ≤ 3) : (thetaGraph k).edist u v ≤ 3 :=
  (Walk.edist_le p).trans (by exact_mod_cast hp)

private lemma theta_edist_xy_eq (k : ℕ) (hk : 0 < k) : (thetaGraph k).edist .x .y = 3 := by
  let i : Fin k := ⟨0, hk⟩
  have hle : (thetaGraph k).edist .x .y ≤ 3 := by
    exact edist_walk_le ((Walk.cons (theta_adj_xa k i)
        (Walk.cons (theta_adj_ab k i) (theta_adj_by k i).toWalk))) (by simp only [Walk.length_cons, Walk.length_nil]; decide)
  have hxy : (.x : ThetaV k) ≠ .y := by intro h; cases h
  have hgt : 2 < (thetaGraph k).edist .x .y :=
    (two_lt_edist_iff).mpr ⟨hxy, theta_not_xy k, theta_cn_xy k⟩
  exact le_antisymm hle (Order.add_one_le_of_lt hgt)

private lemma theta_edist_ab_eq {k : ℕ} {i j : Fin k} (hij : i ≠ j) :
    (thetaGraph k).edist (.a i) (.b j) = 3 := by
  have hle : (thetaGraph k).edist (.a i) (.b j) ≤ 3 := by
    exact edist_walk_le ((Walk.cons (theta_adj_xa k i).symm
        (Walk.cons (theta_adj_xa k j) (theta_adj_ab k j).toWalk))) (by simp only [Walk.length_cons, Walk.length_nil]; decide)
  have hne : (.a i : ThetaV k) ≠ .b j := by intro h; cases h
  have hgt : 2 < (thetaGraph k).edist (.a i) (.b j) :=
    (two_lt_edist_iff).mpr ⟨hne, theta_not_ab hij, theta_cn_ab⟩
  exact le_antisymm hle (Order.add_one_le_of_lt hgt)

private def thetaOther {k : ℕ} (i : Fin k) (hk : 2 ≤ k) : Fin k :=
  if h : i.val = 0 then ⟨1, by omega⟩ else ⟨0, by omega⟩

private lemma thetaOther_ne {k : ℕ} (i : Fin k) (hk : 2 ≤ k) : thetaOther i hk ≠ i := by
  intro h
  by_cases h0 : i.val = 0
  · have : (thetaOther i hk).val = 1 := by simp [thetaOther, h0]
    have : i.val = 1 := by simpa [h] using this
    omega
  · have : (thetaOther i hk).val = 0 := by simp [thetaOther, h0]
    have : i.val = 0 := by simpa [h] using this
    exact h0 this

lemma theta_edist_le {k : ℕ} (hk : 0 < k) (u v : ThetaV k) : (thetaGraph k).edist u v ≤ 3 := by
  let i0 : Fin k := ⟨0, hk⟩
  cases u with
  | x =>
    cases v with
    | x => simp
    | y => exact (theta_edist_xy_eq k hk).le
    | a i =>
      exact edist_walk_le ((theta_adj_xa k i).toWalk) (by simp only [Walk.length_cons, Walk.length_nil]; decide)
    | b i =>
      exact edist_walk_le ((Walk.cons (theta_adj_xa k i) (theta_adj_ab k i).toWalk)) (by simp only [Walk.length_cons, Walk.length_nil]; decide)
  | y =>
    cases v with
    | x => simpa [edist_comm] using (theta_edist_xy_eq k hk).le
    | y => simp
    | a i =>
      exact edist_walk_le ((Walk.cons (theta_adj_by k i).symm (theta_adj_ab k i).symm.toWalk)) (by simp only [Walk.length_cons, Walk.length_nil]; decide)
    | b i =>
      exact edist_walk_le ((theta_adj_by k i).symm.toWalk) (by simp only [Walk.length_cons, Walk.length_nil]; decide)
  | a i =>
    cases v with
    | x =>
      exact edist_walk_le ((theta_adj_xa k i).symm.toWalk) (by simp only [Walk.length_cons, Walk.length_nil]; decide)
    | y =>
      exact edist_walk_le ((Walk.cons (theta_adj_ab k i) (theta_adj_by k i).toWalk)) (by simp only [Walk.length_cons, Walk.length_nil]; decide)
    | a j =>
      by_cases hij : i = j
      · subst hij
        simp
      · exact edist_walk_le ((Walk.cons (theta_adj_xa k i).symm (theta_adj_xa k j).toWalk)) (by simp only [Walk.length_cons, Walk.length_nil]; decide)
    | b j =>
      by_cases hij : i = j
      · subst hij
        exact edist_walk_le ((theta_adj_ab k i).toWalk) (by simp only [Walk.length_cons, Walk.length_nil]; decide)
      · exact (theta_edist_ab_eq hij).le
  | b i =>
    cases v with
    | x =>
      exact edist_walk_le ((Walk.cons (theta_adj_ab k i).symm (theta_adj_xa k i).symm.toWalk)) (by simp only [Walk.length_cons, Walk.length_nil]; decide)
    | y =>
      exact edist_walk_le ((theta_adj_by k i).toWalk) (by simp only [Walk.length_cons, Walk.length_nil]; decide)
    | a j =>
      by_cases hij : i = j
      · subst hij
        exact edist_walk_le ((theta_adj_ab k i).symm.toWalk) (by simp only [Walk.length_cons, Walk.length_nil]; decide)
      · simpa [edist_comm] using (theta_edist_ab_eq (Ne.symm hij)).le
    | b j =>
      by_cases hij : i = j
      · subst hij
        simp
      · exact edist_walk_le ((Walk.cons (theta_adj_by k i) (theta_adj_by k j).symm.toWalk)) (by simp only [Walk.length_cons, Walk.length_nil]; decide)

lemma theta_eccent {k : ℕ} (hk : 3 ≤ k) (u : ThetaV k) : (thetaGraph k).eccent u = 3 := by
  apply le_antisymm
  · rw [eccent_le_iff]
    intro v
    exact theta_edist_le (by omega) u v
  · have hfar : ∃ v, (thetaGraph k).edist u v = 3 := by
      cases u with
      | x => exact ⟨.y, theta_edist_xy_eq k (by omega)⟩
      | y => exact ⟨.x, by simpa [edist_comm] using theta_edist_xy_eq k (by omega)⟩
      | a i =>
        exact ⟨.b (thetaOther i (by omega)),
          theta_edist_ab_eq (Ne.symm (thetaOther_ne i (by omega)))⟩
      | b i =>
        exact ⟨.a (thetaOther i (by omega)), by
          rw [edist_comm]
          exact theta_edist_ab_eq (thetaOther_ne i (by omega))⟩
    obtain ⟨v, hv⟩ := hfar
    calc
      (3 : ℕ∞) = (thetaGraph k).edist u v := hv.symm
      _ ≤ (thetaGraph k).eccent u := edist_le_eccent

lemma theta_radius (k : ℕ) (hk : 3 ≤ k) : radiusNat (thetaGraph k) = 3 := by
  have he : ∀ u, (thetaGraph k).eccent u = 3 := theta_eccent hk
  have hr : (thetaGraph k).radius = 3 := by
    apply le_antisymm
    · simpa [he] using (radius_le_eccent (G := thetaGraph k) (u := .x))
    · rw [radius]
      exact le_iInf fun u => by simp [he]
  simp [radiusNat, hr]

def thetaPath6 {k : ℕ} (hk : 3 ≤ k) (i : Fin 6) : ThetaV k :=
  if i.val = 0 then .a ⟨0, by omega⟩
  else if i.val = 1 then .x
  else if i.val = 2 then .a ⟨1, by omega⟩
  else if i.val = 3 then .b ⟨1, by omega⟩
  else if i.val = 4 then .y
  else .b ⟨2, by omega⟩

private def thetaPathCode {k : ℕ} : ThetaV k → ℕ
  | .x => 0
  | .y => 1
  | .a n => 2 + n.val
  | .b n => 100 + n.val

def theta_path6_embedding {k : ℕ} (hk : 3 ≤ k) : pathGraph 6 ↪g thetaGraph k where
  toFun := thetaPath6 hk
  inj' := by
    intro i j h
    have hc : thetaPathCode (thetaPath6 hk i) = thetaPathCode (thetaPath6 hk j) := by rw [h]
    fin_cases i <;> fin_cases j <;> simp [thetaPath6, thetaPathCode] at hc ⊢
  map_rel_iff' := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [thetaPath6, pathGraph_adj, thetaGraph, simpleOf]

def pathNbr (n : ℕ) (i : Fin n) : Finset (Fin n) :=
  univ.filter fun j => (pathGraph n).Adj i j

lemma pathNbr_card_le_two (n : ℕ) (i : Fin n) : (pathNbr n i).card ≤ 2 := by
  let pred : Finset (Fin n) :=
    if h : 0 < i.val then {⟨i.val - 1, by omega⟩} else ∅
  let succ : Finset (Fin n) :=
    if h : i.val + 1 < n then {⟨i.val + 1, h⟩} else ∅
  have hsub : pathNbr n i ⊆ pred ∪ succ := by
    intro j hj
    simp only [pathNbr, mem_filter, mem_univ, true_and, pathGraph_adj] at hj
    rcases hj with hj | hj
    · have hlt : i.val + 1 < n := by have := j.isLt; omega
      have heq : j = ⟨i.val + 1, hlt⟩ := Fin.ext hj.symm
      have : j ∈ succ := by simp [succ, hlt, heq]
      exact mem_union_right _ this
    · have hpos : 0 < i.val := by omega
      have hval : j.val = i.val - 1 := by omega
      have heq : j = ⟨i.val - 1, by omega⟩ := Fin.ext hval
      have : j ∈ pred := by simp [pred, hpos, heq]
      exact mem_union_left _ this
  have hpred : pred.card ≤ 1 := by
    simp only [pred]
    split_ifs <;> simp
  have hsucc : succ.card ≤ 1 := by
    simp only [succ]
    split_ifs <;> simp
  exact (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add hpred hsucc))

lemma pathNbr_internal (i : Fin 7) (h0 : i.val ≠ 0) (h6 : i.val ≠ 6) : 2 ≤ (pathNbr 7 i).card := by
  have hpred : 0 < i.val := by omega
  have hsucc : i.val + 1 < 7 := by omega
  let p : Fin 7 := ⟨i.val - 1, by omega⟩
  let s : Fin 7 := ⟨i.val + 1, hsucc⟩
  have hp : p ∈ pathNbr 7 i := by
    simp [pathNbr, pathGraph_adj, p]
    omega
  have hs : s ∈ pathNbr 7 i := by
    simp [pathNbr, pathGraph_adj, s]
  have hne : p ≠ s := by
    intro h
    have := congrArg Fin.val h
    simp [p, s] at this
  have hsub : ({p, s} : Finset (Fin 7)) ⊆ pathNbr 7 i := by
    intro j hj
    simp at hj
    rcases hj with rfl | rfl
    · exact hp
    · exact hs
  simpa [card_pair_eq_two_iff.mpr hne] using card_le_card hsub

lemma pathNbr_le_one_endpoint (i : Fin 7) (h : (pathNbr 7 i).card ≤ 1) : i.val = 0 ∨ i.val = 6 := by
  by_contra hnot
  push Not at hnot
  exact (Nat.not_le.mpr (lt_of_le_of_lt h (by omega : (1 : ℕ) < 2))) (pathNbr_internal i hnot.1 hnot.2)

lemma theta_no_p7 {k : ℕ} : IsPkFree (thetaGraph k) 7 := by
  intro ⟨f⟩
  haveI : DecidablePred (fun i : Fin 7 => ∃ j : Fin k, f i = ThetaV.a j) :=
    fun _ => Classical.propDecidable _
  haveI : DecidablePred (fun i : Fin 7 => ∃ j : Fin k, f i = ThetaV.b j) :=
    fun _ => Classical.propDecidable _
  let X : Finset (Fin 7) := univ.filter fun i => f i = .x
  let Y : Finset (Fin 7) := univ.filter fun i => f i = .y
  let A : Finset (Fin 7) := univ.filter fun i => ∃ j, f i = .a j
  let B : Finset (Fin 7) := univ.filter fun i => ∃ j, f i = .b j
  have hone : ∀ i : Fin 7,
      (if i ∈ X then 1 else 0) + (if i ∈ Y then 1 else 0) +
        (if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0) = 1 := by
    intro i
    cases hfi : f i with
    | x => simp [X, Y, A, B, hfi]
    | y => simp [X, Y, A, B, hfi]
    | a j => simp [X, Y, A, B, hfi]
    | b j => simp [X, Y, A, B, hfi]
  have hmem (S : Finset (Fin 7)) :
      ∑ i : Fin 7, (if i ∈ S then (1 : ℕ) else 0) = S.card := by
    rw [sum_boole]
    have hfilter : univ.filter (fun i : Fin 7 => i ∈ S) = S := by
      ext i
      simp
    rw [hfilter, Nat.cast_id]
  have hcards : X.card + Y.card + A.card + B.card = 7 := by
    have hsum : ∑ i : Fin 7,
        ((if i ∈ X then 1 else 0) + (if i ∈ Y then 1 else 0) +
          (if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0)) = 7 := by
      simp only [hone, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      norm_num
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, hmem, hmem, hmem, hmem] at hsum
    exact hsum
  have hXle : X.card ≤ 1 := by
    rw [card_le_one]
    intro i hi j hj
    simp [X] at hi hj
    exact f.injective (hi.trans hj.symm)
  have hYle : Y.card ≤ 1 := by
    rw [card_le_one]
    intro i hi j hj
    simp [Y] at hi hj
    exact f.injective (hi.trans hj.symm)
  have hA : ∀ {ix}, f ix = .x → A.card ≤ 2 := by
    intro ix hix
    have hsub : A ⊆ pathNbr 7 ix := by
      intro i hi
      have hi' : ∃ j, f i = .a j := by simpa [A] using hi
      obtain ⟨j, hj⟩ := hi'
      have hadj : (thetaGraph k).Adj (f ix) (f i) := by
        simpa [hix, hj] using theta_adj_xa k j
      simpa [pathNbr] using (f.map_rel_iff.mp hadj)
    exact (card_le_card hsub).trans (pathNbr_card_le_two 7 ix)
  have hB : ∀ {iy}, f iy = .y → B.card ≤ 2 := by
    intro iy hiy
    have hsub : B ⊆ pathNbr 7 iy := by
      intro i hi
      have hi' : ∃ j, f i = .b j := by simpa [B] using hi
      obtain ⟨j, hj⟩ := hi'
      have hadj : (thetaGraph k).Adj (f iy) (f i) := by
        simpa [hiy, hj] using (theta_adj_by k j).symm
      simpa [pathNbr] using (f.map_rel_iff.mp hadj)
    exact (card_le_card hsub).trans (pathNbr_card_le_two 7 iy)
  have hdegA (hX : X = ∅) {i : Fin 7} (hi : i ∈ A) : (pathNbr 7 i).card ≤ 1 := by
    have hi' : ∃ j, f i = .a j := by simpa [A] using hi
    obtain ⟨j, hj⟩ := hi'
    have hsub : pathNbr 7 i ⊆ univ.filter fun t => f t = .b j := by
      intro t ht
      have hadj : (thetaGraph k).Adj (f i) (f t) := f.map_rel_iff.mpr (by simpa [pathNbr] using ht)
      rw [hj] at hadj
      cases hft : f t with
      | x =>
        have : t ∈ X := by simp [X, hft]
        simp [hX] at this
      | y =>
        rw [hft] at hadj
        simp [thetaGraph, simpleOf] at hadj
      | a m =>
        rw [hft] at hadj
        simp [thetaGraph, simpleOf] at hadj
      | b m =>
        rw [hft] at hadj
        simp [thetaGraph, simpleOf] at hadj
        simp [mem_filter, hft, hadj]
    have huniq : (univ.filter fun t : Fin 7 => f t = .b j).card ≤ 1 := by
      rw [card_le_one]
      intro t1 ht1 t2 ht2
      simp at ht1 ht2
      exact f.injective (ht1.trans ht2.symm)
    exact (card_le_card hsub).trans huniq
  have hdegB (hY : Y = ∅) {i : Fin 7} (hi : i ∈ B) : (pathNbr 7 i).card ≤ 1 := by
    have hi' : ∃ j, f i = .b j := by simpa [B] using hi
    obtain ⟨j, hj⟩ := hi'
    have hsub : pathNbr 7 i ⊆ univ.filter fun t => f t = .a j := by
      intro t ht
      have hadj : (thetaGraph k).Adj (f i) (f t) := f.map_rel_iff.mpr (by simpa [pathNbr] using ht)
      rw [hj] at hadj
      cases hft : f t with
      | y =>
        have : t ∈ Y := by simp [Y, hft]
        simp [hY] at this
      | x =>
        rw [hft] at hadj
        simp [thetaGraph, simpleOf] at hadj
      | b m =>
        rw [hft] at hadj
        simp [thetaGraph, simpleOf] at hadj
      | a m =>
        rw [hft] at hadj
        simp [thetaGraph, simpleOf] at hadj
        simp [mem_filter, hft, hadj]
    have huniq : (univ.filter fun t : Fin 7 => f t = .a j).card ≤ 1 := by
      rw [card_le_one]
      intro t1 ht1 t2 ht2
      simp at ht1 ht2
      exact f.injective (ht1.trans ht2.symm)
    exact (card_le_card hsub).trans huniq
  have hBend (hY : Y = ∅) : B.card ≤ 2 := by
    let ends : Finset (Fin 7) := {⟨0, by decide⟩, ⟨6, by decide⟩}
    have hsub : B ⊆ ends := by
      intro i hi
      have hval := pathNbr_le_one_endpoint i (hdegB hY hi)
      rcases hval with h | h
      · have : i = ⟨0, by decide⟩ := Fin.ext h
        simp [ends, this]
      · have : i = ⟨6, by decide⟩ := Fin.ext h
        simp [ends, this]
    have hends : ends.card = 2 := by
      simp [ends]
    exact (card_le_card hsub).trans (by simp [hends])
  have hAend (hX : X = ∅) : A.card ≤ 2 := by
    let ends : Finset (Fin 7) := {⟨0, by decide⟩, ⟨6, by decide⟩}
    have hsub : A ⊆ ends := by
      intro i hi
      have hval := pathNbr_le_one_endpoint i (hdegA hX hi)
      rcases hval with h | h
      · have : i = ⟨0, by decide⟩ := Fin.ext h
        simp [ends, this]
      · have : i = ⟨6, by decide⟩ := Fin.ext h
        simp [ends, this]
    have hends : ends.card = 2 := by
      simp [ends]
    exact (card_le_card hsub).trans (by simp [hends])
  by_cases hXn : X.Nonempty
  · by_cases hYn : Y.Nonempty
    · obtain ⟨ix, hix⟩ := hXn
      obtain ⟨iy, hiy⟩ := hYn
      have hix' : f ix = .x := by simpa [X] using hix
      have hiy' : f iy = .y := by simpa [Y] using hiy
      have hAle := hA hix'
      have hBle := hB hiy'
      omega
    · obtain ⟨ix, hix⟩ := hXn
      have hix' : f ix = .x := by simpa [X] using hix
      have hY0 : Y.card = 0 := by
        simp [Finset.not_nonempty_iff_eq_empty.mp hYn]
      have hAle := hA hix'
      have hBle := hBend (Finset.not_nonempty_iff_eq_empty.mp hYn)
      omega
  · by_cases hYn : Y.Nonempty
    · obtain ⟨iy, hiy⟩ := hYn
      have hiy' : f iy = .y := by simpa [Y] using hiy
      have hX0 : X.card = 0 := by
        simp [Finset.not_nonempty_iff_eq_empty.mp hXn]
      have hAle := hAend (Finset.not_nonempty_iff_eq_empty.mp hXn)
      have hBle := hB hiy'
      omega
    · have hX0 : X = ∅ := Finset.not_nonempty_iff_eq_empty.mp hXn
      have hY0 : Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hYn
      have h1 : (pathNbr 7 ⟨1, by decide⟩).card ≤ 1 := by
        let i1 : Fin 7 := ⟨1, by decide⟩
        cases hfi : f i1 with
        | x =>
          have : i1 ∈ X := by simp [X, hfi]
          simp [hX0] at this
        | y =>
          have : i1 ∈ Y := by simp [Y, hfi]
          simp [hY0] at this
        | a j =>
          exact hdegA hX0 (by
            simp only [A, mem_filter, mem_univ, true_and]
            exact ⟨j, hfi⟩)
        | b j =>
          exact hdegB hY0 (by
            simp only [B, mem_filter, mem_univ, true_and]
            exact ⟨j, hfi⟩)
      have h2 : 2 ≤ (pathNbr 7 ⟨1, by decide⟩).card :=
        pathNbr_internal ⟨1, by decide⟩ (by decide) (by decide)
      omega

lemma theta_inducedPathOrder {k : ℕ} (hk : 3 ≤ k) : inducedPathOrder (thetaGraph k) = 6 := by
  have hge : 6 ≤ inducedPathOrder (thetaGraph k) :=
    le_csSup (inducedPathOrder_bddAbove (thetaGraph k)) ⟨theta_path6_embedding hk⟩
  have hlt : inducedPathOrder (thetaGraph k) < 7 :=
    (isPkFree_iff_inducedPathOrder_lt (thetaGraph k) 7).mp theta_no_p7
  omega

/-- Proposition 6.2. -/
theorem theta_proposition (k : ℕ) (hk : 3 ≤ k) :
    StrongC4Free (thetaGraph k) ∧
      Fintype.card (ThetaV k) = 2 * k + 2 ∧
      radiusNat (thetaGraph k) = 3 ∧
      inducedPathOrder (thetaGraph k) = 6 ∧
      neighbourhoodIndependenceSum (thetaGraph k) = 6 * k ∧
      neighbourhoodIndependenceSum (thetaGraph k) =
        3 * Fintype.card (ThetaV k) - 6 := by
  refine ⟨theta_strongC4Free k, theta_card k, theta_radius k hk, theta_inducedPathOrder hk,
    theta_S k, ?_⟩
  rw [theta_S k, theta_card k]
  omega

end InducedPaths
