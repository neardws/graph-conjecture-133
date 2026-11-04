/- Reusable cut-side reduction, independent of StatementsCore. -/
module
public import InducedPaths.Basic
open scoped SimpleGraph
open Finset SimpleGraph
@[expose] public section
namespace InducedPaths
variable {V : Type*} {G : SimpleGraph V}

/-- Lemma 2.3. No `C₄`-free hypothesis. `A` and `B` are the two sides of `G - v`. -/
theorem cut_mass_additive [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {v : V}
    (A B : Finset V) (hA : A.Nonempty) (hB : B.Nonempty) (hdisj : Disjoint A B)
    (hcover : (A ∪ B : Set V) = {w | w ≠ v})
    (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    neighbourhoodIndependenceSum G =
      neighbourhoodIndependenceSum (G.induce (insert v A : Set V)) +
        neighbourhoodIndependenceSum (G.induce (insert v B : Set V)) := by
  have _hAB : A.Nonempty ∧ B.Nonempty := ⟨hA, hB⟩
  have hvA : v ∉ A := by
    intro hv
    have hvmem : v ∈ (A ∪ B : Set V) := by simpa [Finset.mem_coe] using mem_union_left B hv
    rw [hcover] at hvmem
    exact hvmem rfl
  have hvB : v ∉ B := by
    intro hv
    have hvmem : v ∈ (A ∪ B : Set V) := by simpa [Finset.mem_coe] using mem_union_right A hv
    rw [hcover] at hvmem
    exact hvmem rfl
  have hvAB : v ∉ A ∪ B := by simp [hvA, hvB]
  have hmem : ∀ x, x ∈ A ∪ B ↔ x ≠ v := by
    intro x
    constructor
    · intro hx hxv
      exact hvAB (hxv ▸ hx)
    · intro hx
      have hxset : x ∈ (A ∪ B : Set V) := by
        rw [hcover]
        simpa using hx
      simpa [Finset.mem_coe] using hxset
  have hNA : ∀ a ∈ A, G.neighborSet a ⊆ (insert v A : Set V) := by
    intro a ha w hw
    have hadj : G.Adj a w := by simpa [mem_neighborSet] using hw
    by_cases hwv : w = v
    · subst hwv
      exact Set.mem_insert _ _
    · have hwAB : w ∈ A ∪ B := (hmem w).mpr hwv
      rcases mem_union.mp hwAB with hwA | hwB
      · exact Set.mem_insert_of_mem _ (by simpa [Finset.mem_coe] using hwA)
      · exact (hno a ha w hwB hadj).elim
  have hNB : ∀ b ∈ B, G.neighborSet b ⊆ (insert v B : Set V) := by
    intro b hb w hw
    have hadj : G.Adj b w := by simpa [mem_neighborSet] using hw
    by_cases hwv : w = v
    · subst hwv
      exact Set.mem_insert _ _
    · have hwAB : w ∈ A ∪ B := (hmem w).mpr hwv
      rcases mem_union.mp hwAB with hwA | hwB
      · exact (hno w hwA b hb hadj.symm).elim
      · exact Set.mem_insert_of_mem _ (by simpa [Finset.mem_coe] using hwB)
  let sA : Set V := (insert v A : Set V)
  let sB : Set V := (insert v B : Set V)
  haveI : DecidablePred (· ∈ sA) := fun _ => Classical.propDecidable _
  haveI : DecidablePred (· ∈ sB) := fun _ => Classical.propDecidable _
  have hvAs : v ∈ sA := by simp [sA]
  have hvBs : v ∈ sB := by simp [sB]
  let fA : V → ℕ := fun x =>
    if hx : x ∈ sA then lambda (G.induce sA) ⟨x, hx⟩ else 0
  let fB : V → ℕ := fun x =>
    if hx : x ∈ sB then lambda (G.induce sB) ⟨x, hx⟩ else 0
  have hsumA : neighbourhoodIndependenceSum (G.induce sA) = ∑ x ∈ insert v A, fA x := by
    rw [neighbourhoodIndependenceSum]
    have hpt : ∀ i : sA, lambda (G.induce sA) i = fA i := by
      intro i
      have hi : (i : V) ∈ sA := i.2
      have heq : (⟨(i : V), hi⟩ : sA) = i := Subtype.ext rfl
      simp only [fA]
      rw [dite_eq_left hi, heq]
    have : (∑ i : sA, lambda (G.induce sA) i) = ∑ i : sA, fA (i : V) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact hpt i
    rw [this, Finset.sum_set_coe]
    have hto : sA.toFinset = insert v A := by
      simp [sA]
    rw [hto]
  have hsumB : neighbourhoodIndependenceSum (G.induce sB) = ∑ x ∈ insert v B, fB x := by
    rw [neighbourhoodIndependenceSum]
    have hpt : ∀ i : sB, lambda (G.induce sB) i = fB i := by
      intro i
      have hi : (i : V) ∈ sB := i.2
      have heq : (⟨(i : V), hi⟩ : sB) = i := Subtype.ext rfl
      simp only [fB]
      rw [dite_eq_left hi, heq]
    have : (∑ i : sB, lambda (G.induce sB) i) = ∑ i : sB, fB (i : V) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      exact hpt i
    rw [this, Finset.sum_set_coe]
    have hto : sB.toFinset = insert v B := by
      simp [sB]
    rw [hto]
  have hfv : fA v = lambda (G.induce sA) ⟨v, hvAs⟩ := by simp only [fA]; rw [dite_eq_left hvAs]
  have hgv : fB v = lambda (G.induce sB) ⟨v, hvBs⟩ := by simp only [fB]; rw [dite_eq_left hvBs]
  have hfA : ∀ a ∈ A, fA a = lambda G a := by
    intro a ha
    have ha' : a ∈ sA := Set.mem_insert_of_mem _ (by simpa [Finset.mem_coe] using ha)
    have hfa : fA a = lambda (G.induce sA) ⟨a, ha'⟩ := by simp only [fA]; rw [dite_eq_left ha']
    rw [hfa, lambda_induce_eq ha' (hNA a ha)]
  have hfB : ∀ b ∈ B, fB b = lambda G b := by
    intro b hb
    have hb' : b ∈ sB := Set.mem_insert_of_mem _ (by simpa [Finset.mem_coe] using hb)
    have hfb : fB b = lambda (G.induce sB) ⟨b, hb'⟩ := by simp only [fB]; rw [dite_eq_left hb']
    rw [hfb, lambda_induce_eq hb' (hNB b hb)]
  have hS1 : neighbourhoodIndependenceSum (G.induce sA) =
      lambda (G.induce sA) ⟨v, hvAs⟩ + ∑ a ∈ A, lambda G a := by
    rw [hsumA, sum_insert hvA, hfv]
    exact congrArg _ (sum_congr rfl hfA)
  have hS2 : neighbourhoodIndependenceSum (G.induce sB) =
      lambda (G.induce sB) ⟨v, hvBs⟩ + ∑ b ∈ B, lambda G b := by
    rw [hsumB, sum_insert hvB, hgv]
    exact congrArg _ (sum_congr rfl hfB)
  have hinterA : G.neighborSet v ∩ sA = G.neighborSet v ∩ (A : Set V) := by
    ext x
    constructor
    · rintro ⟨hx, hmem⟩
      rcases Set.mem_insert_iff.mp hmem with rfl | hxA
      · simp [mem_neighborSet] at hx
      · exact ⟨hx, hxA⟩
    · rintro ⟨hx, hxA⟩
      exact ⟨hx, Set.mem_insert_of_mem _ hxA⟩
  have hinterB : G.neighborSet v ∩ sB = G.neighborSet v ∩ (B : Set V) := by
    ext x
    constructor
    · rintro ⟨hx, hmem⟩
      rcases Set.mem_insert_iff.mp hmem with rfl | hxB
      · simp [mem_neighborSet] at hx
      · exact ⟨hx, hxB⟩
    · rintro ⟨hx, hxB⟩
      exact ⟨hx, Set.mem_insert_of_mem _ hxB⟩
  have hlamvA : lambda (G.induce sA) ⟨v, hvAs⟩ =
      alphaIn G (G.neighborSet v ∩ (A : Set V)) := by
    rw [lambda_eq_alphaIn_neighbor_inter hvAs]
    exact alphaIn_congr hinterA
  have hlamvB : lambda (G.induce sB) ⟨v, hvBs⟩ =
      alphaIn G (G.neighborSet v ∩ (B : Set V)) := by
    rw [lambda_eq_alphaIn_neighbor_inter hvBs]
    exact alphaIn_congr hinterB
  have hNsplit : G.neighborSet v =
      (G.neighborSet v ∩ (A : Set V)) ∪ (G.neighborSet v ∩ (B : Set V)) := by
    ext x
    constructor
    · intro hx
      have hxne : x ≠ v := by
        intro hxv
        subst hxv
        simp [mem_neighborSet] at hx
      rcases mem_union.mp ((hmem x).mpr hxne) with hxA | hxB
      · exact Or.inl ⟨hx, by simpa [Finset.mem_coe] using hxA⟩
      · exact Or.inr ⟨hx, by simpa [Finset.mem_coe] using hxB⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hdisjN : Disjoint (G.neighborSet v ∩ (A : Set V)) (G.neighborSet v ∩ (B : Set V)) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    intro ⟨⟨_, ha⟩, _, hb⟩
    exact Finset.disjoint_left.mp hdisj (by simpa [Finset.mem_coe] using ha)
      (by simpa [Finset.mem_coe] using hb)
  have hnoN : ∀ ⦃a b : V⦄, a ∈ G.neighborSet v ∩ (A : Set V) →
      b ∈ G.neighborSet v ∩ (B : Set V) → ¬ G.Adj a b := by
    intro a b ha hb
    exact hno a (by simpa [Finset.mem_coe] using ha.2) b (by simpa [Finset.mem_coe] using hb.2)
  have hadd : lambda G v =
      lambda (G.induce sA) ⟨v, hvAs⟩ + lambda (G.induce sB) ⟨v, hvBs⟩ := by
    rw [hlamvA, hlamvB, lambda]
    conv_lhs => rw [hNsplit]
    exact alphaIn_union_no_cross hdisjN hnoN
  have huniv : (univ : Finset V) = insert v (A ∪ B) := by
    ext x
    simp only [mem_univ, true_iff, mem_insert]
    by_cases hx : x = v
    · exact Or.inl hx
    · exact Or.inr ((hmem x).mpr hx)
  have hSG : neighbourhoodIndependenceSum G =
      lambda G v + (∑ a ∈ A, lambda G a + ∑ b ∈ B, lambda G b) := by
    rw [neighbourhoodIndependenceSum, huniv, sum_insert hvAB, sum_union hdisj]
  calc neighbourhoodIndependenceSum G
      = lambda G v + (∑ a ∈ A, lambda G a + ∑ b ∈ B, lambda G b) := hSG
    _ = lambda (G.induce sA) ⟨v, hvAs⟩ + lambda (G.induce sB) ⟨v, hvBs⟩ +
          (∑ a ∈ A, lambda G a + ∑ b ∈ B, lambda G b) := by rw [hadd]
    _ = (lambda (G.induce sA) ⟨v, hvAs⟩ + ∑ a ∈ A, lambda G a) +
          (lambda (G.induce sB) ⟨v, hvBs⟩ + ∑ b ∈ B, lambda G b) := by ac_rfl
    _ = neighbourhoodIndependenceSum (G.induce sA) +
          neighbourhoodIndependenceSum (G.induce sB) := by rw [← hS1, ← hS2]

/-- No induced path of order at least four starts at the root (the exact
hypothesis accepted by Lemma 5.3). -/
def RootedNoP4 (H : SimpleGraph V) (s : V) : Prop :=
  ∀ n (hn : 4 ≤ n) (f : pathGraph n ↪g H),
    f ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 4) hn⟩ ≠ s

/-- A separated vertex set containing the root stays connected to the root.
No finiteness or forbidden-subgraph hypothesis is needed. -/
lemma connected_induce_of_boundary_root (hconn : G.Connected) {s : V} {X : Set V}
    (hs : s ∈ X) (hboundary : ∀ x ∈ X, ∀ y ∉ X, G.Adj x y → x = s) :
    (G.induce X).Connected := by
  classical
  let rec go {x : V} (p : G.Walk x s) (hx : x ∈ X) :
      (G.induce X).Reachable ⟨x, hx⟩ ⟨s, hs⟩ := by
    cases p with
    | nil => exact Reachable.refl _
    | @cons _ y _ hxy p =>
      by_cases hxs : x = s
      · subst x; exact Reachable.refl _
      · have hy : y ∈ X := by
          by_contra hy
          exact hxs (hboundary x hx y hy hxy)
        exact (show (G.induce X).Adj ⟨x, hx⟩ ⟨y, hy⟩ from hxy).reachable.trans (go p hy)
  have hroot (x : V) (hx : x ∈ X) : (G.induce X).Reachable ⟨x, hx⟩ ⟨s, hs⟩ :=
    (hconn x s).elim (fun p => go p hx)
  haveI : Nonempty X := ⟨⟨s, hs⟩⟩
  exact ⟨fun x y => (hroot x x.2).trans (hroot y y.2).symm⟩

/-- A two-sided cut partition. The finsets exclude the cut vertex. -/
structure CutPartition [Fintype V] (G : SimpleGraph V) (s : V) where
  left : Finset V
  right : Finset V
  left_nonempty : left.Nonempty
  right_nonempty : right.Nonempty
  disjoint : Disjoint left right
  cover : (left ∪ right : Set V) = {w | w ≠ s}
  no_cross : ∀ a ∈ left, ∀ b ∈ right, ¬ G.Adj a b

namespace CutPartition
open Classical
variable [Fintype V] {s : V} (D : CutPartition G s)

lemma root_not_left : s ∉ D.left := by
  intro h
  have : s ∈ (D.left ∪ D.right : Set V) := by simp [h]
  rw [D.cover] at this
  exact this rfl

lemma root_not_right : s ∉ D.right := by
  intro h
  have : s ∈ (D.left ∪ D.right : Set V) := by simp [h]
  rw [D.cover] at this
  exact this rfl

lemma mem_union (x : V) : x ∈ D.left ∪ D.right ↔ x ≠ s := by
  have h := Set.ext_iff.mp D.cover x
  simpa only [Set.mem_union, Finset.mem_coe, Finset.mem_union, Set.mem_setOf_eq] using h

lemma connected_left (hconn : G.Connected) :
    (G.induce (insert s D.left : Set V)).Connected := by
  apply connected_induce_of_boundary_root (s := s) hconn (by simp)
  intro x hx y hy hxy
  rcases hx with rfl | hx
  · rfl
  · exfalso
    have hys : y ≠ s := by intro h; subst y; exact hy (by simp)
    rcases Finset.mem_union.mp ((D.mem_union y).2 hys) with hyL | hyR
    · exact hy (Set.mem_insert_of_mem _ hyL)
    · exact D.no_cross x hx y hyR hxy

lemma connected_right (hconn : G.Connected) :
    (G.induce (insert s D.right : Set V)).Connected := by
  apply connected_induce_of_boundary_root (s := s) hconn (by simp)
  intro x hx y hy hxy
  rcases hx with rfl | hx
  · rfl
  · exfalso
    have hys : y ≠ s := by intro h; subst y; exact hy (by simp)
    rcases Finset.mem_union.mp ((D.mem_union y).2 hys) with hyL | hyR
    · exact D.no_cross y hyL x hx hxy.symm
    · exact hy (Set.mem_insert_of_mem _ hyR)

lemma card_partition : Fintype.card V = D.left.card + D.right.card + 1 := by
  classical
  have hu : (univ : Finset V) = insert s (D.left ∪ D.right) := by
    ext x
    simp only [mem_univ, true_iff, mem_insert]
    by_cases h : x = s
    · exact Or.inl h
    · exact Or.inr ((D.mem_union x).2 h)
  have hs : s ∉ D.left ∪ D.right := by
    simp [D.root_not_left, D.root_not_right]
  rw [← card_univ, hu, card_insert_of_notMem hs, card_union_of_disjoint D.disjoint]

lemma card_left : Fintype.card (insert s D.left : Set V) = D.left.card + 1 := by
  classical
  simp [D.root_not_left]

lemma card_right : Fintype.card (insert s D.right : Set V) = D.right.card + 1 := by
  classical
  simp [D.root_not_right]

lemma card_sides : Fintype.card V =
    Fintype.card (insert s D.left : Set V) +
      Fintype.card (insert s D.right : Set V) - 1 := by
  rw [D.card_left, D.card_right, D.card_partition]
  omega

lemma left_smaller : Fintype.card (insert s D.left : Set V) < Fintype.card V := by
  have := D.right_nonempty.card_pos
  rw [D.card_left, D.card_partition]
  omega

lemma right_smaller : Fintype.card (insert s D.right : Set V) < Fintype.card V := by
  have := D.left_nonempty.card_pos
  rw [D.card_right, D.card_partition]
  omega

lemma left_two_le : 2 ≤ Fintype.card (insert s D.left : Set V) := by
  have := D.left_nonempty.card_pos
  rw [D.card_left]
  omega

end CutPartition

open Classical

/-- A cut vertex supplies a nontrivial separated partition of its deletion. -/
theorem exists_cutPartition [Fintype V] {s : V} (hcut : IsCutVertex G s) :
    Nonempty (CutPartition G s) := by
  classical
  let H := G.induce {w | w ≠ s}
  obtain ⟨x, y, hxy⟩ : ∃ x y, ¬ H.Reachable x y := by
    simpa only [IsCutVertex, Preconnected, not_forall] using hcut
  let A : Finset V := univ.filter fun a => ∃ ha : a ≠ s, H.Reachable x ⟨a, ha⟩
  let B : Finset V := univ.filter fun b => b ≠ s ∧ b ∉ A
  have hx : x.val ∈ A := by simp only [A, mem_filter, mem_univ, true_and]; exact ⟨x.2, .refl _⟩
  have hy : y.val ∈ B := by
    simp only [B, mem_filter, mem_univ, true_and]
    refine ⟨y.2, ?_⟩
    intro hy
    obtain ⟨hy, hr⟩ := (mem_filter.mp hy).2
    exact hxy hr
  refine ⟨⟨A, B, ⟨x.val, hx⟩, ⟨y.val, hy⟩, ?_, ?_, ?_⟩⟩
  · exact Finset.disjoint_left.mpr fun a ha hb => (mem_filter.mp hb).2.2 ha
  · ext a
    simp only [Set.mem_union, mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro (ha | hb)
      · exact (mem_filter.mp ha).2.choose
      · exact (mem_filter.mp hb).2.1
    · intro ha
      by_cases h : a ∈ A
      · exact Or.inl h
      · exact Or.inr (mem_filter.mpr ⟨mem_univ _, ha, h⟩)
  · intro a ha b hb hab
    obtain ⟨haS, hra⟩ := (mem_filter.mp ha).2
    have hbS := (mem_filter.mp hb).2.1
    have hbA : b ∈ A := mem_filter.mpr ⟨mem_univ _, hbS,
      hra.trans (show H.Adj ⟨a, haS⟩ ⟨b, hbS⟩ from hab).reachable⟩
    exact (mem_filter.mp hb).2.2 hbA

open Classical

/-- The rooted side of a cut partition, in the form directly consumed by
Lemma 5.3. -/
structure RootedCutSide [Fintype V] (G : SimpleGraph V) (s : V)
    extends CutPartition G s where
  rooted_no_P4 : RootedNoP4 (G.induce (insert s left : Set V)) ⟨s, by simp⟩

/-- Strict cut arithmetic. The rooted bound is a parameter to avoid importing
StatementsCore upstream; Lemma 5.3 supplies it (even with a stronger RHS). -/
theorem cut_strict_mass_of_rooted_bound [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {s : V} (D : RootedCutSide G s)
    (hroot : neighbourhoodIndependenceSum (G.induce (insert s D.left : Set V)) ≤
      2 * (Fintype.card (insert s D.left : Set V) - 1))
    (hother : neighbourhoodIndependenceSum (G.induce (insert s D.right : Set V)) ≤
      3 * Fintype.card (insert s D.right : Set V)) :
    neighbourhoodIndependenceSum G < 3 * Fintype.card V := by
  have hmass := cut_mass_additive D.left D.right D.left_nonempty D.right_nonempty
    D.disjoint D.cover D.no_cross
  have hc := D.toCutPartition.card_partition
  have hl := D.toCutPartition.card_left
  have hr := D.toCutPartition.card_right
  have hn := D.left_nonempty.card_pos
  simp only [Fintype.card_eq_nat_card] at *
  omega

/-- Cardinal strong-induction interface. The only class-specific input is the
bound on the rooted side; the induction hypothesis is only invoked on the
proper connected remaining induced side. -/
theorem cut_strict_mass_of_induction [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {s : V} (D : RootedCutSide G s) (hconn : G.Connected)
    (hroot : neighbourhoodIndependenceSum (G.induce (insert s D.left : Set V)) ≤
      2 * (Fintype.card (insert s D.left : Set V) - 1))
    (ih : ∀ (X : Set V), Fintype.card X < Fintype.card V →
      (G.induce X).Connected →
      neighbourhoodIndependenceSum (G.induce X) ≤ 3 * Fintype.card X) :
    neighbourhoodIndependenceSum G < 3 * Fintype.card V :=
by
  apply cut_strict_mass_of_rooted_bound D hroot
  have hsmall := D.toCutPartition.right_smaller
  simp only [Fintype.card_eq_nat_card] at hsmall
  have h := ih (insert s D.right : Set V) (by simpa only [Fintype.card_eq_nat_card] using hsmall)
    (D.toCutPartition.connected_right hconn)
  exact (show ∀ (i j : Fintype (insert s D.right : Set V)),
    @neighbourhoodIndependenceSum _ i _ ≤ 3 * @Fintype.card _ i →
    @neighbourhoodIndependenceSum _ j _ ≤ 3 * @Fintype.card _ j from
      fun i j => by have hij : i = j := Subsingleton.elim _ _; cases hij; exact id) _ _ h

set_option maxHeartbeats 4000000 in
/-- Two rooted induced `P₄`s on opposite cut sides concatenate to an induced
`P₇`. This elementary obstruction does not use strong `C₄`-freeness. -/
lemma CutPartition.not_two_rooted_P4 [Fintype V] {s : V} (D : CutPartition G s)
    (hp : IsPkFree G 7)
    (f : pathGraph 4 ↪g G.induce (insert s D.left : Set V))
    (g : pathGraph 4 ↪g G.induce (insert s D.right : Set V))
    (hf : f 0 = ⟨s, by simp⟩) (hg : g 0 = ⟨s, by simp⟩) : False := by
  classical
  let F : pathGraph 4 ↪g G := f.trans (Embedding.induce _)
  let J : pathGraph 4 ↪g G := g.trans (Embedding.induce _)
  have hF : F 0 = s := congrArg Subtype.val hf
  have hJ : J 0 = s := congrArg Subtype.val hg
  have hFL (i : Fin 4) (hi : i ≠ 0) : F i ∈ D.left := by
    have h := (f i).2
    rcases h with h | h
    · exact False.elim (hi (F.injective (h.trans hF.symm)))
    · exact h
  have hJR (i : Fin 4) (hi : i ≠ 0) : J i ∈ D.right := by
    have h := (g i).2
    rcases h with h | h
    · exact False.elim (hi (J.injective (h.trans hJ.symm)))
    · exact h
  have hcross (i j : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) :
      ¬ G.Adj (F i) (J j) := D.no_cross _ (hFL i hi) _ (hJR j hj)
  have hcrossne (i j : Fin 4) (hi : i ≠ 0) (hj : j ≠ 0) : F i ≠ J j := by
    intro h
    exact Finset.disjoint_left.mp D.disjoint (hFL i hi) (h ▸ hJR j hj)
  let v : Fin 7 → V := fun i =>
    if i = 0 then F 3 else if i = 1 then F 2 else if i = 2 then F 1
    else if i = 3 then F 0 else if i = 4 then J 1 else if i = 5 then J 2 else J 3
  have hFinj := F.injective
  have hJinj := J.injective
  have hrelF (i j : Fin 4) : G.Adj (F i) (F j) ↔ (pathGraph 4).Adj i j := F.map_rel_iff
  have hrelJ (i j : Fin 4) : G.Adj (J i) (J j) ↔ (pathGraph 4).Adj i j := J.map_rel_iff
  apply hp
  refine ⟨{ toFun := v, inj' := ?_, map_rel_iff' := ?_ }⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp only [v, Fin.reduceEq, ↓reduceIte] at hij ⊢ <;>
      first
      | rfl
      | exact False.elim (by have := hFinj hij; norm_num at this)
      | exact False.elim (by have := hJinj hij; norm_num at this)
      | exact False.elim (hcrossne _ _ (by decide) (by decide) hij)
      | exact False.elim (hcrossne _ _ (by decide) (by decide) hij.symm)
      | exact False.elim (by rw [hF, ← hJ] at hij; have := hJinj hij; norm_num at this)
      | exact False.elim (by rw [hF, ← hJ] at hij; have := hJinj hij; norm_num at this)
  · intro i j
    change G.Adj (v i) (v j) ↔ (pathGraph 7).Adj i j
    fin_cases i <;> fin_cases j <;>
      simp only [v, Fin.reduceEq, ↓reduceIte] <;>
      first
      | solve | simp [hrelF, pathGraph_adj]
      | solve | simp [hrelJ, pathGraph_adj]
      | solve | rw [hF, ← hJ]; simp [hrelJ, pathGraph_adj]
      | solve | simp [hcross, pathGraph_adj]
      | solve | rw [G.adj_comm]; simp [hcross, pathGraph_adj]

/-- Restriction to the first four vertices suffices for the rooted condition. -/
lemma rootedNoP4_of_no_embedding {H : SimpleGraph V} {s : V}
    (h : ∀ f : pathGraph 4 ↪g H, f 0 ≠ s) : RootedNoP4 H s := by
  intro n hn f hf
  let e := (pathGraph_mono hn).trans f
  apply h e
  change f ((pathGraph_mono hn) 0) = s
  have hz : (pathGraph_mono hn) 0 =
      ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 4) hn⟩ := Fin.ext rfl
  rw [hz]
  exact hf

/-- At any cut vertex of a `P₇`-free graph, one of the two connected proper
sides is rooted-`P₄`-free. The side need not be prescribed beforehand. -/
theorem exists_rootedCutSide [Fintype V] {s : V} (hp : IsPkFree G 7)
    (hcut : IsCutVertex G s) : Nonempty (RootedCutSide G s) := by
  classical
  obtain ⟨D⟩ := exists_cutPartition hcut
  by_cases hl : ∀ f : pathGraph 4 ↪g G.induce (insert s D.left : Set V),
      f 0 ≠ ⟨s, by simp⟩
  · exact ⟨⟨D, rootedNoP4_of_no_embedding hl⟩⟩
  · push_neg at hl
    obtain ⟨f, hf⟩ := hl
    let E : CutPartition G s := {
      left := D.right, right := D.left,
      left_nonempty := D.right_nonempty, right_nonempty := D.left_nonempty,
      disjoint := D.disjoint.symm,
      cover := by simpa [Set.union_comm] using D.cover,
      no_cross := fun a ha b hb hab => D.no_cross b hb a ha hab.symm }
    refine ⟨⟨E, rootedNoP4_of_no_embedding ?_⟩⟩
    intro g hg
    exact D.not_two_rooted_P4 hp f g hf hg

/-- End-to-end cut reduction for cardinal strong induction. Instantiate the
rooted bound by Lemma 5.3; hereditary restrictions (one triangle, for example)
can be discharged when supplying `ih`. -/
theorem cut_strict_mass [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hp : IsPkFree G 7) {s : V} (hcut : IsCutVertex G s)
    (rooted_bound : ∀ (X : Set V) (r : X), (G.induce X).Connected →
      RootedNoP4 (G.induce X) r →
      neighbourhoodIndependenceSum (G.induce X) ≤ 2 * (Fintype.card X - 1))
    (ih : ∀ (X : Set V), Fintype.card X < Fintype.card V →
      (G.induce X).Connected →
      neighbourhoodIndependenceSum (G.induce X) ≤ 3 * Fintype.card X) :
    neighbourhoodIndependenceSum G < 3 * Fintype.card V := by
  obtain ⟨D⟩ := exists_rootedCutSide hp hcut
  have hr := rooted_bound (insert s D.left : Set V) ⟨s, by simp⟩
    (D.toCutPartition.connected_left hconn) D.rooted_no_P4
  apply cut_strict_mass_of_induction D hconn ?_ ih
  exact (show ∀ (i j : Fintype (insert s D.left : Set V)),
    @neighbourhoodIndependenceSum _ i _ ≤ 2 * (@Fintype.card _ i - 1) →
    @neighbourhoodIndependenceSum _ j _ ≤ 2 * (@Fintype.card _ j - 1) from
      fun i j => by have hij : i = j := Subsingleton.elim _ _; cases hij; exact id) _ _ hr

end InducedPaths
