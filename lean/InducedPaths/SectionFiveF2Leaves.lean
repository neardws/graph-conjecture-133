module

public import InducedPaths.SectionFiveReconstruction

open SimpleGraph

@[expose] public section
namespace InducedPaths
namespace SectionFiveReconstruction

/-- A leaf at the near internal vertex of one branch exposes an induced P₇
using two other branches. -/
lemma f2_A1_leaf_not_P7free {t : ℕ} (i j k : Fin t)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ IsPkFree (addLeaf (f2Graph t) (.A1 i)) 7 := by
  classical
  intro hp
  let p : Fin 7 → Option (F2V t) :=
    ![none, some (.A1 i), some (.cycle 0), some (.A1 j),
      some (.A3 j), some (.cycle 2), some (.A3 k)]
  have pinj : Function.Injective p := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [p, hij, hik, hjk, Ne.symm]
  have padj : ∀ a b, (addLeaf (f2Graph t) (.A1 i)).Adj (p a) (p b) ↔
      (pathGraph 7).Adj a b := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [p, addLeaf, simpleOf, f2Graph, cycleGraph_adj, pathGraph_adj,
        hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk] <;> decide
  exact hp ⟨{ toFun := p, inj' := pinj, map_rel_iff' := fun {a b} => padj a b }⟩

/-- The opposite side is witnessed by the reversed hub orientation. -/
lemma f2_A3_leaf_not_P7free {t : ℕ} (i j k : Fin t)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ IsPkFree (addLeaf (f2Graph t) (.A3 i)) 7 := by
  classical
  intro hp
  let p : Fin 7 → Option (F2V t) :=
    ![none, some (.A3 i), some (.cycle 2), some (.A3 j),
      some (.A1 j), some (.cycle 0), some (.A1 k)]
  have pinj : Function.Injective p := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [p, hij, hik, hjk, Ne.symm]
  have padj : ∀ a b, (addLeaf (f2Graph t) (.A3 i)).Adj (p a) (p b) ↔
      (pathGraph 7).Adj a b := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [p, addLeaf, simpleOf, f2Graph, cycleGraph_adj, pathGraph_adj,
        hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk] <;> decide
  exact hp ⟨{ toFun := p, inj' := pinj, map_rel_iff' := fun {a b} => padj a b }⟩

lemma f2_cycle4_leaf_not_P7free {t : ℕ} (j k : Fin t) (hjk : j ≠ k) :
    ¬ IsPkFree (addLeaf (f2Graph t) (.cycle 4)) 7 := by
  classical
  intro hp
  let p : Fin 7 → Option (F2V t) :=
    ![none, some (.cycle 4), some (.cycle 0), some (.A1 j),
      some (.A3 j), some (.cycle 2), some (.A3 k)]
  have pinj : Function.Injective p := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [p, hjk, Ne.symm]
  have padj : ∀ a b, (addLeaf (f2Graph t) (.cycle 4)).Adj (p a) (p b) ↔
      (pathGraph 7).Adj a b := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [p, addLeaf, simpleOf, f2Graph, cycleGraph_adj, pathGraph_adj,
        hjk, Ne.symm hjk] <;> decide
  exact hp ⟨{ toFun := p, inj' := pinj, map_rel_iff' := fun {a b} => padj a b }⟩

lemma f2_cycle3_leaf_not_P7free {t : ℕ} (j k : Fin t) (hjk : j ≠ k) :
    ¬ IsPkFree (addLeaf (f2Graph t) (.cycle 3)) 7 := by
  classical
  intro hp
  let p : Fin 7 → Option (F2V t) :=
    ![none, some (.cycle 3), some (.cycle 2), some (.A3 j),
      some (.A1 j), some (.cycle 0), some (.A1 k)]
  have pinj : Function.Injective p := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [p, hjk, Ne.symm]
  have padj : ∀ a b, (addLeaf (f2Graph t) (.cycle 3)).Adj (p a) (p b) ↔
      (pathGraph 7).Adj a b := by
    intro a b
    fin_cases a <;> fin_cases b <;>
      simp [p, addLeaf, simpleOf, f2Graph, cycleGraph_adj, pathGraph_adj,
        hjk, Ne.symm hjk] <;> decide
  exact hp ⟨{ toFun := p, inj' := pinj, map_rel_iff' := fun {a b} => padj a b }⟩

/-- For the equality range there are enough branches to obstruct every internal site. -/
theorem f2_leaf_site {t : ℕ} (ht : 5 ≤ t) (r : F2V t)
    (hp : IsPkFree (addLeaf (f2Graph t) r) 7) :
    r = .cycle 0 ∨ r = .cycle 1 ∨ r = .cycle 2 := by
  classical
  have two (i : Fin t) : ∃ j k : Fin t, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    let a : Fin t := ⟨0, by omega⟩
    let b : Fin t := ⟨1, by omega⟩
    let c : Fin t := ⟨2, by omega⟩
    by_cases ha : i = a
    · exact ⟨b, c, by subst i; intro h; have := congrArg Fin.val h; simp [a, b, c] at this, by subst i; intro h; have := congrArg Fin.val h; simp [a, b, c] at this, by intro h; have := congrArg Fin.val h; simp [a, b, c] at this⟩
    · by_cases hb : i = b
      · exact ⟨a, c, ha, by subst i; intro h; have := congrArg Fin.val h; simp [a, b, c] at this, by intro h; have := congrArg Fin.val h; simp [a, b, c] at this⟩
      · exact ⟨a, b, ha, hb, by intro h; have := congrArg Fin.val h; simp [a, b, c] at this⟩
  cases r with
  | cycle c =>
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · exact (f2_cycle3_leaf_not_P7free ⟨0, by omega⟩ ⟨1, by omega⟩ (by intro h; have := congrArg Fin.val h; norm_num at this) hp).elim
    · exact (f2_cycle4_leaf_not_P7free ⟨0, by omega⟩ ⟨1, by omega⟩ (by intro h; have := congrArg Fin.val h; norm_num at this) hp).elim
  | A1 i =>
    obtain ⟨j, k, hij, hik, hjk⟩ := two i
    exact (f2_A1_leaf_not_P7free i j k hij hik hjk hp).elim
  | A3 i =>
    obtain ⟨j, k, hij, hik, hjk⟩ := two i
    exact (f2_A3_leaf_not_P7free i j k hij hik hjk hp).elim

def flipF2 {t : ℕ} : F2V t → F2V t
  | .cycle i => .cycle (1 + 1 - i)
  | .A1 i => .A3 i
  | .A3 i => .A1 i

lemma flipF2_involution {t : ℕ} (v : F2V t) : flipF2 (flipF2 v) = v := by
  cases v with
  | cycle i => fin_cases i <;> rfl
  | A1 i => rfl
  | A3 i => rfl

/-- The symmetry exchanging the two F₂ hubs. -/
def f2HubSwap (t : ℕ) : f2Graph t ≃g f2Graph t where
  toFun := flipF2
  invFun := flipF2
  left_inv := flipF2_involution
  right_inv := flipF2_involution
  map_rel_iff' := by
    intro v w
    cases v with
    | cycle i =>
      cases w with
      | cycle j => fin_cases i <;> fin_cases j <;>
        simp [flipF2, f2Graph, simpleOf, cycleGraph_adj] <;> decide
      | A1 j => fin_cases i <;> simp [flipF2, f2Graph, simpleOf]
      | A3 j => fin_cases i <;> simp [flipF2, f2Graph, simpleOf]
    | A1 i =>
      cases w with
      | cycle j => fin_cases j <;> simp [flipF2, f2Graph, simpleOf]
      | A1 j => simp [flipF2, f2Graph, simpleOf]
      | A3 j => simp [flipF2, f2Graph, simpleOf, eq_comm]
    | A3 i =>
      cases w with
      | cycle j => fin_cases j <;> simp [flipF2, f2Graph, simpleOf]
      | A1 j => simp [flipF2, f2Graph, simpleOf, eq_comm]
      | A3 j => simp [flipF2, f2Graph, simpleOf]

/-- Every admissible one-leaf F₂ extension is one of the two exact named models. -/
theorem f2_leaf_canonical {t : ℕ} (ht : 5 ≤ t) (r : F2V t)
    (hp : IsPkFree (addLeaf (f2Graph t) r) 7) :
    Nonempty (addLeaf (f2Graph t) r ≃g f2HubLeaf t) ∨
      Nonempty (addLeaf (f2Graph t) r ≃g f2MidLeaf t) := by
  rcases f2_leaf_site ht r hp with hr | hr | hr
  · subst r; exact Or.inl ⟨SimpleGraph.Iso.refl⟩
  · subst r; exact Or.inr ⟨SimpleGraph.Iso.refl⟩
  · subst r
    left
    have hi := addLeafIso (f2HubSwap t) (.cycle 2)
    change Nonempty (addLeaf (f2Graph t) (.cycle 2) ≃g addLeaf (f2Graph t) (.cycle 0))
    exact ⟨hi⟩

/-- Assemble the actual F₂ one-leaf classification from the generic stripping API. -/
theorem f2_one_exterior_canonical {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) (Q : Set V) [Fintype Q] {t : ℕ} (ht : 5 ≤ t)
    (hc : G.Connected) (hp : IsPkFree G 7)
    (hq : Fintype.card Q + 1 = Fintype.card V)
    (hu : ∀ x, x ∉ Q → (Q ∩ G.neighborSet x).Subsingleton)
    (hi : Nonempty (G.induce Q ≃g f2Graph t)) :
    Nonempty (G ≃g f2HubLeaf t) ∨ Nonempty (G ≃g f2MidLeaf t) := by
  obtain ⟨r, ⟨e⟩⟩ := isoNamedLeafOfCardGapOne G (f2Graph t) Q hc hq hu hi
  have hp' : IsPkFree (addLeaf (f2Graph t) r) 7 := by
    intro hpath
    exact hp (hpath.trans e.symm.isIndContained)
  rcases f2_leaf_canonical ht r hp' with hi' | hi'
  · obtain ⟨i⟩ := hi'
    exact Or.inl ⟨e.trans i⟩
  · obtain ⟨i⟩ := hi'
    exact Or.inr ⟨e.trans i⟩

end SectionFiveReconstruction
end InducedPaths
