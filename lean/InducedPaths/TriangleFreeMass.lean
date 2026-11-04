/- The triangle-free part of Theorem 5.5, isolated from its downstream GEN₃ clause. -/
module

public import InducedPaths.ChenXuCounts
public import InducedPaths.ChenXuCore
public import InducedPaths.CanonicalMass

open SimpleGraph

@[expose] public section
namespace InducedPaths

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A nonnegative core deficit plus the number of stripped vertices bounds
and characterizes equality, without truncated-subtraction assumptions. -/
theorem triangleFree_mass_from_core {h q : ℕ}
    (hle : h ≤ Fintype.card V)
    (he : edgeCount G = q + (Fintype.card V - h))
    (hq : 2 * q ≤ 3 * h)
    (heq : 2 * q = 3 * h → h = Fintype.card V → Nonempty (G ≃g petersenGraph))
    (hpetersen : Nonempty (G ≃g petersenGraph) →
      2 * edgeCount G = 3 * Fintype.card V) :
    2 * edgeCount G ≤ 3 * Fintype.card V ∧
      (2 * edgeCount G = 3 * Fintype.card V ↔ Nonempty (G ≃g petersenGraph)) := by
  constructor
  · omega
  · constructor
    · intro h
      apply heq <;> omega
    · exact hpetersen

/-- A core occupying every vertex gives an actual ambient isomorphism. -/
noncomputable def coreFullIso (Q : Set V) (hQ : Nat.card Q = Fintype.card V) :
    G ≃g G.induce Q := by
  classical
  have hsurj : Function.Surjective (Subtype.val : Q → V) := by
    exact ((Fintype.bijective_iff_injective_and_card (Subtype.val : Q → V)).2
      ⟨Subtype.val_injective, by simpa only [Nat.card_eq_fintype_card] using hQ⟩).surjective
  let e : Q ≃ V := Equiv.ofBijective Subtype.val ⟨Subtype.val_injective, hsurj⟩
  exact ({ e with map_rel_iff' := by intros; rfl } : G.induce Q ≃g G).symm

/-- The triangle-free inequality and Petersen equality, independently of GEN₃. -/
theorem triangleFree_edge_bound (hconn : G.Connected) (htri : G.CliqueFree 3)
    (hC : StrongC4Free G) (hp : IsPkFree G 7) :
    2 * edgeCount G ≤ 3 * Fintype.card V ∧
      (2 * edgeCount G = 3 * Fintype.card V ↔ Nonempty (G ≃g petersenGraph)) := by
  classical
  obtain ⟨Q, hd, hqc, hqt, hqC, hqp, hcut, hclass, he, hdef⟩ :=
    chenXu_tree_core hconn htri hC hp
  letI := hd
  have hle : Nat.card Q ≤ Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le (· ∈ Q)
  have hq : 2 * edgeCount (G.induce Q) ≤ 3 * Nat.card Q := by
    rcases hclass with hi | hi | hf
    · obtain ⟨e⟩ := hi
      have he' := chenXu_edgeCount_iso e
      have hn' := Fintype.card_congr e.toEquiv
      have hz : edgeCount (completeGraph (Fin 1)) = 0 := by decide
      simp only [Fintype.card_fin] at hn'
      rw [Nat.card_eq_fintype_card]
      omega
    · obtain ⟨e⟩ := hi
      have he' := chenXu_edgeCount_iso e
      have hn' := Fintype.card_congr e.toEquiv
      have hz : edgeCount k2Graph = 1 := by decide
      simp only [Fintype.card_fin] at hn'
      rw [Nat.card_eq_fintype_card]
      omega
    · simpa only [Nat.card_eq_fintype_card] using chenXu_family_edge_bound hf
  apply triangleFree_mass_from_core hle he hq
  · intro heq hfull
    have hiso : Nonempty (G.induce Q ≃g petersenGraph) := by
      rcases hclass with hi | hi | hf
      · obtain ⟨e⟩ := hi
        have he' := chenXu_edgeCount_iso e
        have hn' := Fintype.card_congr e.toEquiv
        have hz : edgeCount (completeGraph (Fin 1)) = 0 := by decide
        simp only [Fintype.card_fin] at hn'
        rw [Nat.card_eq_fintype_card] at heq
        omega
      · obtain ⟨e⟩ := hi
        have he' := chenXu_edgeCount_iso e
        have hn' := Fintype.card_congr e.toEquiv
        have hz : edgeCount k2Graph = 1 := by decide
        simp only [Fintype.card_fin] at hn'
        rw [Nat.card_eq_fintype_card] at heq
        omega
      · rcases chenXu_counts hf with ⟨hi, _⟩ | ⟨_, hb⟩
        · exact hi
        · rw [Nat.card_eq_fintype_card] at heq
          have hpos : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr hqc.nonempty
          omega
    obtain ⟨e⟩ := hiso
    exact ⟨(coreFullIso Q hfull).trans e⟩
  · intro hi
    obtain ⟨e⟩ := hi
    have he' := chenXu_edgeCount_iso e
    have hn' := Fintype.card_congr e.toEquiv
    obtain ⟨⟨pc, pe⟩, _⟩ := chenXu_fixed_counts
    omega

/-- Triangle-free neighbourhood mass is twice the edge count. -/
theorem triangleFree_mass_eq_twice_edges (htri : G.CliqueFree 3) :
    neighbourhoodIndependenceSum G = 2 * edgeCount G := by
  have ht : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj a c := by
    intro a b c hab hbc hac
    exact htri {a,b,c} (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)
  rw [mass_eq_degree_sum_of_no_triangle ht]
  simpa [edgeCount, Nat.mul_comm] using G.sum_degrees_eq_twice_card_edges

/-- Standalone triangle-free mass theorem, with exact Petersen equality. -/
theorem triangleFree_mass_bound (hconn : G.Connected) (htri : G.CliqueFree 3)
    (hC : StrongC4Free G) (hp : IsPkFree G 7) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V ∧
      (neighbourhoodIndependenceSum G = 3 * Fintype.card V ↔
        Nonempty (G ≃g petersenGraph)) := by
  rw [triangleFree_mass_eq_twice_edges htri]
  exact triangleFree_edge_bound hconn htri hC hp

end InducedPaths
