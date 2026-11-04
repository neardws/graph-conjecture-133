module

public import InducedPaths.Graphs
public import InducedPaths.IsoLoss
public import Mathlib.Data.Fintype.BigOperators

open scoped SimpleGraph
open Finset SimpleGraph Classical

@[expose] public section
set_option maxHeartbeats 1600000

namespace InducedPaths

variable {V : Type*} {G : SimpleGraph V}

namespace RadiusFourExtension

/-- Total number of vertices in the six attachment classes. -/
noncomputable def attachmentCount [Fintype V] (E : RadiusFourExtension G) : ℕ :=
  ∑ i, Nat.card (E.attach i)

/-- Indices of the occupied cycle edges. -/
abbrev Occupied (E : RadiusFourExtension G) := {i : Fin 6 // (E.edgeVert i).isSome}

noncomputable def occupiedVertex (E : RadiusFourExtension G) (i : E.Occupied) : V :=
  (E.edgeVert i.val).get (by simpa using i.property)

 theorem occupiedVertex_spec (E : RadiusFourExtension G) (i : E.Occupied) :
    E.edgeVert i.val = some (E.occupiedVertex i) := by
  exact (Option.some_get _).symm

/-- The disjoint partition into cycle, attachment, and edge-added vertices. -/
noncomputable def vertexEquiv (E : RadiusFourExtension G) :
    (Fin 6 ⊕ (Σ i : Fin 6, E.attach i) ⊕ E.Occupied) ≃ V :=
  Equiv.ofBijective
    (Sum.elim E.cycleEmb (Sum.elim (fun x => x.2.val) E.occupiedVertex)) (by
      constructor
      · intro x y h
        cases x with
        | inl i =>
          cases y with
          | inl j => exact congrArg Sum.inl (E.cycleEmb.injective h)
          | inr y =>
            cases y with
            | inl y => exact (E.attach_off_cycle y.1 y.2.val y.2.property i h).elim
            | inr j => exact (E.edge_off_cycle j.val _ (E.occupiedVertex_spec j) i h).elim
        | inr x =>
          cases x with
          | inl x =>
            cases y with
            | inl j => exact (E.attach_off_cycle x.1 x.2.val x.2.property j h.symm).elim
            | inr y =>
              cases y with
              | inl y =>
                have hij : x.1 = y.1 := by
                  by_contra hn
                  change x.2.val = y.2.val at h
                  exact Set.disjoint_left.mp (E.attach_pairwise hn) x.2.property
                    (h.symm ▸ y.2.property)
                obtain ⟨i, x⟩ := x
                obtain ⟨j, y⟩ := y
                dsimp at hij h
                subst j
                exact congrArg (fun z => Sum.inr (Sum.inl z)) (Sigma.ext rfl (heq_of_eq (Subtype.ext h)))
              | inr j => exact (E.edge_off_attach j.val _ x.1 x.2.val
                  (E.occupiedVertex_spec j) x.2.property h.symm).elim
          | inr i =>
            cases y with
            | inl j => exact (E.edge_off_cycle i.val _ (E.occupiedVertex_spec i) j h.symm).elim
            | inr y =>
              cases y with
              | inl y => exact (E.edge_off_attach i.val _ y.1 y.2.val
                  (E.occupiedVertex_spec i) y.2.property h).elim
              | inr j =>
                change E.occupiedVertex i = E.occupiedVertex j at h
                have hij := E.edge_inj i.val j.val _ (E.occupiedVertex_spec i)
                  (h.symm ▸ E.occupiedVertex_spec j)
                exact congrArg (fun z => Sum.inr (Sum.inr z)) (Subtype.ext hij)
      · intro v
        rcases E.exhaustive v with ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩
        · exact ⟨Sum.inl i, hi⟩
        · exact ⟨Sum.inr (Sum.inl ⟨i, ⟨v, hi⟩⟩), rfl⟩
        · have his : (E.edgeVert i).isSome := by simp [hi]
          refine ⟨Sum.inr (Sum.inr ⟨i, his⟩), ?_⟩
          exact Option.some.inj ((E.occupiedVertex_spec ⟨i, his⟩).symm.trans hi))

 theorem card_occupied (E : RadiusFourExtension G) : Nat.card E.Occupied = addedCount E := by
  classical
  simp [Occupied, addedCount, Nat.card_eq_fintype_card, Fintype.card_subtype]

 theorem card_vertices [Fintype V] (E : RadiusFourExtension G) :
    Fintype.card V = 6 + E.attachmentCount + addedCount E := by
  classical
  have h := Fintype.card_congr E.vertexEquiv
  have ho : Fintype.card E.Occupied = addedCount E := by
    simpa [Nat.card_eq_fintype_card] using E.card_occupied
  simpa [Fintype.card_sum, Fintype.card_sigma, attachmentCount,
    Nat.card_eq_fintype_card, ho, Nat.add_assoc] using h.symm

 theorem sum_vertices [Fintype V] (E : RadiusFourExtension G) (f : V → ℕ) :
    (∑ v, f v) = (∑ i, f (E.cycleEmb i)) +
      (∑ i, ∑ v : E.attach i, f v.val) + ∑ i : E.Occupied, f (E.occupiedVertex i) := by
  classical
  rw [← Fintype.sum_equiv E.vertexEquiv (fun x => f (E.vertexEquiv x)) f (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma]
  exact (Nat.add_assoc _ _ _).symm

 theorem matchingCount_eq_zero_iff [Fintype V] [DecidableEq V]
    (E : RadiusFourExtension G) :
    matchingCount E = 0 ↔ ∀ i, ∀ v ∈ E.attach i, ∀ w ∈ E.attach i, ¬ G.Adj v w := by
  classical
  simp only [matchingCount, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_const]
  constructor
  · intro h i v hv w hw hadj
    have hz := h i
    have he : s(⟨v, hv⟩, ⟨w, hw⟩) ∈ (G.induce (E.attach i)).edgeFinset := by
      exact (G.induce (E.attach i)).mem_edgeFinset.mpr hadj
    have hemp : (G.induce (E.attach i)).edgeFinset = ∅ := Finset.card_eq_zero.mp hz
    simpa [hemp] using he
  · intro h i
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    exact h i e.out.1.val e.out.1.property e.out.2.val e.out.2.property
      (adj_out_of_mem _ e he)

 theorem isolated_attachment_of_matchingCount_zero [Fintype V] [DecidableEq V]
    (E : RadiusFourExtension G) (hm : matchingCount E = 0) :
    ∀ i, ∃ v ∈ E.attach i, ∀ w ∈ E.attach i, ¬ G.Adj v w := by
  intro i
  obtain ⟨v, hv⟩ := E.attach_nonempty i
  exact ⟨v, hv, (E.matchingCount_eq_zero_iff.mp hm) i v hv⟩

theorem degree_partition [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) (v : V) :
    G.degree v = (∑ i, if G.Adj v (E.cycleEmb i) then 1 else 0) +
      (∑ i, ∑ w : E.attach i, if G.Adj v w.val then 1 else 0) +
      ∑ i : E.Occupied, if G.Adj v (E.occupiedVertex i) then 1 else 0 := by
  classical
  have hv : G.degree v = ∑ w : V, if G.Adj v w then 1 else 0 := by
    simpa only [Finset.sum_boole, Nat.cast_id, ← G.neighborFinset_eq_filter] using
      (G.card_neighborFinset_eq_degree v).symm
  rw [hv, E.sum_vertices]

 theorem occupied_degree [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) (i : E.Occupied) :
    G.degree (E.occupiedVertex i) = 2 := by
  classical
  have hne : E.cycleEmb i.val ≠ E.cycleEmb (i.val + 1) := by
    apply E.cycleEmb.injective.ne
    have hf : ∀ j : Fin 6, j ≠ j + 1 := by decide
    exact hf i.val
  have hn : G.neighborFinset (E.occupiedVertex i) =
      {E.cycleEmb i.val, E.cycleEmb (i.val + 1)} := by
    ext w
    simp only [mem_neighborFinset, mem_insert, mem_singleton]
    exact E.edge_adj i.val _ (E.occupiedVertex_spec i) w
  rw [← G.card_neighborFinset_eq_degree, hn, Finset.card_pair hne]

 theorem attachment_degree_le_one [Fintype V] [DecidableEq V]
    (E : RadiusFourExtension G) (i : Fin 6) (v : E.attach i) :
    (G.induce (E.attach i)).degree v ≤ 1 := by
  classical
  apply (Finset.card_le_one).mpr
  intro a ha b hb
  exact Subtype.ext (E.matching i v.val v.property b.val b.property
    (((G.induce (E.attach i)).mem_neighborFinset v b).mp hb) a.val a.property
    (((G.induce (E.attach i)).mem_neighborFinset v a).mp ha))

 theorem matching_vertices_bound [Fintype V] [DecidableEq V]
    (E : RadiusFourExtension G) : 2 * matchingCount E ≤ E.attachmentCount := by
  classical
  have hi (i : Fin 6) := two_mul_edgeFinset_card_le
    (H := G.induce (E.attach i)) (E.attachment_degree_le_one i)
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 6))) => hi i)
  simpa [matchingCount, attachmentCount, Finset.mul_sum, edgeCount,
    Nat.card_eq_fintype_card] using h

theorem attachment_degree [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) (i : Fin 6) (v : E.attach i) :
    G.degree v.val = 1 + (G.induce (E.attach i)).degree v := by
  classical
  have hn : G.neighborFinset v.val = insert (E.cycleEmb i)
      (((G.induce (E.attach i)).neighborFinset v).image Subtype.val) := by
    ext w
    simp only [mem_neighborFinset, mem_insert, mem_image]
    constructor
    · intro h
      rcases E.no_extra_attach i v.val w v.property h with hw | hw
      · exact Or.inl hw
      · exact Or.inr ⟨⟨w, hw⟩, h, rfl⟩
    · rintro (rfl | ⟨w, hw, rfl⟩)
      · exact (E.trace i v.val v.property i).mpr rfl
      · exact hw
  have hoff : E.cycleEmb i ∉
      (((G.induce (E.attach i)).neighborFinset v).image Subtype.val) := by
    rintro h
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp h
    exact E.attach_off_cycle i w.val w.property i hw.symm
  rw [← G.card_neighborFinset_eq_degree, hn, Finset.card_insert_of_notMem hoff,
    Finset.card_image_of_injective _ Subtype.val_injective,
    (G.induce (E.attach i)).card_neighborFinset_eq_degree]
  omega

 theorem sum_attachment_degrees [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) :
    (∑ i, ∑ v : E.attach i, G.degree v.val) = E.attachmentCount + 2 * matchingCount E := by
  classical
  simp_rw [E.attachment_degree]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    mul_one, SimpleGraph.sum_degrees_eq_twice_card_edges]
  simp only [attachmentCount, matchingCount, edgeCount, Finset.mul_sum,
    Nat.card_eq_fintype_card]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact congrArg Finset.card (by ext e; simp)

 theorem sum_cycle_degrees [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) :
    (∑ i, G.degree (E.cycleEmb i)) = 12 + E.attachmentCount + 2 * addedCount E := by
  classical
  have hc (i : Fin 6) :
      (∑ j : Fin 6, if G.Adj (E.cycleEmb i) (E.cycleEmb j) then 1 else 0) = 2 := by
    simp_rw [E.cycle_induced]
    have hf : ∀ i : Fin 6,
        (∑ j : Fin 6, if (cycleGraph 6).Adj i j then 1 else 0) = 2 := by decide
    exact hf i
  have ha (j : Fin 6) (v : E.attach j) :
      (∑ i : Fin 6, if G.Adj (E.cycleEmb i) v.val then 1 else 0) = 1 := by
    simp_rw [G.adj_comm, E.trace j v.val v.property]
    simp
  have hb (j : E.Occupied) :
      (∑ i : Fin 6, if G.Adj (E.cycleEmb i) (E.occupiedVertex j) then 1 else 0) = 2 := by
    simp_rw [G.adj_comm, E.edge_adj j.val _ (E.occupiedVertex_spec j)]
    simp only [EmbeddingLike.apply_eq_iff_eq]
    have hf : ∀ j : Fin 6, (∑ i : Fin 6, if i = j ∨ i = j + 1 then 1 else 0) = 2 := by decide
    exact hf j.val
  simp_rw [E.degree_partition, hc]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hA : (∑ i : Fin 6, ∑ j : Fin 6, ∑ v : E.attach j,
      if G.Adj (E.cycleEmb i) v.val then 1 else 0) = E.attachmentCount := by
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    simp_rw [ha]
    simp [attachmentCount, Nat.card_eq_fintype_card]
  have hB : (∑ i : Fin 6, ∑ j : E.Occupied,
      if G.Adj (E.cycleEmb i) (E.occupiedVertex j) then 1 else 0) = 2 * addedCount E := by
    rw [Finset.sum_comm]
    simp_rw [hb]
    have ho := E.card_occupied
    simp only [Nat.card_eq_fintype_card] at ho
    simp [ho, Nat.mul_comm]
  rw [hA, hB]
  simp

 theorem edgeCount_eq [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) :
    edgeCount G = 6 + E.attachmentCount + 2 * addedCount E + matchingCount E := by
  classical
  have h := SimpleGraph.sum_degrees_eq_twice_card_edges (G := G)
  rw [E.sum_vertices, E.sum_cycle_degrees, E.sum_attachment_degrees] at h
  simp_rw [E.occupied_degree] at h
  have ho := E.card_occupied
  simp only [Nat.card_eq_fintype_card] at ho
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, ho] at h
  unfold edgeCount
  omega

theorem addedCount_eq_zero_iff (E : RadiusFourExtension G) :
    addedCount E = 0 ↔ ∀ i, E.edgeVert i = none := by
  classical
  simp only [addedCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    Finset.mem_univ, forall_const]
  constructor
  · intro h i
    cases he : E.edgeVert i with
    | none => rfl
    | some v => exact False.elim (h (x := i) (by simp [he]))
  · intro h i
    simp [h i]

 theorem no_triangle_of_counts_zero [Fintype V] [DecidableEq V]
    (E : RadiusFourExtension G) (hb : addedCount E = 0) (hm : matchingCount E = 0) :
    ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj a c := by
  have he := E.addedCount_eq_zero_iff.mp hb
  have ha := E.matchingCount_eq_zero_iff.mp hm
  have hattach (i : Fin 6) (v : V) (hv : v ∈ E.attach i) (w : V) (hvw : G.Adj v w) :
      w = E.cycleEmb i := by
    exact (E.no_extra_attach i v w hv hvw).resolve_right
      (fun hw => ha i v hv w hw hvw)
  have hv (v : V) : (∃ i, E.cycleEmb i = v) ∨ ∃ i, v ∈ E.attach i := by
    rcases E.exhaustive v with h | h | ⟨i, hi⟩
    · exact Or.inl h
    · exact Or.inr h
    · simp [he i] at hi
  intro a b c hab hbc hac
  rcases hv a with ⟨i, rfl⟩ | ⟨i, hi⟩
  · rcases hv b with ⟨j, rfl⟩ | ⟨j, hj⟩
    · rcases hv c with ⟨k, rfl⟩ | ⟨k, hk⟩
      · have hf : ∀ i j k : Fin 6, (cycleGraph 6).Adj i j →
            (cycleGraph 6).Adj j k → ¬ (cycleGraph 6).Adj i k := by decide
        exact hf i j k ((E.cycle_induced i j).mp hab)
          ((E.cycle_induced j k).mp hbc) ((E.cycle_induced i k).mp hac)
      · have h1 := hattach k c hk (E.cycleEmb i) hac.symm
        have h2 := hattach k c hk (E.cycleEmb j) hbc.symm
        exact hab.ne (h1.trans h2.symm)
    · have h1 := hattach j b hj (E.cycleEmb i) hab.symm
      have h2 := hattach j b hj c hbc
      exact hac.ne (h1.trans h2.symm)
  · have h1 := hattach i a hi b hab
    have h2 := hattach i a hi c hac
    exact hbc.ne (h1.trans h2.symm)

 theorem triangleCount_eq_zero_of_counts_zero [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (E : RadiusFourExtension G)
    (hb : addedCount E = 0) (hm : matchingCount E = 0) : triangleCount G = 0 := by
  classical
  rw [triangleCount, Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro s hs
  have hcl := G.mem_cliqueFinset_iff.mp hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcl.card_eq
  exact E.no_triangle_of_counts_zero hb hm a b c
    (hcl.isClique (by simp) (by simp) hab)
    (hcl.isClique (by simp) (by simp) hbc)
    (hcl.isClique (by simp) (by simp) hac)

 theorem mass_of_counts_zero [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) (hC : StrongC4Free G)
    (hb : addedCount E = 0) (hm : matchingCount E = 0) :
    neighbourhoodIndependenceSum G = 2 * Fintype.card V := by
  rw [strongC4Free_S_identity hC, E.triangleCount_eq_zero_of_counts_zero hb hm,
    E.edgeCount_eq, E.card_vertices, hb, hm]
  omega

/-- The remaining triangle count is the sole combinatorial input needed for the general mass. -/
theorem mass_of_triangleCount [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) (hC : StrongC4Free G)
    (hT : triangleCount G = addedCount E + matchingCount E) :
    neighbourhoodIndependenceSum G =
      2 * Fintype.card V - addedCount E - matchingCount E := by
  rw [strongC4Free_S_identity hC, E.edgeCount_eq, E.card_vertices, hT]
  have hbound := E.matching_vertices_bound
  omega

theorem mass_eq_full_iff_of_triangleCount [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (E : RadiusFourExtension G) (hC : StrongC4Free G)
    (hT : triangleCount G = addedCount E + matchingCount E) :
    neighbourhoodIndependenceSum G = 2 * Fintype.card V ↔
      addedCount E = 0 ∧ matchingCount E = 0 := by
  rw [E.mass_of_triangleCount hC hT]
  have hn := E.card_vertices
  constructor
  · intro h
    constructor <;> omega
  · rintro ⟨hb, hm⟩
    simp [hb, hm]

/-- In the zero-deficit construction every exterior vertex really is a pendant leaf. -/
theorem outside_is_leaf_of_counts_zero [Fintype V] [DecidableEq V]
    (E : RadiusFourExtension G) (hb : addedCount E = 0) (hm : matchingCount E = 0)
    (v : V) (hv : ∀ i, E.cycleEmb i ≠ v) :
    ∃ i, v ∈ E.attach i ∧ ∀ w, G.Adj v w ↔ w = E.cycleEmb i := by
  rcases E.exhaustive v with ⟨i, hi⟩ | ⟨i, hi⟩ | ⟨i, hi⟩
  · exact (hv i hi).elim
  · refine ⟨i, hi, fun w => ⟨?_, ?_⟩⟩
    · intro hw
      exact (E.no_extra_attach i v w hi hw).resolve_right
        (fun hw' => E.matchingCount_eq_zero_iff.mp hm i v hi w hw' hw)
    · rintro rfl
      exact (E.trace i v hi i).mpr rfl
  · have hn := E.addedCount_eq_zero_iff.mp hb i
    simp [hn] at hi

theorem triangle_with_attachment [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) (s : Finset V) (hs : s ∈ G.cliqueFinset 3)
    (i : Fin 6) (v : V) (hv : v ∈ E.attach i) (hvs : v ∈ s) :
    ∃ w ∈ E.attach i, G.Adj v w ∧ s = {E.cycleEmb i, v, w} := by
  classical
  have hc := G.mem_cliqueFinset_iff.mp hs
  have her : (s.erase v).card = 2 := by rw [Finset.card_erase_of_mem hvs, hc.card_eq]
  obtain ⟨a, b, hab, her⟩ := Finset.card_eq_two.mp her
  have hav : a ≠ v := by
    have : a ∈ s.erase v := by simp [her]
    exact (Finset.mem_erase.mp this).1
  have hbv : b ≠ v := by
    have : b ∈ s.erase v := by simp [her]
    exact (Finset.mem_erase.mp this).1
  have has : a ∈ s := (Finset.mem_erase.mp (by simp [her] : a ∈ s.erase v)).2
  have hbs : b ∈ s := (Finset.mem_erase.mp (by simp [her] : b ∈ s.erase v)).2
  have hva := hc.isClique hvs has hav.symm
  have hvb := hc.isClique hvs hbs hbv.symm
  have hshape : s = {v, a, b} := by
    rw [← Finset.insert_erase hvs, her]
  rcases E.no_extra_attach i v a hv hva with ha | ha <;>
    rcases E.no_extra_attach i v b hv hvb with hb | hb
  · exact (hab (ha.trans hb.symm)).elim
  · refine ⟨b, hb, hvb, ?_⟩
    rw [hshape, ha]
    ext x
    simp [or_comm, or_left_comm, or_assoc]
  · refine ⟨a, ha, hva, ?_⟩
    rw [hshape, hb]
    ext x
    simp [or_comm, or_left_comm, or_assoc]
  · exact (hab (E.matching i v hv b hb hvb a ha hva)).elim

 theorem triangle_with_occupied [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) (s : Finset V) (hs : s ∈ G.cliqueFinset 3)
    (i : E.Occupied) (hvs : E.occupiedVertex i ∈ s) :
    s = {E.occupiedVertex i, E.cycleEmb i.val, E.cycleEmb (i.val + 1)} := by
  classical
  have hc := G.mem_cliqueFinset_iff.mp hs
  have her : (s.erase (E.occupiedVertex i)).card = 2 := by
    rw [Finset.card_erase_of_mem hvs, hc.card_eq]
  obtain ⟨a, b, hab, her⟩ := Finset.card_eq_two.mp her
  have ha := Finset.mem_erase.mp (show a ∈ s.erase (E.occupiedVertex i) by simp [her])
  have hb := Finset.mem_erase.mp (show b ∈ s.erase (E.occupiedVertex i) by simp [her])
  have hva := hc.isClique hvs ha.2 ha.1.symm
  have hvb := hc.isClique hvs hb.2 hb.1.symm
  have hshape : s = {E.occupiedVertex i, a, b} := by
    rw [← Finset.insert_erase hvs, her]
  rcases (E.edge_adj i.val _ (E.occupiedVertex_spec i) a).mp hva with h1 | h1 <;>
    rcases (E.edge_adj i.val _ (E.occupiedVertex_spec i) b).mp hvb with h2 | h2
  · exact (hab (h1.trans h2.symm)).elim
  · rw [hshape, h1, h2]
  · rw [hshape, h1, h2]
    ext x
    simp [or_comm, or_left_comm, or_assoc]
  · exact (hab (h1.trans h2.symm)).elim

theorem triangle_normal_form [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) (s : Finset V) (hs : s ∈ G.cliqueFinset 3) :
    (∃ i, ∃ v ∈ E.attach i, ∃ w ∈ E.attach i,
      G.Adj v w ∧ s = {E.cycleEmb i, v, w}) ∨
    (∃ i : E.Occupied,
      s = {E.occupiedVertex i, E.cycleEmb i.val, E.cycleEmb (i.val + 1)}) := by
  classical
  by_cases ha : ∃ i, ∃ v ∈ E.attach i, v ∈ s
  · obtain ⟨i, v, hv, hvs⟩ := ha
    obtain ⟨w, hw, hadj, hshape⟩ := E.triangle_with_attachment s hs i v hv hvs
    exact Or.inl ⟨i, v, hv, w, hw, hadj, hshape⟩
  · by_cases hb : ∃ i : E.Occupied, E.occupiedVertex i ∈ s
    · obtain ⟨i, hi⟩ := hb
      exact Or.inr ⟨i, E.triangle_with_occupied s hs i hi⟩
    · have hc := G.mem_cliqueFinset_iff.mp hs
      have hv (v : V) (hvs : v ∈ s) : ∃ i, E.cycleEmb i = v := by
        rcases E.exhaustive v with h | ⟨i, hi⟩ | ⟨i, hi⟩
        · exact h
        · exact (ha ⟨i, v, hi, hvs⟩).elim
        · have his : (E.edgeVert i).isSome := by simp [hi]
          have heq : E.occupiedVertex ⟨i, his⟩ = v :=
            Option.some.inj ((E.occupiedVertex_spec ⟨i, his⟩).symm.trans hi)
          exact (hb ⟨⟨i, his⟩, heq.symm ▸ hvs⟩).elim
      obtain ⟨a, b, c, hab, hac, hbc, hshape⟩ := Finset.card_eq_three.mp hc.card_eq
      have has : a ∈ s := by simp [hshape]
      have hbs : b ∈ s := by simp [hshape]
      have hcs : c ∈ s := by simp [hshape]
      obtain ⟨i, rfl⟩ := hv a has
      obtain ⟨j, rfl⟩ := hv b hbs
      obtain ⟨k, rfl⟩ := hv c hcs
      have hf : ∀ i j k : Fin 6, (cycleGraph 6).Adj i j →
          (cycleGraph 6).Adj j k → ¬ (cycleGraph 6).Adj i k := by decide
      exact (hf i j k
        ((E.cycle_induced i j).mp (hc.isClique has hbs hab))
        ((E.cycle_induced j k).mp (hc.isClique hbs hcs hbc))
        ((E.cycle_induced i k).mp (hc.isClique has hcs hac))).elim

abbrev MatchingEdge [Fintype V] [DecidableEq V] (E : RadiusFourExtension G) :=
  Σ i : Fin 6, {e : Sym2 (E.attach i) // e ∈ (G.induce (E.attach i)).edgeSet}

noncomputable def matchingTriangle [Fintype V] [DecidableEq V]
    (E : RadiusFourExtension G) (e : E.MatchingEdge) : Finset V :=
  {E.cycleEmb e.1, e.2.val.out.1.val, e.2.val.out.2.val}

 theorem matchingTriangle_mem [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) (e : E.MatchingEdge) :
    E.matchingTriangle e ∈ G.cliqueFinset 3 := by
  classical
  let a := e.2.val.out.1
  let b := e.2.val.out.2
  have hadj : G.Adj a.val b.val := by
    have he : e.2.val ∈ (G.induce (E.attach e.1)).edgeFinset := by
      simpa only [SimpleGraph.mem_edgeFinset] using e.2.property
    exact adj_out_of_mem _ _ he
  have hca := (E.trace e.1 a.val a.property e.1).mpr rfl
  have hcb := (E.trace e.1 b.val b.property e.1).mpr rfl
  apply G.mem_cliqueFinset_iff.mpr
  constructor
  · rw [SimpleGraph.isClique_iff]
    intro x hx y hy hxy
    change x ∈ ({E.cycleEmb e.1, a.val, b.val} : Finset V) at hx
    change y ∈ ({E.cycleEmb e.1, a.val, b.val} : Finset V) at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact (hxy rfl).elim
    · exact hca.symm
    · exact hcb.symm
    · exact hca
    · exact (hxy rfl).elim
    · exact hadj
    · exact hcb
    · exact hadj.symm
    · exact (hxy rfl).elim
  · apply Finset.card_eq_three.mpr
    exact ⟨_, _, _, E.attach_off_cycle e.1 a.val a.property e.1,
      E.attach_off_cycle e.1 b.val b.property e.1, hadj.ne, rfl⟩

 theorem matchingTriangle_cycle_mem_iff [Fintype V] [DecidableEq V]
    (E : RadiusFourExtension G) (e : E.MatchingEdge) (i : Fin 6) :
    E.cycleEmb i ∈ E.matchingTriangle e ↔ i = e.1 := by
  classical
  simp only [matchingTriangle, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h | h)
    · exact E.cycleEmb.injective h
    · exact (E.attach_off_cycle e.1 _ e.2.val.out.1.property i h).elim
    · exact (E.attach_off_cycle e.1 _ e.2.val.out.2.property i h).elim
  · rintro rfl
    exact Or.inl rfl

 theorem matchingTriangle_injective [Fintype V] [DecidableEq V]
    (E : RadiusFourExtension G) : Function.Injective E.matchingTriangle := by
  classical
  rintro ⟨i, e⟩ ⟨j, f⟩ h
  have hij : i = j := by
    apply (E.matchingTriangle_cycle_mem_iff ⟨j, f⟩ i).mp
    rw [← h]
    exact (E.matchingTriangle_cycle_mem_iff ⟨i, e⟩ i).mpr rfl
  subst j
  apply congrArg (fun z => (⟨i, z⟩ : E.MatchingEdge))
  apply Subtype.ext
  have her : ({e.val.out.1.val, e.val.out.2.val} : Finset V) =
      {f.val.out.1.val, f.val.out.2.val} := by
    have := congrArg (fun s : Finset V => s.erase (E.cycleEmb i)) h
    simpa [matchingTriangle,
      E.attach_off_cycle i _ e.val.out.1.property i,
      E.attach_off_cycle i _ e.val.out.2.property i,
      E.attach_off_cycle i _ f.val.out.1.property i,
      E.attach_off_cycle i _ f.val.out.2.property i] using this
  have hout : e.val.out.1.val = f.val.out.1.val ∨ e.val.out.1.val = f.val.out.2.val := by
    have : e.val.out.1.val ∈ ({f.val.out.1.val, f.val.out.2.val} : Finset V) := by
      rw [← her]; simp
    simpa using this
  have hne : e.val.out.1 ≠ e.val.out.2 :=
    (adj_out_of_mem _ _ ((G.induce (E.attach i)).mem_edgeFinset.mpr e.property)).ne
  have hne' : f.val.out.1 ≠ f.val.out.2 :=
    (adj_out_of_mem _ _ ((G.induce (E.attach i)).mem_edgeFinset.mpr f.property)).ne
  rw [← Sym2.mk_fst_out_snd_out e.val, ← Sym2.mk_fst_out_snd_out f.val]
  rcases hout with hh | hh
  · have hh' : e.val.out.2.val = f.val.out.2.val := by
      have hm : f.val.out.2.val ∈ ({e.val.out.1.val, e.val.out.2.val} : Finset V) := by
        rw [her]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      exact (hm.resolve_left (fun h => hne' (Subtype.ext (hh.symm.trans h.symm)))).symm
    rw [Subtype.ext hh, Subtype.ext hh']
  · have hh' : e.val.out.2.val = f.val.out.1.val := by
      have hm : f.val.out.1.val ∈ ({e.val.out.1.val, e.val.out.2.val} : Finset V) := by
        rw [her]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      exact (hm.resolve_left (fun h => hne' (Subtype.ext (h.trans hh)))).symm
    rw [Subtype.ext hh, Subtype.ext hh']
    exact Sym2.eq_swap

noncomputable def occupiedTriangle [DecidableEq V] (E : RadiusFourExtension G) (i : E.Occupied) : Finset V :=
  {E.occupiedVertex i, E.cycleEmb i.val, E.cycleEmb (i.val + 1)}

 theorem occupiedTriangle_mem [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) (i : E.Occupied) :
    E.occupiedTriangle i ∈ G.cliqueFinset 3 := by
  classical
  have h1 := (E.edge_adj i.val _ (E.occupiedVertex_spec i) (E.cycleEmb i.val)).mpr (Or.inl rfl)
  have h2 := (E.edge_adj i.val _ (E.occupiedVertex_spec i) (E.cycleEmb (i.val + 1))).mpr (Or.inr rfl)
  have h3 : G.Adj (E.cycleEmb i.val) (E.cycleEmb (i.val + 1)) := by
    rw [E.cycle_induced, cycleGraph_adj']
    exact Or.inr (by simp)
  apply G.mem_cliqueFinset_iff.mpr
  constructor
  · rw [SimpleGraph.isClique_iff]
    intro x hx y hy hxy
    change x ∈ ({E.occupiedVertex i, E.cycleEmb i.val, E.cycleEmb (i.val + 1)} : Finset V) at hx
    change y ∈ ({E.occupiedVertex i, E.cycleEmb i.val, E.cycleEmb (i.val + 1)} : Finset V) at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
    · exact (hxy rfl).elim
    · exact h1
    · exact h2
    · exact h1.symm
    · exact (hxy rfl).elim
    · exact h3
    · exact h2.symm
    · exact h3.symm
    · exact (hxy rfl).elim
  · exact Finset.card_eq_three.mpr ⟨_, _, _, h1.ne, h2.ne, h3.ne, rfl⟩

 theorem occupiedTriangle_injective [DecidableEq V] (E : RadiusFourExtension G) :
    Function.Injective E.occupiedTriangle := by
  classical
  intro i j h
  have hv : E.occupiedVertex i ∈ E.occupiedTriangle j := by rw [← h]; simp [occupiedTriangle]
  simp only [occupiedTriangle, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv | hv
  · exact Subtype.ext (E.edge_inj i.val j.val _ (E.occupiedVertex_spec i)
      (hv.symm ▸ E.occupiedVertex_spec j))
  · exact (E.edge_off_cycle i.val _ (E.occupiedVertex_spec i) j.val hv.symm).elim
  · exact (E.edge_off_cycle i.val _ (E.occupiedVertex_spec i) (j.val + 1) hv.symm).elim

 theorem matchingTriangle_ne_occupiedTriangle [Fintype V] [DecidableEq V]
    (E : RadiusFourExtension G) (e : E.MatchingEdge) (i : E.Occupied) :
    E.matchingTriangle e ≠ E.occupiedTriangle i := by
  classical
  intro h
  have hv : E.occupiedVertex i ∈ E.matchingTriangle e := by rw [h]; simp [occupiedTriangle]
  simp only [matchingTriangle, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | hv | hv
  · exact E.edge_off_cycle i.val _ (E.occupiedVertex_spec i) e.1 hv.symm
  · exact E.edge_off_attach i.val _ e.1 _ (E.occupiedVertex_spec i) e.2.val.out.1.property hv
  · exact E.edge_off_attach i.val _ e.1 _ (E.occupiedVertex_spec i) e.2.val.out.2.property hv

theorem triangleCount_eq [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) : triangleCount G = addedCount E + matchingCount E := by
  classical
  let f : E.MatchingEdge ⊕ E.Occupied → {s : Finset V // s ∈ G.cliqueFinset 3} :=
    Sum.elim (fun e => ⟨E.matchingTriangle e, E.matchingTriangle_mem e⟩)
      (fun i => ⟨E.occupiedTriangle i, E.occupiedTriangle_mem i⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have hval := congrArg Subtype.val h
      cases x with
      | inl e =>
        cases y with
        | inl e' => exact congrArg Sum.inl (E.matchingTriangle_injective hval)
        | inr i => exact (E.matchingTriangle_ne_occupiedTriangle e i hval).elim
      | inr i =>
        cases y with
        | inl e => exact (E.matchingTriangle_ne_occupiedTriangle e i hval.symm).elim
        | inr j => exact congrArg Sum.inr (E.occupiedTriangle_injective hval)
    · intro ⟨s, hs⟩
      rcases E.triangle_normal_form s hs with ⟨i, v, hv, w, hw, hadj, hshape⟩ | ⟨i, hshape⟩
      · let e : Sym2 (E.attach i) := s(⟨v, hv⟩, ⟨w, hw⟩)
        have he : e ∈ (G.induce (E.attach i)).edgeSet := hadj
        refine ⟨Sum.inl ⟨i, ⟨e, he⟩⟩, Subtype.ext ?_⟩
        change E.matchingTriangle ⟨i, ⟨e, he⟩⟩ = s
        have hout := congrArg (fun t : Sym2 (E.attach i) =>
          t.toFinset.image Subtype.val) (Sym2.mk_fst_out_snd_out e)
        change ((s(e.out.1, e.out.2)).toFinset.image Subtype.val) =
          ((s(⟨v, hv⟩, ⟨w, hw⟩)).toFinset.image Subtype.val) at hout
        simp only [Sym2.toFinset_mk_eq, Finset.image_insert, Finset.image_singleton] at hout
        change insert (E.cycleEmb i) {e.out.1.val, e.out.2.val} = s
        rw [hout, hshape]
      · exact ⟨Sum.inr i, Subtype.ext hshape.symm⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective f hf)
  have hecard : Fintype.card E.MatchingEdge = matchingCount E := by
    simp only [MatchingEdge, Fintype.card_sigma, matchingCount, edgeCount]
    apply Finset.sum_congr rfl
    intro i _
    have hc := (G.induce (E.attach i)).card_edgeSet
    convert hc using 1
    exact congrArg Finset.card (by ext e; simp)
  have hocard : Fintype.card E.Occupied = addedCount E := by
    simpa only [Nat.card_eq_fintype_card] using E.card_occupied
  simpa only [Fintype.card_sum, Fintype.card_coe, hecard, hocard, triangleCount,
    Nat.add_comm] using hcard.symm

 theorem mass [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) (hC : StrongC4Free G) :
    neighbourhoodIndependenceSum G =
      2 * Fintype.card V - addedCount E - matchingCount E :=
  E.mass_of_triangleCount hC E.triangleCount_eq

 theorem mass_eq_full_iff [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (E : RadiusFourExtension G) (hC : StrongC4Free G) :
    neighbourhoodIndependenceSum G = 2 * Fintype.card V ↔
      addedCount E = 0 ∧ matchingCount E = 0 :=
  E.mass_eq_full_iff_of_triangleCount hC E.triangleCount_eq

end RadiusFourExtension

end InducedPaths
