/- Assembly interfaces for Theorem 5.7, independent of StatementsCore. -/
module
public import InducedPaths.OneTriangleMass
public import InducedPaths.CutSideReduction
public import InducedPaths.ChenXuCore
public import InducedPaths.ChenXuAttachmentBounds
public import InducedPaths.TriangleFreeMass
open Finset SimpleGraph
@[expose] public section
set_option maxHeartbeats 4000000
namespace InducedPaths
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Triangle counts cannot increase when vertices are deleted. -/
theorem oneTriangle_triangleCount_induce_le [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (X : Set V) [DecidablePred (· ∈ X)] :
    triangleCount (G.induce X) ≤ triangleCount G := by
  classical
  let e : X ↪ V := Function.Embedding.subtype _
  apply Finset.card_le_card_of_injOn (fun s => s.map e)
  · intro s hs
    have hcl := mem_cliqueFinset_iff.mp hs
    apply mem_cliqueFinset_iff.mpr
    refine ⟨?_, by simpa using hcl.card_eq⟩
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_map.mp hy
    exact hcl.isClique ha hb (fun h => hxy (congrArg e h))
  · intro s hs t ht hst
    exact Finset.map_injective e hst

/-- Triangle-free is equivalent to zero triangle count on a finite graph. -/
theorem oneTriangle_cliqueFree_iff_triangleCount_zero [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] : G.CliqueFree 3 ↔ triangleCount G = 0 := by
  rw [triangleCount, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  simp only [mem_cliqueFinset_iff, CliqueFree]

/-- Heredity of induced-path exclusion, kept local to avoid a StatementsCore
 dependency. -/
theorem oneTriangle_isPkFree_induce {k : ℕ} (hp : IsPkFree G k) (X : Set V) :
    IsPkFree (G.induce X) k := by
  intro h
  exact hp (h.trans ⟨Embedding.induce X⟩)

/-- Moving a core of the deletion graph back into the ambient vertex type.
The resulting ambient core excludes the deleted vertex by construction. -/
def oneTriangleAmbientCore (v : V) (Q : Set ({v}ᶜ : Set V)) : Set V :=
  {x | ∃ hx : x ∈ ({v}ᶜ : Set V), (⟨x, hx⟩ : ({v}ᶜ : Set V)) ∈ Q}

theorem oneTriangle_not_mem_ambientCore (v : V) (Q : Set ({v}ᶜ : Set V)) :
    v ∉ oneTriangleAmbientCore v Q := by
  rintro ⟨hx, _⟩
  exact hx rfl

/-- Removing the subtype nesting does not alter the core graph. -/
noncomputable def oneTriangleAmbientCoreIso (v : V) (Q : Set ({v}ᶜ : Set V)) :
    ((G.induce ({v}ᶜ : Set V)).induce Q) ≃g
      G.induce (oneTriangleAmbientCore v Q) where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.choose⟩, x.property.choose_spec⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Discharging all classification-dependent inequalities for an ambient
core, leaving only the literal tree-stripping data. -/
theorem oneTriangle_mass_of_small_core [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hC : StrongC4Free G) (hT : triangleCount G ≤ 1)
    {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hdu : G.degree v ≤ G.degree u) (hdw : G.degree v ≤ G.degree w)
    (Q : Finset V) (hvQ : v ∉ Q)
    (hclass : ChenXuSmallCore (G.induce (Q : Set V)))
    (hbound : 2 * edgeCount (G.induce (Q : Set V)) ≤ 3 * Q.card)
    (hstrip : edgeCount (G.induce {v}ᶜ) = edgeCount (G.induce (Q : Set V)) +
      (Fintype.card V - 1 - Q.card))
    (hattach : ∀ x, x ≠ v → x ∉ Q →
      (oneTriangleCoreNeighbors G Q x).card ≤ 1) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V := by
  classical
  let eta := 3 * Q.card - 2 * edgeCount (G.induce (Q : Set V))
  let a := (oneTriangleCoreNeighbors G Q v).card
  let A := oneTriangleSelected (G := G) Q v
  have hA : ChenXuAttachmentDisjoint (G.induce (Q : Set V)) A := by
    intro x hx y hy hxy z hbad
    have hvx : G.Adj v x := by simpa [A, oneTriangleSelected] using hx
    have hvy : G.Adj v y := by simpa [A, oneTriangleSelected] using hy
    have hd := oneTriangle_core_neighborSets_disjoint hC (Q : Set V) hvQ hvx hvy hxy
    exact Set.disjoint_left.mp hd hbad.1 hbad.2
  have hcard : Fintype.card V = Q.card + (Fintype.card V - 1 - Q.card) + 1 := by
    have hlt : Q.card < Fintype.card V := by
      have hsub : Q ⊂ univ := Finset.ssubset_iff_subset_ne.mpr
        ⟨subset_univ _, fun h => hvQ (h.symm ▸ mem_univ v)⟩
      simpa using Finset.card_lt_card hsub
    omega
  have hO : (univ \ insert v Q).card = Fintype.card V - 1 - Q.card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_insert_of_notMem hvQ]
    omega
  have hpart := oneTriangle_attachment_partition (G := G) Q v
  rw [hO] at hpart
  apply oneTriangle_mass_of_core_data hC hT hvu hvw huw hdu hdw Q
    (edgeCount (G.induce (Q : Set V))) eta (Fintype.card V - 1 - Q.card) a
    hstrip (by dsimp [eta]; omega) hcard hpart
  · have h := chenXu_core_attachment_card hclass A hA
    rw [oneTriangleSelected_card] at h
    simpa only [Fintype.card_coe] using (show a ≤ eta + 3 by
      dsimp [a, eta] at *; simp only [Fintype.card_coe] at h; omega)
  · intro x hx y hy hvx hvy hxy
    have hxA : (⟨x, hx⟩ : (Q : Set V)) ∈ A := by simp [A, oneTriangleSelected, hvx]
    have hyA : (⟨y, hy⟩ : (Q : Set V)) ∈ A := by simp [A, oneTriangleSelected, hvy]
    have h := chenXu_core_attachment_edge hclass A hA hxA hyA hxy
    rw [oneTriangleSelected_card, oneTriangle_core_degree, oneTriangle_core_degree] at h
    have hqc : Fintype.card (Q : Set V) = Q.card := by simp
    dsimp [a, eta]
    rw [hqc] at h
    exact h
  · exact hattach

/-- The no-cut case of Theorem 5.7, with no remaining classification or
mass assumptions. -/
theorem oneTriangle_mass_noCut [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hc : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 7)
    (hT : triangleCount G ≤ 1) (hpos : triangleCount G ≠ 0)
    (hcut : ∀ s, ¬ IsCutVertex G s) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V := by
  classical
  obtain ⟨v, u, w, hvu, hvw, huw, hdu, hdw⟩ := oneTriangle_exists_min_degree hpos
  let H := G.induce ({v}ᶜ : Set V)
  have hhc : H.Connected := by
    have hpre := hcut v
    simp only [IsCutVertex, not_not] at hpre
    haveI : Nonempty ({v}ᶜ : Set V) := ⟨⟨u, hvu.ne.symm⟩⟩
    exact ⟨hpre⟩
  have hht : H.CliqueFree 3 := oneTriangle_cliqueFree_iff_triangleCount_zero.mpr
    (oneTriangle_delete_triangleCount hT hvu hvw huw)
  obtain ⟨R, hR, hs, hrc, hrt, hrC, hrp, hrcl, hrclass, hre, hdef⟩ :=
    chenXu_tree_core_stripping hhc hht (strongC4Free_induce hC)
      (oneTriangle_isPkFree_induce hp _)
  let Q : Finset V := (oneTriangleAmbientCore v R).toFinset
  have hQset : (Q : Set V) = oneTriangleAmbientCore v R := by simp [Q]
  let e : (H.induce R) ≃g G.induce (Q : Set V) :=
    { toFun := fun x => ⟨x.val.val, by simpa [Q] using
        (show x.val.val ∈ oneTriangleAmbientCore v R from ⟨x.val.property, x.property⟩)⟩
      invFun := fun x => ⟨⟨x.val, (show x.val ∈ oneTriangleAmbientCore v R by simpa [Q] using x.property).choose⟩,
        (show x.val ∈ oneTriangleAmbientCore v R by simpa [Q] using x.property).choose_spec⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have hcard : Nat.card R = Q.card := by
    have h := Nat.card_congr e.toEquiv
    have hh : Nat.card (Q : Set V) = Q.card := by simp only [Nat.card_eq_fintype_card]; simp
    exact h.trans hh
  have he : edgeCount (H.induce R) = edgeCount (G.induce (Q : Set V)) := by
    exact chenXu_edgeCount_iso e
  have hclass : ChenXuSmallCore (G.induce (Q : Set V)) := by
    rcases hrclass with h1 | h2 | hf
    · exact Or.inl (h1.map fun f => e.symm.trans f)
    · exact Or.inr (Or.inl (h2.map fun f => e.symm.trans f))
    · apply Or.inr; apply Or.inr
      unfold InChenXuFamily at hf ⊢
      rcases hf with h | h | h | h | h | h | h | h | h | h | h | h | h | h
      all_goals first
      | obtain ⟨f⟩ := h; have hh := Nonempty.intro (e.symm.trans f); tauto
      | obtain ⟨t, ht, ⟨f⟩⟩ := h; have hh := Nonempty.intro (e.symm.trans f); aesop

  have hbound : 2 * edgeCount (G.induce (Q : Set V)) ≤ 3 * Q.card := by
    rcases hrclass with h1 | h2 | hf
    · obtain ⟨f⟩ := h1
      have hn := Fintype.card_congr f.toEquiv
      have hh := chenXu_edgeCount_iso f
      have hz : edgeCount (completeGraph (Fin 1)) = 0 := by decide
      simp only [Fintype.card_fin] at hn
      rw [he, hz] at hh
      simp only [Nat.card_eq_fintype_card] at hcard
      omega
    · obtain ⟨f⟩ := h2
      have hn := Fintype.card_congr f.toEquiv
      have hh := chenXu_edgeCount_iso f
      have hz : edgeCount k2Graph = 1 := by decide
      simp only [Fintype.card_fin] at hn
      rw [he, hz] at hh
      simp only [Nat.card_eq_fintype_card] at hcard
      omega
    · have hh := chenXu_family_edge_bound hf
      rw [he] at hh
      have hh' : 2 * edgeCount (G.induce (Q : Set V)) ≤ 3 * Nat.card R := by
        simpa only [Nat.card_eq_fintype_card] using hh
      omega
  apply oneTriangle_mass_of_small_core hC hT hvu hvw huw hdu hdw Q
    (by simpa [Q] using oneTriangle_not_mem_ambientCore v R) hclass hbound
  · have hn : Fintype.card ({v}ᶜ : Set V) = Fintype.card V - 1 := by
      have hh := Fintype.card_subtype_compl (fun x : V => x = v)
      have hsing : Fintype.card {x : V // x = v} = 1 := by simp
      change Fintype.card {x : V // ¬x = v} = _
      omega
    simpa only [H, he, hcard, hn] using hre
  · intro x hxv hxQ
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have hx : x ∈ ({v}ᶜ : Set V) := hxv
    have hxR : (⟨x, hx⟩ : ({v}ᶜ : Set V)) ∉ R := by
      intro hr
      exact hxQ (by simpa [Q] using
        (show x ∈ oneTriangleAmbientCore v R from ⟨hx, hr⟩))
    have hsingle := hs.outside_neighbors ⟨x, hx⟩ (Set.mem_univ _) hxR
    have hmem {z : V} (hz : z ∈ oneTriangleCoreNeighbors G Q x) :
        ∃ hzv : z ∈ ({v}ᶜ : Set V), (⟨z, hzv⟩ : ({v}ᶜ : Set V)) ∈ R ∧ G.Adj x z := by
      have hh : G.Adj x z ∧ z ∈ Q := by
        simpa only [oneTriangleCoreNeighbors, mem_inter, mem_neighborFinset] using hz
      obtain ⟨hzv, hzR⟩ := (show z ∈ oneTriangleAmbientCore v R by simpa [Q] using hh.2)
      exact ⟨hzv, hzR, hh.1⟩
    obtain ⟨hav, haR, hxa⟩ := hmem ha
    obtain ⟨hbv, hbR, hxb⟩ := hmem hb
    exact congrArg Subtype.val (hsingle ⟨haR, hxa⟩ ⟨hbR, hxb⟩)

/-- Full cut-side induction for Theorem 5.7. The only unassembled inputs
are the triangle-free base case, the rooted mass estimate (Lemma 5.3), and
the no-cut one-triangle core argument. None is the cyclic global GenK bound. -/
theorem oneTriangle_mass_by_cut_induction
    (htf : ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], H.Connected → StrongC4Free H → IsPkFree H 7 →
      H.CliqueFree 3 → neighbourhoodIndependenceSum H ≤ 3 * Fintype.card W)
    (hroot : ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj] (s : W), H.Connected → StrongC4Free H → RootedNoP4 H s →
      neighbourhoodIndependenceSum H ≤ 2 * (Fintype.card W - 1))
    (hcore : ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj], H.Connected → StrongC4Free H → IsPkFree H 7 →
      triangleCount H ≤ 1 → triangleCount H ≠ 0 → (∀ s, ¬ IsCutVertex H s) →
      neighbourhoodIndependenceSum H ≤ 3 * Fintype.card W)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hc : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 7)
    (hT : triangleCount G ≤ 1) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V := by
  classical
  have main : ∀ n, ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj], Fintype.card W = n →
      H.Connected → StrongC4Free H → IsPkFree H 7 → triangleCount H ≤ 1 →
      neighbourhoodIndependenceSum H ≤ 3 * Fintype.card W := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W iF iE H iA hn hc hC hp hT
      letI : DecidableEq W := iE
      letI : DecidableRel H.Adj := iA
      by_cases hzero : triangleCount H = 0
      · exact htf H hc hC hp (oneTriangle_cliqueFree_iff_triangleCount_zero.mpr hzero)
      by_cases hcut : ∃ s, IsCutVertex H s
      · obtain ⟨s, hs⟩ := hcut
        obtain ⟨D⟩ := exists_rootedCutSide hp hs
        have hleft := hroot (H.induce (insert s D.left : Set W)) ⟨s, by simp⟩
          (D.toCutPartition.connected_left hc) (strongC4Free_induce hC) D.rooted_no_P4
        have hsmall : Fintype.card (insert s D.right : Set W) < n := by
          have h := D.toCutPartition.right_smaller
          rw [← hn]
          convert h using 1 <;> simp only [Fintype.card_eq_nat_card]
        have hsub : triangleCount (H.induce (insert s D.right : Set W)) ≤ 1 := by
          convert (oneTriangle_triangleCount_induce_le (G := H)
            (insert s D.right : Set W)).trans hT using 1
          unfold triangleCount
          congr 1
          ext z
          simp only [mem_cliqueFinset_iff]
        have hright := ih (Fintype.card (insert s D.right : Set W)) hsmall
          (H.induce (insert s D.right : Set W)) rfl
          (D.toCutPartition.connected_right hc) (strongC4Free_induce hC)
          (oneTriangle_isPkFree_induce hp _) hsub
        have hstrict := cut_strict_mass_of_rooted_bound D hleft hright
        exact hstrict.le
      · exact hcore H hc hC hp hT hzero (by simpa only [not_exists] using hcut)
  exact main (Fintype.card V) G rfl hc hC hp hT

/-- Exact Theorem 5.7, parameterized only by the already-proved Lemma 5.3
rooted estimate so that this module stays upstream of StatementsCore. -/
theorem oneTriangle_mass_bound_of_rooted
    (hroot : ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
      [DecidableRel H.Adj] (s : W), H.Connected → StrongC4Free H → RootedNoP4 H s →
      neighbourhoodIndependenceSum H ≤ 2 * (Fintype.card W - 1))
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hc : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 7)
    (hT : triangleCount G ≤ 1) :
    neighbourhoodIndependenceSum G ≤ 3 * Fintype.card V := by
  apply oneTriangle_mass_by_cut_induction (htf := ?_) (hroot := hroot) (hcore := ?_) hc hC hp hT
  · intro W _ _ H _ hc hC hp htri
    exact (triangleFree_mass_bound hc htri hC hp).1
  · intro W _ _ H _ hc hC hp hT hpos hcut
    exact oneTriangle_mass_noCut hc hC hp hT hpos hcut

end InducedPaths
