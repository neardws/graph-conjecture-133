/- Equality structure in the one-triangle case, upstream of StatementsCore. -/
module
public import InducedPaths.OneTriangleAssembly
public import InducedPaths.SectionFiveGlobal
public import InducedPaths.PetersenTriangleEmbedding
open Finset SimpleGraph
@[expose] public section
set_option maxHeartbeats 4000000
namespace InducedPaths
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Equality in the one-triangle estimate forces the triangle edge into the
core and saturates the sharp attachment edge inequality. This statement
separates the structural equality information from its later Petersen endgame. -/
theorem oneTriangle_equality_core_slack
    (hC : StrongC4Free G) (hT : triangleCount G ≤ 1)
    {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hdu : G.degree v ≤ G.degree u) (hdw : G.degree v ≤ G.degree w)
    (Q : Finset V) (eQ eta t a : ℕ)
    (hstrip : edgeCount (G.induce {v}ᶜ) = eQ + t)
    (hdef : 2 * eQ + eta = 3 * Q.card)
    (hn : Fintype.card V = Q.card + t + 1)
    (ht : t + a = G.degree v + (oneTriangleRemainder G Q v).card)
    (hcore : a ≤ eta + 2)
    (hedge : ∀ x ∈ Q, ∀ y ∈ Q, G.Adj v x → G.Adj v y → G.Adj x y →
      a + min (oneTriangleCoreNeighbors G Q x).card
        (oneTriangleCoreNeighbors G Q y).card ≤ eta + 5)
    (hattach : ∀ x, x ≠ v → x ∉ Q →
      (oneTriangleCoreNeighbors G Q x).card ≤ 1)
    (heq : neighbourhoodIndependenceSum G = 3 * Fintype.card V) :
    u ∈ Q ∧ w ∈ Q ∧
      G.degree v = 1 + (oneTriangleRemainder G Q v).card +
        min (oneTriangleCoreNeighbors G Q u).card (oneTriangleCoreNeighbors G Q w).card ∧
      a + min (oneTriangleCoreNeighbors G Q u).card
        (oneTriangleCoreNeighbors G Q w).card = eta + 5 := by
  have htv := oneTriangle_trianglesAt_eq_one hT hvu hvw huw
  have htle : trianglesAt G v ≤ triangleCount G :=
    Finset.card_le_card (filter_subset _ _)
  have hTeq : triangleCount G = 1 := by omega
  have hSi := strongC4Free_S_identity hC
  have hlow := three_mul_triangleCount_le_two_edge hC
  have hS : neighbourhoodIndependenceSum G + 3 = 2 * edgeCount G := by
    rw [hTeq] at hSi hlow
    omega
  have he := edgeCount_induce_compl_add (G := G) v
  have huQ : u ∈ Q := by
    by_contra huQ
    have hu := oneTriangle_degree_le_remainder_add_three hT hvu hvw huw Q
      (hattach u hvu.ne.symm huQ)
    have hs := SectionFiveGlobal.outside_core_strict hS he.symm hstrip hdef hn ht
      (show G.degree v ≤ (oneTriangleRemainder G Q v).card + 3 by omega) hcore
    omega
  have hwQ : w ∈ Q := by
    by_contra hwQ
    have hw := oneTriangle_degree_le_remainder_add_three hT hvw hvu huw.symm Q
      (hattach w hvw.ne.symm hwQ)
    have hs := SectionFiveGlobal.outside_core_strict hS he.symm hstrip hdef hn ht
      (show G.degree v ≤ (oneTriangleRemainder G Q v).card + 3 by omega) hcore
    omega
  have hu := oneTriangle_degree_le_core_add_remainder hT hvu hvw huw Q hwQ
  have hw := oneTriangle_degree_le_core_add_remainder hT hvw hvu huw.symm Q huQ
  have hdeg : G.degree v ≤ 1 + (oneTriangleRemainder G Q v).card +
      min (oneTriangleCoreNeighbors G Q u).card (oneTriangleCoreNeighbors G Q w).card := by omega
  exact ⟨huQ, hwQ, SectionFiveGlobal.inside_core_equality_slack hS he.symm hstrip hdef hn ht
    hdeg (hedge u huQ w hwQ hvu hvw huw) heq⟩

/-- Neighbours outside the core, restricted to the paper's remainder set. -/
noncomputable def oneTriangleOutsideNeighbors (Q : Finset V) (v u : V) : Finset V := by
  classical
  exact G.neighborFinset u ∩ oneTriangleRemainder G Q v

/-- If both surviving triangle vertices lie in the core, their outside
neighbour sets are disjoint: otherwise they would form a second triangle. -/
theorem oneTriangle_outside_neighbor_card_add_le (hT : triangleCount G ≤ 1)
    {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : G.Adj u w)
    (Q : Finset V) (hvQ : v ∉ Q) :
    (oneTriangleOutsideNeighbors (G := G) Q v u).card +
      (oneTriangleOutsideNeighbors (G := G) Q v w).card ≤
      (oneTriangleRemainder G Q v).card := by
  classical
  let U := oneTriangleOutsideNeighbors (G := G) Q v u
  let W := oneTriangleOutsideNeighbors (G := G) Q v w
  have hd : Disjoint U W := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hux : G.Adj u x := by simpa [U, oneTriangleOutsideNeighbors] using (mem_inter.mp hx).1
    have hwx : G.Adj w x := by simpa [W, oneTriangleOutsideNeighbors] using (mem_inter.mp hy).1
    have heq := oneTriangle_common_neighbor hT huw hvu.symm hvw.symm hux hwx
    have hr := (mem_inter.mp hx).2
    have hne : x ≠ v := by
      have hh : x ≠ v ∧ x ∉ Q ∧ ¬G.Adj v x := by
        simpa only [oneTriangleRemainder, mem_filter, mem_univ, true_and] using hr
      exact hh.1
    exact hne heq
  have hsub : U ∪ W ⊆ oneTriangleRemainder G Q v := by
    intro x hx
    rcases mem_union.mp hx with hx | hx
    · exact (mem_inter.mp hx).2
    · exact (mem_inter.mp hx).2
  have h := card_le_card hsub
  rw [card_union_of_disjoint hd] at h
  exact h

/-- Refined degree estimate with the actual outside-neighbour count,
needed to force the equality remainder to vanish. -/
theorem oneTriangle_degree_le_core_add_outside (hT : triangleCount G ≤ 1)
    {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : G.Adj u w)
    (Q : Finset V) (hwQ : w ∈ Q) :
    G.degree u ≤ 1 + (oneTriangleCoreNeighbors G Q u).card +
      (oneTriangleOutsideNeighbors (G := G) Q v u).card := by
  classical
  have hcov : G.neighborFinset u ⊆ insert v
      (oneTriangleCoreNeighbors G Q u ∪ oneTriangleOutsideNeighbors (G := G) Q v u) := by
    intro x hx
    by_cases hxv : x = v
    · simp [hxv]
    apply mem_insert_of_mem
    by_cases hxQ : x ∈ Q
    · apply mem_union_left
      simpa only [oneTriangleCoreNeighbors, mem_inter, mem_neighborFinset] using
        (show G.Adj u x ∧ x ∈ Q from ⟨by simpa using hx, hxQ⟩)
    · apply mem_union_right
      simp only [oneTriangleOutsideNeighbors, mem_inter, mem_neighborFinset,
        oneTriangleRemainder, mem_filter, mem_univ, true_and]
      refine ⟨by simpa using hx, hxv, hxQ, ?_⟩
      intro hvx
      exact hxQ ((oneTriangle_common_neighbor hT hvu hvw huw hvx
        (by simpa using hx)) ▸ hwQ)
  have h := card_le_card hcov
  have h1 := card_insert_le v
    (oneTriangleCoreNeighbors G Q u ∪ oneTriangleOutsideNeighbors (G := G) Q v u)
  have h2 := card_union_le (oneTriangleCoreNeighbors G Q u)
    (oneTriangleOutsideNeighbors (G := G) Q v u)
  rw [card_neighborFinset_eq_degree] at h
  omega

/-- Once the saturated core is Petersen (hence its triangle-edge endpoints
have core degree three and `a=2`), all equality arithmetic collapses to the
thirteen-vertex case. -/
theorem oneTriangle_petersen_equality_parameters (hT : triangleCount G ≤ 1)
    {v u w : V} (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : G.Adj u w)
    (hdu : G.degree v ≤ G.degree u) (hdw : G.degree v ≤ G.degree w)
    (Q : Finset V) (hvQ : v ∉ Q) (huQ : u ∈ Q) (hwQ : w ∈ Q)
    (hu3 : (oneTriangleCoreNeighbors G Q u).card = 3)
    (hw3 : (oneTriangleCoreNeighbors G Q w).card = 3)
    (hslack : G.degree v = 4 + (oneTriangleRemainder G Q v).card)
    {t : ℕ} (ht : t + 2 = G.degree v + (oneTriangleRemainder G Q v).card) :
    (oneTriangleRemainder G Q v).card = 0 ∧ G.degree v = 4 ∧ t = 2 := by
  have hu := oneTriangle_degree_le_core_add_outside hT hvu hvw huw Q hwQ
  have hw := oneTriangle_degree_le_core_add_outside hT hvw hvu huw.symm Q huQ
  have hd := oneTriangle_outside_neighbor_card_add_le hT hvu hvw huw Q hvQ
  rw [hu3] at hu
  rw [hw3] at hw
  have hh := SectionFiveGlobal.petersen_equality_arithmetic
    (show G.degree v ≤ 4 + (oneTriangleOutsideNeighbors (G := G) Q v u).card by omega)
    (show G.degree v ≤ 4 + (oneTriangleOutsideNeighbors (G := G) Q v w).card by omega)
    hd hslack ht
  exact ⟨hh.1, hh.2.2.2⟩

/-- Saturation of the selected triangle-edge attachment inequality identifies
an actual Petersen core, rather than merely its order and edge count. -/
theorem oneTriangle_saturated_core_petersen
    (hC : StrongC4Free G) {v u w : V}
    (hvu : G.Adj v u) (hvw : G.Adj v w) (huw : G.Adj u w)
    (Q : Finset V) (hvQ : v ∉ Q) (huQ : u ∈ Q) (hwQ : w ∈ Q)
    (hclass : ChenXuSmallCore (G.induce (Q : Set V)))
    (heq : (oneTriangleCoreNeighbors G Q v).card +
      min (oneTriangleCoreNeighbors G Q u).card (oneTriangleCoreNeighbors G Q w).card =
        3 * Q.card - 2 * edgeCount (G.induce (Q : Set V)) + 5) :
    Nonempty (G.induce (Q : Set V) ≃g petersenGraph) := by
  classical
  let A := oneTriangleSelected (G := G) Q v
  have hA : ChenXuAttachmentDisjoint (G.induce (Q : Set V)) A := by
    intro x hx y hy hxy z hbad
    have hvx : G.Adj v x := by simpa [A, oneTriangleSelected] using hx
    have hvy : G.Adj v y := by simpa [A, oneTriangleSelected] using hy
    have hd := oneTriangle_core_neighborSets_disjoint hC (Q : Set V) hvQ hvx hvy hxy
    exact Set.disjoint_left.mp hd hbad.1 hbad.2
  have huA : (⟨u, huQ⟩ : (Q : Set V)) ∈ A := by simp [A, oneTriangleSelected, hvu]
  have hwA : (⟨w, hwQ⟩ : (Q : Set V)) ∈ A := by simp [A, oneTriangleSelected, hvw]
  apply chenXu_core_attachment_edge_eq_petersen hclass A hA huA hwA huw
  rw [oneTriangleSelected_card, oneTriangle_core_degree, oneTriangle_core_degree]
  have hn : Fintype.card (Q : Set V) = Q.card := by simp
  rw [hn]
  exact heq

/-- Concrete numerical equality witness, ready for the finite Petersen
extension contradiction. -/
structure OneTriangleEqualityCore (G : SimpleGraph V) where
  v : V
  u : V
  w : V
  triangle_vu : G.Adj v u
  triangle_vw : G.Adj v w
  triangle_uw : G.Adj u w
  core : Finset V
  deleted_not_core : v ∉ core
  u_core : u ∈ core
  w_core : w ∈ core
  petersen : Nonempty (G.induce (core : Set V) ≃g petersenGraph)
  outside_card : (univ \ insert v core).card = 2
  remainder_empty : (oneTriangleRemainder G core v).card = 0
  deleted_core_neighbors : (oneTriangleCoreNeighbors G core v).card = 2
  attachment : ∀ x, x ≠ v → x ∉ core → (oneTriangleCoreNeighbors G core x).card ≤ 1

/-- Equality yields an actual Petersen core and precisely two exterior vertices. -/
theorem oneTriangle_equality_core_exists
    (hc : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 7)
    (hT : triangleCount G ≤ 1) (hpos : triangleCount G ≠ 0)
    (hcut : ∀ s, ¬ IsCutVertex G s)
    (hequality : neighbourhoodIndependenceSum G = 3 * Fintype.card V) :
    Nonempty (OneTriangleEqualityCore G) := by
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
  have hattach : ∀ x, x ≠ v → x ∉ Q →
      (oneTriangleCoreNeighbors G Q x).card ≤ 1 := by
    intro x hxv hxQ
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
  have hvQ : v ∉ Q := by simpa [Q] using oneTriangle_not_mem_ambientCore v R
  let eQ := edgeCount (G.induce (Q : Set V))
  let eta := 3 * Q.card - 2 * eQ
  let t := Fintype.card V - 1 - Q.card
  let a := (oneTriangleCoreNeighbors G Q v).card
  let A := oneTriangleSelected (G := G) Q v
  have hA : ChenXuAttachmentDisjoint (G.induce (Q : Set V)) A := by
    intro x hx y hy hxy z hbad
    have hvx : G.Adj v x := by simpa [A, oneTriangleSelected] using hx
    have hvy : G.Adj v y := by simpa [A, oneTriangleSelected] using hy
    exact Set.disjoint_left.mp
      (oneTriangle_core_neighborSets_disjoint hC (Q : Set V) hvQ hvx hvy hxy) hbad.1 hbad.2
  have hqc : Fintype.card (Q : Set V) = Q.card := by simp
  have hcore : a ≤ eta + 2 := by
    have hh := chenXu_core_attachment_card hclass A hA
    rw [oneTriangleSelected_card, hqc] at hh
    exact hh
  have hedge : ∀ x ∈ Q, ∀ y ∈ Q, G.Adj v x → G.Adj v y → G.Adj x y →
      a + min (oneTriangleCoreNeighbors G Q x).card
        (oneTriangleCoreNeighbors G Q y).card ≤ eta + 5 := by
    intro x hx y hy hvx hvy hxy
    have hxA : (⟨x, hx⟩ : (Q : Set V)) ∈ A := by simp [A, oneTriangleSelected, hvx]
    have hyA : (⟨y, hy⟩ : (Q : Set V)) ∈ A := by simp [A, oneTriangleSelected, hvy]
    have hh := chenXu_core_attachment_edge hclass A hA hxA hyA hxy
    rw [oneTriangleSelected_card, oneTriangle_core_degree, oneTriangle_core_degree, hqc] at hh
    exact hh
  have hstrip : edgeCount (G.induce {v}ᶜ) = eQ + t := by
    have hn : Fintype.card ({v}ᶜ : Set V) = Fintype.card V - 1 := by
      have hh := Fintype.card_subtype_compl (fun x : V => x = v)
      have hsing : Fintype.card {x : V // x = v} = 1 := by simp
      change Fintype.card {x : V // ¬x = v} = _
      omega
    simpa only [H, he, hcard, hn] using hre
  have hnum : 2 * eQ + eta = 3 * Q.card := by dsimp [eta, eQ]; omega
  have hn : Fintype.card V = Q.card + t + 1 := by
    have hlt : Q.card < Fintype.card V := by
      have hsub : Q ⊂ univ := Finset.ssubset_iff_subset_ne.mpr
        ⟨subset_univ _, fun h => hvQ (h.symm ▸ mem_univ v)⟩
      simpa using Finset.card_lt_card hsub
    dsimp [t]; omega
  have hO : (univ \ insert v Q).card = t := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_insert_of_notMem hvQ]
    dsimp [t]; omega
  have ht := oneTriangle_attachment_partition (G := G) Q v
  rw [hO] at ht
  obtain ⟨huQ, hwQ, hslack, hedgeeq⟩ := oneTriangle_equality_core_slack
    hC hT hvu hvw huw hdu hdw Q eQ eta t a hstrip hnum hn ht hcore hedge hattach hequality
  obtain ⟨p⟩ := oneTriangle_saturated_core_petersen hC hvu hvw huw Q hvQ huQ hwQ hclass hedgeeq
  have hdegree (x : V) (hx : x ∈ Q) : (oneTriangleCoreNeighbors G Q x).card = 3 := by
    rw [← oneTriangle_core_degree Q hx, ← p.degree_eq]
    have hh : ∀ z : PetersenVertex, petersenGraph.degree z = 3 := by decide
    exact hh _
  have hpeq : 2 * eQ = 3 * Q.card := by
    have h1 := chenXu_edgeCount_iso p
    have h2 := Fintype.card_congr p.toEquiv
    have h3 : edgeCount petersenGraph = 15 := by decide
    have h4 : Fintype.card PetersenVertex = 10 := by decide
    rw [h3] at h1
    rw [h4, hqc] at h2
    dsimp [eQ]; omega
  have heta : eta = 0 := by omega
  have hu3 := hdegree u huQ
  have hw3 := hdegree w hwQ
  have ha : a = 2 := by rw [hu3, hw3] at hedgeeq; simp only [min_self] at hedgeeq; omega
  have hdslack : G.degree v = 4 + (oneTriangleRemainder G Q v).card := by
    rw [hu3, hw3] at hslack
    simp only [min_self] at hslack
    omega
  have htt : t + 2 = G.degree v + (oneTriangleRemainder G Q v).card := by omega
  obtain ⟨hc0, hd4, ht2⟩ := oneTriangle_petersen_equality_parameters hT hvu hvw huw hdu hdw
    Q hvQ huQ hwQ hu3 hw3 hdslack htt
  exact ⟨⟨v, u, w, hvu, hvw, huw, Q, hvQ, huQ, hwQ, ⟨p⟩, by omega, hc0, ha, hattach⟩⟩

/-- The concrete thirteen-vertex equality witness contradicts P7-freeness. -/
theorem oneTriangle_equality_core_impossible (hC : StrongC4Free G)
    (hp : IsPkFree G 7) (hT : triangleCount G ≤ 1)
    (hcut : ∀ s, ¬ IsCutVertex G s) (D : OneTriangleEqualityCore G) : False := by
  classical
  obtain ⟨p⟩ := D.petersen
  let e : petersenGraph ↪g G := p.symm.toEmbedding.trans (Embedding.induce (D.core : Set V))
  have hecore (z : PetersenVertex) : e z ∈ D.core := (p.symm z).property
  have hev : ∀ z, D.v ≠ e z := fun z h => D.deleted_not_core (h ▸ hecore z)
  obtain ⟨x, y, hxy, hO⟩ := Finset.card_eq_two.mp D.outside_card
  have hxO : x ∈ univ \ insert D.v D.core := by rw [hO]; simp
  have hyO : y ∈ univ \ insert D.v D.core := by rw [hO]; simp
  have hx : x ≠ D.v ∧ x ∉ D.core := by simpa using hxO
  have hy : y ≠ D.v ∧ y ∉ D.core := by simpa using hyO
  have hxcore : ∀ z, x ≠ e z := fun z h => hx.2 (h ▸ hecore z)
  have hycore : ∀ z, y ≠ e z := fun z h => hy.2 (h ▸ hecore z)
  have hpart : ∀ z, (∃ a, z = e a) ∨ z = D.v ∨ z = x ∨ z = y := by
    intro z
    by_cases hzQ : z ∈ D.core
    · left
      refine ⟨p ⟨z, hzQ⟩, ?_⟩
      exact congrArg Subtype.val (p.symm_apply_apply ⟨z, hzQ⟩) |>.symm
    · by_cases hzv : z = D.v
      · exact Or.inr (Or.inl hzv)
      · have hzO : z ∈ univ \ insert D.v D.core := by simp [hzv, hzQ]
        rw [hO] at hzO
        simpa only [mem_insert, mem_singleton] using
          (show (∃ a, z = e a) ∨ z = D.v ∨ z = x ∨ z = y from
            Or.inr (Or.inr (by simpa using hzO)))
  have hadj (z : V) (hzv : z ≠ D.v) (hzQ : z ∉ D.core) : G.Adj D.v z := by
    by_contra hh
    have hz : z ∈ oneTriangleRemainder G D.core D.v := by
      simp [oneTriangleRemainder, hzv, hzQ, hh]
    have hempty := Finset.card_eq_zero.mp D.remainder_empty
    rw [hempty] at hz
    exact Finset.notMem_empty _ hz
  have hselected : oneTriangleCoreNeighbors G D.core D.v = {D.u, D.w} := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      have hdu : D.u ∈ oneTriangleCoreNeighbors G D.core D.v := by
        simp [oneTriangleCoreNeighbors, D.triangle_vu, D.u_core]
      have hdw : D.w ∈ oneTriangleCoreNeighbors G D.core D.v := by
        simp [oneTriangleCoreNeighbors, D.triangle_vw, D.w_core]
      have hsub : {D.u, D.w} ⊆ oneTriangleCoreNeighbors G D.core D.v := by
        intro z hz
        rcases mem_insert.mp hz with rfl | hz
        · exact hdu
        · exact (mem_singleton.mp hz) ▸ hdw
      have heq : {D.u, D.w} = oneTriangleCoreNeighbors G D.core D.v :=
        Finset.eq_of_subset_of_card_le hsub (by simpa [D.triangle_uw.ne] using D.deleted_core_neighbors.le)
      rw [← heq] at hz
      exact hz
    · simp [D.triangle_uw.ne, D.deleted_core_neighbors]
  have hvtrace : ∀ z, G.Adj D.v (e z) ↔ z = p ⟨D.u, D.u_core⟩ ∨ z = p ⟨D.w, D.w_core⟩ := by
    intro z
    have hm : G.Adj D.v (e z) ↔ e z ∈ oneTriangleCoreNeighbors G D.core D.v := by
      simp [oneTriangleCoreNeighbors, hecore]
    rw [hm, hselected]
    simp only [mem_insert, mem_singleton]
    constructor
    · rintro (h | h)
      · left; apply p.symm.injective; apply Subtype.ext; simpa [e] using h
      · right; apply p.symm.injective; apply Subtype.ext; simpa [e] using h
    · rintro (rfl | rfl) <;> simp [e]
  have huni (z : V) (hzv : z ≠ D.v) (hzQ : z ∉ D.core) :
      ∀ a b, G.Adj z (e a) → G.Adj z (e b) → a = b := by
    intro a b ha hb
    have hsmall := Finset.card_le_one.mp (D.attachment z hzv hzQ)
    apply e.injective
    apply hsmall
    · simp [oneTriangleCoreNeighbors, ha, hecore]
    · simp [oneTriangleCoreNeighbors, hb, hecore]
  exact SectionFiveGlobal.petersenTriangle_partition_not_P7free hC hp hT e D.v x y
    hev hxcore hycore hx.1.symm hy.1.symm hxy hpart (hcut D.v)
    (p ⟨D.u, D.u_core⟩) (p ⟨D.w, D.w_core⟩)
    (p.map_rel_iff.mpr D.triangle_uw) hvtrace
    (hadj x hx.1 hx.2) (hadj y hy.1 hy.2) (huni x hx.1 hx.2) (huni y hy.1 hy.2)

/-- Strict one-triangle bound in the no-cut case. No low-loss or adjacent
 degree-two invariant is needed after the sharp attachment inequalities. -/
theorem oneTriangle_strict_noCut (hc : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 7) (hT : triangleCount G ≤ 1) (hpos : triangleCount G ≠ 0)
    (hcut : ∀ s, ¬ IsCutVertex G s) :
    neighbourhoodIndependenceSum G < 3 * Fintype.card V := by
  have hle := oneTriangle_mass_noCut hc hC hp hT hpos hcut
  apply lt_of_le_of_ne hle
  intro heq
  obtain ⟨D⟩ := oneTriangle_equality_core_exists hc hC hp hT hpos hcut heq
  exact oneTriangle_equality_core_impossible hC hp hT hcut D

end InducedPaths
