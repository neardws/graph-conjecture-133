/- Extracting the closest triangle configurations used by the four seed rows. -/
module

public import InducedPaths.StatementsCore
public import InducedPaths.SeedEmbedding
public import InducedPaths.TrianglePairs

open Finset SimpleGraph

@[expose] public section

namespace InducedPaths

/-- Enumerate the remaining two vertices of a triangle around any chosen hub. -/
theorem triangle_vertices_at {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {s : Finset V} (hs : G.IsNClique 3 s) {u : V} (hu : u ∈ s) :
    ∃ a b, s = {u, a, b} ∧ G.Adj u a ∧ G.Adj a b ∧ G.Adj b u := by
  have hc : (s.erase u).card = 2 := by rw [card_erase_of_mem hu, hs.card_eq]
  obtain ⟨a, b, hab, heq⟩ := card_eq_two.mp hc
  have ha : a ∈ s.erase u := by simp [heq]
  have hb : b ∈ s.erase u := by simp [heq]
  have hsa : a ∈ s := mem_of_mem_erase ha
  have hsb : b ∈ s := mem_of_mem_erase hb
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · rw [← insert_erase hu, heq]
  · exact hs.isClique hu hsa (ne_of_mem_erase ha).symm
  · exact hs.isClique hsa hsb hab
  · exact hs.isClique hsb hu (ne_of_mem_erase hb)

/-- Distinct triangles that meet induce the actual distance-zero seed. -/
theorem sharedSeed_of_inter_nonempty {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (hC : StrongC4Free G) {s t : Finset V}
    (hs : G.IsNClique 3 s) (ht : G.IsNClique 3 t) (hne : s ≠ t)
    (hi : (s ∩ t).Nonempty) : Nonempty (sharedSeedGraph ↪g G) := by
  obtain ⟨u, hu⟩ := hi
  obtain ⟨a, b, hsEq, hT1⟩ := triangle_vertices_at hs (mem_inter.mp hu).1
  obtain ⟨c, d, htEq, hT2⟩ := triangle_vertices_at ht (mem_inter.mp hu).2
  have hinter := triangle_inter_card_le_one hC hs ht hne
  have hone : (s ∩ t) = {u} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hu, fun x hx =>
      (Finset.card_le_one.mp hinter) x hx u hu⟩
  have cross {x y : V} (hx : x ∈ s) (hy : y ∈ t) (hxu : x ≠ u) : x ≠ y := by
    intro hxy
    have hm : x ∈ s ∩ t := mem_inter.mpr ⟨hx, hxy ▸ hy⟩
    rw [hone] at hm
    exact hxu (mem_singleton.mp hm)
  exact ⟨sharedSeedEmbedding hC hT1 hT2
    ⟨cross (by simp [hsEq]) (by simp [htEq]) hT1.1.ne.symm,
     cross (by simp [hsEq]) (by simp [htEq]) hT1.1.ne.symm,
     cross (by simp [hsEq]) (by simp [htEq]) hT1.2.2.ne,
     cross (by simp [hsEq]) (by simp [htEq]) hT1.2.2.ne⟩⟩

/-- Closest endpoints of two disjoint triangles give precisely the hypotheses
of the distance bound and the explicit positive-distance seed embeddings. -/
theorem closest_disjoint_triangles {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 7) {s t : Finset V}
    (hs : G.IsNClique 3 s) (ht : G.IsNClique 3 t) (hdis : Disjoint s t) :
    ∃ u a b v c e : V,
      G.Adj u a ∧ G.Adj a b ∧ G.Adj b u ∧
      G.Adj v c ∧ G.Adj c e ∧ G.Adj e v ∧
      ({u, a, b} : Set V) ∩ {v, c, e} = ∅ ∧
      1 ≤ G.dist u v ∧ G.dist u v ≤ 3 ∧
      (∀ p q, p ∈ ({u, a, b} : Set V) → q ∈ ({v, c, e} : Set V) →
        G.dist u v ≤ G.dist p q) := by
  have hsne : s.Nonempty := Finset.card_pos.mp (by rw [hs.card_eq]; decide)
  have htne : t.Nonempty := Finset.card_pos.mp (by rw [ht.card_eq]; decide)
  obtain ⟨⟨u, v⟩, huv, hmin⟩ :=
    (s ×ˢ t).exists_min_image (fun p => G.dist p.1 p.2) (hsne.product htne)
  have hu : u ∈ s := (mem_product.mp huv).1
  have hv : v ∈ t := (mem_product.mp huv).2
  obtain ⟨a, b, hsEq, hT1⟩ := triangle_vertices_at hs hu
  obtain ⟨c, e, htEq, hT2⟩ := triangle_vertices_at ht hv
  have hdisj : ({u, a, b} : Set V) ∩ {v, c, e} = ∅ := by
    have hh : Disjoint (s : Set V) (t : Set V) := Finset.disjoint_coe.mpr hdis
    simpa [hsEq, htEq, Set.disjoint_iff_inter_eq_empty] using hh
  have hmin' : ∀ p q, p ∈ ({u, a, b} : Set V) → q ∈ ({v, c, e} : Set V) →
      G.dist u v ≤ G.dist p q := by
    intro p q hps hqt
    apply hmin (p, q)
    simpa [hsEq, htEq] using And.intro hps hqt
  have hne : u ≠ v := fun heq => (Finset.disjoint_left.mp hdis hu (heq ▸ hv))
  have hpos : 1 ≤ G.dist u v := by
    have hnzero : G.dist u v ≠ 0 := fun hh =>
      hne ((hconn u v).dist_eq_zero_iff.mp hh)
    omega
  exact ⟨u, a, b, v, c, e, hT1.1, hT1.2.1, hT1.2.2,
    hT2.1, hT2.2.1, hT2.2.2, hdisj, hpos,
    lemma_5_8_distance_le_three hC hp hT1 hT2 hdisj (hconn u v) rfl hmin', hmin'⟩

/-- Any two triangles with closest endpoints at distance at most three contain
one of the positive-distance certificate seeds. -/
theorem positiveSeed_of_closest {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hconn : G.Connected) (hC : StrongC4Free G)
    {u a b v c e : V}
    (hT1 : G.Adj u a ∧ G.Adj a b ∧ G.Adj b u)
    (hT2 : G.Adj v c ∧ G.Adj c e ∧ G.Adj e v)
    (hdisj : ({u, a, b} : Set V) ∩ {v, c, e} = ∅)
    (hpos : 1 ≤ G.dist u v) (hbound : G.dist u v ≤ 3)
    (hmin : ∀ x y, x ∈ ({u, a, b} : Set V) → y ∈ ({v, c, e} : Set V) →
      G.dist u v ≤ G.dist x y) :
    Nonempty (adjacentSeedGraph ↪g G) ∨
      Nonempty (distanceTwoSeedGraph ↪g G) ∨ Nonempty (distanceThreeSeedGraph ↪g G) := by
  have cases : G.dist u v = 1 ∨ G.dist u v = 2 ∨ G.dist u v = 3 := by omega
  rcases cases with hd | hd | hd
  · exact Or.inl ⟨adjacentSeedEmbedding hC hT1 hT2 hdisj (G.dist_eq_one_iff_adj.mp hd)⟩
  all_goals
    have hcross : ∀ x ∈ ({u, a, b} : Set V), ∀ y ∈ ({v, c, e} : Set V), ¬ G.Adj x y := by
      intro x hx y hy hxy
      have hm := hmin x y hx hy
      have hone := G.dist_eq_one_iff_adj.mpr hxy
      omega
    obtain ⟨w, hw⟩ := hconn.exists_walk_length_eq_dist u v
  · have hlen : w.length = 2 := hw.trans hd
    have hu : G.Adj u (w.getVert 1) := by
      simpa using w.adj_getVert_succ (show 0 < w.length by omega)
    have hv : G.Adj (w.getVert 1) v := by
      have hh := w.adj_getVert_succ (show 1 < w.length by omega)
      simpa [← hlen] using hh
    exact Or.inr (Or.inl ⟨distanceTwoSeedEmbedding hC hT1 hT2 hdisj hcross hu hv⟩)
  · have hlen : w.length = 3 := hw.trans hd
    have hu : G.Adj u (w.getVert 1) := by
      simpa using w.adj_getVert_succ (show 0 < w.length by omega)
    have hpq : G.Adj (w.getVert 1) (w.getVert 2) :=
      w.adj_getVert_succ (show 1 < w.length by omega)
    have hv : G.Adj (w.getVert 2) v := by
      have hh := w.adj_getVert_succ (show 2 < w.length by omega)
      simpa [← hlen] using hh
    have hleft : ∀ x ∈ ({u, a, b} : Set V), ¬ G.Adj x (w.getVert 2) := by
      intro x hx hxq
      have hm := hmin x v hx (by simp)
      have hb := G.dist_le ((Walk.nil.cons hv).cons hxq)
      simp only [Walk.length_cons, Walk.length_nil] at hb
      omega
    have hright : ∀ y ∈ ({v, c, e} : Set V), ¬ G.Adj (w.getVert 1) y := by
      intro y hy hpy
      have hm := hmin u y (by simp) hy
      have hb := G.dist_le ((Walk.nil.cons hpy).cons hu)
      simp only [Walk.length_cons, Walk.length_nil] at hb
      omega
    exact Or.inr (Or.inr ⟨distanceThreeSeedEmbedding hC hT1 hT2 hdisj
      hcross hleft hright hu hpq hv⟩)

/-- Two distinct triangles in a connected strong `C₄`-free, induced-`P₇`-free
graph realize one of the four actual certificate seed graphs. -/
theorem exists_certificate_seed_embedding {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hconn : G.Connected) (hC : StrongC4Free G) (hp : IsPkFree G 7)
    (htri : 2 ≤ triangleCount G) :
    Nonempty (sharedSeedGraph ↪g G) ∨ Nonempty (adjacentSeedGraph ↪g G) ∨
      Nonempty (distanceTwoSeedGraph ↪g G) ∨ Nonempty (distanceThreeSeedGraph ↪g G) := by
  obtain ⟨s, t, hs, ht, hne⟩ := exists_distinct_triangles htri
  by_cases hi : (s ∩ t).Nonempty
  · exact Or.inl (sharedSeed_of_inter_nonempty hC hs ht hne hi)
  · have hdis : Disjoint s t := Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hi)
    obtain ⟨u, a, b, v, c, e, hua, hab, hbu, hvc, hce, hev, hdisj, hpos, hbound, hmin⟩ :=
      closest_disjoint_triangles hconn hC hp hs ht hdis
    exact Or.inr (positiveSeed_of_closest hconn hC ⟨hua, hab, hbu⟩ ⟨hvc, hce, hev⟩
      hdisj hpos hbound hmin)

end InducedPaths
