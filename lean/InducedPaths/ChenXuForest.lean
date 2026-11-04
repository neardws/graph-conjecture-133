module

public import InducedPaths.ChenXuCore
public import InducedPaths.PetersenPaths

open scoped SimpleGraph
open SimpleGraph Finset

@[expose] public section
namespace InducedPaths
variable {V : Type*} {G : SimpleGraph V}

/-- A simple path whose endpoints avoid a degree-one vertex cannot visit it. -/
lemma chenXu_path_avoids_leaf [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {v a b : V} (hv : G.degree v = 1) (ha : a ≠ v) (hb : b ≠ v)
    (p : G.Walk a b) (hp : p.IsPath) : v ∉ p.support := by
  classical
  intro hmem
  obtain ⟨k, hk, hkle⟩ := Walk.mem_support_iff_exists_getVert.mp hmem
  have hkpos : 0 < k := by
    by_contra hn
    have hk0 : k = 0 := by omega
    simp only [hk0, Walk.getVert_zero] at hk
    exact ha hk
  have hklt : k < p.length := by
    by_contra hn
    have hke : k = p.length := by omega
    simp only [hke, Walk.getVert_length] at hk
    exact hb hk
  obtain ⟨u, hu, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hv
  have hprev : G.Adj v (p.getVert (k - 1)) := by
    have h := (p.adj_getVert_succ (i := k - 1) (by omega)).symm
    simpa only [show k - 1 + 1 = k by omega, hk] using h
  have hnext : G.Adj v (p.getVert (k + 1)) := by
    simpa only [hk] using p.adj_getVert_succ hklt
  have heq : p.getVert (k - 1) = p.getVert (k + 1) :=
    (huniq _ hprev).trans (huniq _ hnext).symm
  have hidx := hp.getVert_injOn (show k - 1 ≤ p.length by omega)
    (show k + 1 ≤ p.length by omega) heq
  omega

/-- Leaf stripping preserves every simple path between retained vertices, not merely
reachability: such a path cannot leave the retained set. -/
lemma ChenXuLeafStrips.path_support {S Q : Set V} (hs : ChenXuLeafStrips G S Q)
    {a b : V} (ha : a ∈ Q) (hb : b ∈ Q) (p : G.Walk a b) (hp : p.IsPath)
    (hS : ∀ z ∈ p.support, z ∈ S) : ∀ z ∈ p.support, z ∈ Q := by
  classical
  induction hs with
  | refl => exact hS
  | step S Q v hleaf tail ih =>
    have haS : a ∈ S := (tail.subset ha).1
    have hbS : b ∈ S := (tail.subset hb).1
    have hav : a ≠ v.val := (tail.subset ha).2
    have hbV : b ≠ v.val := (tail.subset hb).2
    let q := p.induce S hS
    have hq : q.IsPath := by
      apply Walk.IsPath.of_map (f := (Embedding.induce S).toHom)
      change (p.induce S hS |>.map (Embedding.induce S).toHom).IsPath
      rw [Walk.map_induce]
      exact hp
    have havoid : v ∉ q.support := chenXu_path_avoids_leaf hleaf
      (fun h => hav (congrArg Subtype.val h))
      (fun h => hbV (congrArg Subtype.val h)) q hq
    have havoid' : v.val ∉ p.support := by
      intro hv
      apply havoid
      dsimp [q]
      rw [Walk.support_induce]
      simpa using hv
    apply ih ha hb
    intro z hz
    exact ⟨hS z hz, fun h => havoid' (h ▸ hz)⟩

/-- In particular, retained vertices cannot be joined by a simple path with a
nonempty exterior interior. -/
lemma ChenXuLeafStrips.no_exterior_path {Q : Set V}
    (hs : ChenXuLeafStrips G Set.univ Q) {a b : V}
    (ha : a ∈ Q) (hb : b ∈ Q) (p : G.Walk a b) (hp : p.IsPath)
    (hi : ∀ i, 0 < i → i < p.length → p.getVert i ∉ Q) : p.length ≤ 1 := by
  by_contra hn
  have hlen : 1 < p.length := by omega
  exact hi 1 (by omega) hlen
    (hs.path_support ha hb p hp (fun _ _ => Set.mem_univ _) _ (p.getVert_mem_support 1))

/-- A connected exterior side has only one possible root in the retained core. -/
lemma ChenXuLeafStrips.exterior_root_unique {Q : Set V}
    (hs : ChenXuLeafStrips G Set.univ Q) {a b x y : V}
    (ha : a ∈ Q) (hb : b ∈ Q) (hx : x ∉ Q) (hy : y ∉ Q)
    (hax : G.Adj a x) (hby : G.Adj b y)
    (hr : (G.induce Qᶜ).Reachable ⟨x, hx⟩ ⟨y, hy⟩) : a = b := by
  classical
  by_contra hab
  obtain ⟨p, hp⟩ := hr.exists_isPath
  let incl : (G.induce Qᶜ) →g G := ⟨Subtype.val, fun h => h⟩
  let q := p.map incl
  have hq : q.IsPath := hp.map Subtype.val_injective
  have hout : ∀ z ∈ q.support, z ∉ Q := by
    intro z hz
    dsimp [q] at hz
    rw [Walk.support_map] at hz
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz
    exact w.property
  have haout : a ∉ q.support := fun h => hout a h ha
  have hbout : b ∉ q.support := fun h => hout b h hb
  have hqc : (q.cons hax).IsPath := by
    exact Walk.IsPath.cons hq haout
  have hfull : ((q.cons hax).concat hby.symm).IsPath := by
    apply Walk.IsPath.concat hqc
    simp only [Walk.support_cons, List.mem_cons, not_or]
    exact ⟨Ne.symm hab, hbout⟩
  have hxmem : x ∈ ((q.cons hax).concat hby.symm).support := by
    simp only [Walk.support_concat, List.mem_append, Walk.support_cons, List.mem_cons]
    exact Or.inl (Or.inr q.start_mem_support)
  exact hx (hs.path_support ha hb _ hfull (fun _ _ => Set.mem_univ _) x hxmem)

/-- Every exterior component of a connected graph touches the nonempty core. -/
lemma chenXu_exterior_touches_core (hc : G.Connected) {Q : Set V} (hq : Q.Nonempty)
    (x : ↥(Qᶜ)) : ∃ (y : ↥(Qᶜ)) (a : Q),
      (G.induce Qᶜ).Reachable x y ∧ G.Adj a y := by
  classical
  let H := G.induce Qᶜ
  by_contra hn
  have closed : ∀ u v, G.Adj u v →
      (∃ hu : u ∉ Q, H.Reachable x ⟨u, hu⟩) →
      ∃ hv : v ∉ Q, H.Reachable x ⟨v, hv⟩ := by
    intro u v huv ⟨hu, hr⟩
    have hv : v ∉ Q := by
      intro hv
      exact hn ⟨⟨u, hu⟩, ⟨v, hv⟩, hr, huv.symm⟩
    exact ⟨hv, hr.trans (show H.Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv).reachable⟩
  have propagate {u v} (w : G.Walk u v) :
      (∃ hu : u ∉ Q, H.Reachable x ⟨u, hu⟩) →
      ∃ hv : v ∉ Q, H.Reachable x ⟨v, hv⟩ := by
    induction w with
    | nil => exact id
    | cons h w ih => exact fun hu => ih (closed _ _ h hu)
  obtain ⟨a, ha⟩ := hq
  obtain ⟨w⟩ := hc.preconnected x.val a
  obtain ⟨hnot, -⟩ := propagate w ⟨x.property, Reachable.rfl⟩
  exact hnot ha

set_option maxHeartbeats 2000000 in
/-- A two-edge branch attached to a Petersen core forces an induced P7. -/
lemma chenXu_petersen_no_branch {Q : Set V}
    (hs : ChenXuLeafStrips G Set.univ Q) (htri : G.CliqueFree 3)
    (hp : IsPkFree G 7) (e : G.induce Q ≃g petersenGraph)
    (a : Q) (x y : ↥(Qᶜ)) (hax : G.Adj a x) (hxy : G.Adj x y) : False := by
  classical
  obtain ⟨f, hf⟩ := SectionFiveGlobal.petersen_rooted_P5 (e a)
  let c : Fin 5 → V := fun i => (e.symm (f i)).val
  have hc0 : c 0 = a.val := by simp [c, hf]
  have hcQ (i) : c i ∈ Q := (e.symm (f i)).property
  have hci : Function.Injective c := fun i j h =>
    f.injective (e.symm.injective (Subtype.ext h))
  have hcadj (i j) : G.Adj (c i) (c j) ↔ (pathGraph 5).Adj i j := by
    exact (e.symm.map_rel_iff.trans f.map_rel_iff)
  have hxQ : x.val ∉ Q := x.property
  have hyQ : y.val ∉ Q := y.property
  have hna : ¬ G.Adj a y := chenXu_not_adj_of_two_edges htri hax hxy
  have hnX (i) (hi : i ≠ 0) : ¬ G.Adj x (c i) := by
    intro h
    have heq := hs.exterior_root_unique a.property (hcQ i) x.property x.property
      hax h.symm (Reachable.rfl)
    exact hi (hci ((hc0.trans heq).symm))
  have hnY (i) : ¬ G.Adj y (c i) := by
    intro h
    have heq := hs.exterior_root_unique a.property (hcQ i) x.property y.property
      hax h.symm (show (G.induce Qᶜ).Adj x y from hxy).reachable
    exact hna (by simpa only [heq] using h.symm)
  let p : Fin 7 → V := ![y, x, c 0, c 1, c 2, c 3, c 4]
  have hcne (i j : Fin 5) (hij : i ≠ j) : c i ≠ c j := fun h => hij (hci h)
  have pinj : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [p] at hij ⊢ <;>
      grind only [hxy.ne]
  have pc : ∀ i j, G.Adj (p i) (p j) ↔ (pathGraph 7).Adj i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [p, pathGraph_adj] <;>
      grind only [G.adj_comm, G.irrefl, pathGraph_adj]
  exact hp ⟨{toFun := p, inj' := pinj, map_rel_iff' := fun {i j} => pc i j}⟩

/-- No exterior edge can occur over a Petersen core. -/
lemma chenXu_petersen_exterior_independent (hc : G.Connected) {Q : Set V}
    (hs : ChenXuLeafStrips G Set.univ Q) (htri : G.CliqueFree 3)
    (hp : IsPkFree G 7) (e : G.induce Q ≃g petersenGraph) :
    ∀ x y : ↥(Qᶜ), ¬ G.Adj x y := by
  classical
  intro x y hxy
  have hq : Q.Nonempty := ⟨(e.symm petersenHub).val, (e.symm petersenHub).property⟩
  obtain ⟨z, a, hxz, haz⟩ := chenXu_exterior_touches_core hc hq x
  obtain ⟨p⟩ := hxz
  cases p with
  | nil => exact chenXu_petersen_no_branch hs htri hp e a x y haz hxy
  | @cons u w v huw p =>
    have hzhas : ∃ t : ↥(Qᶜ), G.Adj z t := by
      have hne : ¬ (Walk.cons huw p).Nil := Walk.not_nil_cons
      exact ⟨_, ((Walk.cons huw p).adj_penultimate hne).symm⟩
    obtain ⟨t, hzt⟩ := hzhas
    exact chenXu_petersen_no_branch hs htri hp e a z t haz hzt

open Classical in
/-- All vertices outside a stripped Petersen core are genuine ambient leaves. -/
theorem chenXu_petersen_outside_degree_one [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hc : G.Connected) {Q : Set V}
    (hs : ChenXuLeafStrips G Set.univ Q) (htri : G.CliqueFree 3)
    (hp : IsPkFree G 7) (e : G.induce Q ≃g petersenGraph) :
    ∀ x : V, x ∉ Q → G.degree x = 1 := by
  classical
  intro x hx
  have hq : Q.Nonempty := ⟨(e.symm petersenHub).val, (e.symm petersenHub).property⟩
  obtain ⟨z, a, hxz, haz⟩ := chenXu_exterior_touches_core hc hq ⟨x, hx⟩
  have hind := chenXu_petersen_exterior_independent hc hs htri hp e
  obtain ⟨p⟩ := hxz
  have hzx : z.val = x := by
    by_contra hne
    have hnil : ¬ p.Nil := p.not_nil_of_ne (fun h => hne (congrArg Subtype.val h).symm)
    have h := p.adj_snd hnil
    exact hind ⟨x, hx⟩ p.snd (show G.Adj x p.snd.val from h)
  have hax : G.Adj a x := by simpa only [hzx] using haz
  rw [degree_eq_one_iff_existsUnique_adj]
  refine ⟨a.val, hax.symm, ?_⟩
  intro y hxy
  have hy : y ∈ Q := by
    by_contra hyn
    exact hind ⟨x, hx⟩ ⟨y, hyn⟩ hxy
  exact hs.outside_neighbors x (Set.mem_univ _) hx ⟨hy, hxy⟩ ⟨a.property, hax.symm⟩

end InducedPaths
