module

public import InducedPaths.Basic
public import InducedPaths.Graphs

open scoped SimpleGraph
open SimpleGraph Classical

set_option maxHeartbeats 2000000

@[expose] public section
namespace InducedPaths
namespace RadiusFourExtension
variable {V : Type*} {G : SimpleGraph V}

/-- Exterior vertices cannot occur internally in a nontrivial induced path. -/
theorem path_external_endpoint {n : ℕ} (E : RadiusFourExtension G)
    (f : pathGraph n ↪g G) (hn : 3 ≤ n) :
    ∀ i : Fin n, (∀ j, E.cycleEmb j ≠ f i) → i.val = 0 ∨ i.val = n - 1 := by
  intro i hoff
  by_contra hnot
  have hi0 : i.val ≠ 0 := fun h => hnot (Or.inl h)
  have hil : i.val ≠ n - 1 := fun h => hnot (Or.inr h)
  have hlt : i.val < n := i.isLt
  let p : Fin n := ⟨i.val - 1, by omega⟩
  let q : Fin n := ⟨i.val + 1, by omega⟩
  have hpq : p ≠ q := by
    intro h
    have := congrArg Fin.val h
    simp [p, q] at this
  have hadj_p : G.Adj (f p) (f i) := by
    rw [f.map_adj_iff, pathGraph_adj]
    left
    simp [p]
    omega
  have hadj_q : G.Adj (f i) (f q) := by
    rw [f.map_adj_iff, pathGraph_adj]
    left
    simp [q]
  have hchord : ¬ G.Adj (f p) (f q) := by
    rw [f.map_adj_iff, pathGraph_adj]
    simp [p, q]
    omega
  have hfpq : f p ≠ f q := f.injective.ne hpq
  rcases E.exhaustive (f i) with ⟨j, hj⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
  · exact (hoff j hj).elim
  · have hp_mem := E.no_extra_attach j (f i) (f p) hj hadj_p.symm
    have hq_mem := E.no_extra_attach j (f i) (f q) hj hadj_q
    rcases hp_mem with hpC | hpA <;> rcases hq_mem with hqC | hqA
    · exact (hfpq (hpC.trans hqC.symm)).elim
    · have hcross := (E.trace j (f q) hqA j).mpr rfl
      rw [← hpC] at hcross
      exact hchord hcross.symm
    · have hcross := (E.trace j (f p) hpA j).mpr rfl
      rw [← hqC] at hcross
      exact hchord hcross
    · exact hfpq (E.matching j (f i) hj (f q) hqA hadj_q (f p) hpA hadj_p.symm)
  · have hp_mem := (E.edge_adj j (f i) hj (f p)).mp hadj_p.symm
    have hq_mem := (E.edge_adj j (f i) hj (f q)).mp hadj_q
    have hcycle : G.Adj (E.cycleEmb j) (E.cycleEmb (j + 1)) := by
      rw [E.cycle_induced, cycleGraph_adj']
      right
      simp
    rcases hp_mem with hp1 | hp2 <;> rcases hq_mem with hq1 | hq2
    · exact (hfpq (hp1.trans hq1.symm)).elim
    · exact hchord (hp1 ▸ hq2 ▸ hcycle)
    · exact hchord (hp2 ▸ hq1 ▸ hcycle.symm)
    · exact (hfpq (hp2.trans hq2.symm)).elim

/-- An induced octagonal path would put six consecutive internal vertices on the
hexagon, forcing an impossible induced spanning path there. -/
theorem isP8Free (E : RadiusFourExtension G) : IsPkFree G 8 := by
  rintro ⟨f⟩
  have hc (i : Fin 6) : ∃ j, E.cycleEmb j = f ⟨i.val + 1, by omega⟩ := by
    by_contra h
    have he := E.path_external_endpoint f (by omega) ⟨i.val + 1, by omega⟩
      (by simpa using h)
    dsimp at he
    omega
  choose g hg using hc
  have hinj : Function.Injective g := by
    intro i j h
    have hh := f.injective ((hg i).symm.trans ((congrArg E.cycleEmb h).trans (hg j)))
    have hv := congrArg Fin.val hh
    apply Fin.ext
    dsimp at hv
    omega
  have adj (a b : Fin 6) : (cycleGraph 6).Adj (g a) (g b) ↔
      (pathGraph 6).Adj a b := by
    rw [← E.cycle_induced, hg a, hg b, f.map_adj_iff, pathGraph_adj, pathGraph_adj]
    simp only
    omega
  have hsurj := (Finite.injective_iff_surjective).mp hinj
  obtain ⟨a, ha⟩ := hsurj (g 0 + 1)
  obtain ⟨b, hb⟩ := hsurj (g 0 - 1)
  have hf : ∀ i : Fin 6, (cycleGraph 6).Adj i (i + 1) ∧
      (cycleGraph 6).Adj i (i - 1) ∧ i + 1 ≠ i - 1 := by decide
  have hpa := (adj 0 a).mp (ha ▸ (hf (g 0)).1)
  have hpb := (adj 0 b).mp (hb ▸ (hf (g 0)).2.1)
  have ha1 : a = 1 := by
    apply Fin.ext
    simpa [pathGraph_adj, eq_comm] using hpa
  have hb1 : b = 1 := by
    apply Fin.ext
    simpa [pathGraph_adj, eq_comm] using hpb
  exact (hf (g 0)).2.2 (ha.symm.trans ((congrArg g (ha1.trans hb1.symm)).trans hb))

/-- The seven-vertex path displayed in the converse proof. -/
def pathSeven (E : RadiusFourExtension G) (x y : V) (a : Fin 7) : V :=
  ![x, E.cycleEmb 0, E.cycleEmb 5, E.cycleEmb 4,
    E.cycleEmb 3, E.cycleEmb 2, y] a

theorem pathSeven_embedding (E : RadiusFourExtension G) (x y : V)
    (hx : x ∈ E.attach 0) (hy : y ∈ E.attach 2) :
    Nonempty (pathGraph 7 ↪g G) := by
  have hxy : x ≠ y := by
    intro h
    exact Set.disjoint_left.mp (E.attach_pairwise (by decide : (0 : Fin 6) ≠ 2)) hx (h ▸ hy)
  have hnxy : ¬ G.Adj x y := E.no_cross (by decide) x hx y hy
  refine ⟨{toFun := E.pathSeven x y, inj' := ?_, map_rel_iff' := ?_}⟩
  · intro a b h
    fin_cases a <;> fin_cases b <;>
      dsimp [pathSeven] at h ⊢ <;>
      first | rfl | exact (hxy h).elim | exact (hxy h.symm).elim |
        exact (E.attach_off_cycle 0 x hx _ h).elim |
        exact (E.attach_off_cycle 0 x hx _ h.symm).elim |
        exact (E.attach_off_cycle 2 y hy _ h).elim |
        exact (E.attach_off_cycle 2 y hy _ h.symm).elim |
        exact (by have := E.cycleEmb.injective h; contradiction)
  · intro a b
    change G.Adj (E.pathSeven x y a) (E.pathSeven x y b) ↔ _
    fin_cases a <;> fin_cases b <;>
      simp [pathSeven, E.cycle_induced, E.trace 0 x hx, E.trace 2 y hy,
        G.adj_comm, hnxy, cycleGraph_adj, pathGraph_adj] <;> decide

theorem inducedPathOrder_eq_seven [Fintype V] (E : RadiusFourExtension G) :
    inducedPathOrder G = 7 := by
  have hu := (isPkFree_iff_inducedPathOrder_lt G 8).mp E.isP8Free
  obtain ⟨x, hx⟩ := E.attach_nonempty 0
  obtain ⟨y, hy⟩ := E.attach_nonempty 2
  have hl : 7 ≤ inducedPathOrder G :=
    le_csSup (inducedPathOrder_bddAbove G) (E.pathSeven_embedding x y hx hy)
  omega

theorem cycle_edist_le_three (E : RadiusFourExtension G) (i j : Fin 6) :
    G.edist (E.cycleEmb i) (E.cycleEmb j) ≤ 3 := by
  have hf : ∀ i j : Fin 6, i = j ∨ (cycleGraph 6).Adj i j ∨
      (∃ k, (cycleGraph 6).Adj i k ∧ (cycleGraph 6).Adj k j) ∨
      ∃ k l, (cycleGraph 6).Adj i k ∧ (cycleGraph 6).Adj k l ∧ (cycleGraph 6).Adj l j := by decide
  rcases hf i j with h | h | ⟨k, h1, h2⟩ | ⟨k, l, h1, h2, h3⟩
  · subst j; simp
  · exact ((E.cycle_induced i j).mpr h).toWalk.edist_le.trans (by simp)
  · exact (((E.cycle_induced i k).mpr h1).toWalk.append
      ((E.cycle_induced k j).mpr h2).toWalk).edist_le.trans (by simp; decide)
  · exact ((((E.cycle_induced i k).mpr h1).toWalk.append
      ((E.cycle_induced k l).mpr h2).toWalk).append
      ((E.cycle_induced l j).mpr h3).toWalk).edist_le.trans (by simp)

theorem cycle_eccent_le_four (E : RadiusFourExtension G) (i : Fin 6) :
    G.eccent (E.cycleEmb i) ≤ 4 := by
  rw [eccent_le_iff]
  intro v
  rcases E.exhaustive v with ⟨j, rfl⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
  · exact (E.cycle_edist_le_three i j).trans (by decide)
  · calc
      G.edist (E.cycleEmb i) v ≤ G.edist (E.cycleEmb i) (E.cycleEmb j) +
          G.edist (E.cycleEmb j) v := G.edist_triangle
      _ ≤ 3 + 1 := add_le_add (E.cycle_edist_le_three i j)
        (((E.trace j v hj j).mpr rfl).symm.toWalk.edist_le.trans (by simp))
      _ = 4 := by decide
  · calc
      G.edist (E.cycleEmb i) v ≤ G.edist (E.cycleEmb i) (E.cycleEmb j) +
          G.edist (E.cycleEmb j) v := G.edist_triangle
      _ ≤ 3 + 1 := add_le_add (E.cycle_edist_le_three i j)
        (((E.edge_adj j v hj (E.cycleEmb j)).mpr (Or.inl rfl)).symm.toWalk.edist_le.trans (by simp))
      _ = 4 := by decide

theorem connected (E : RadiusFourExtension G) : G.Connected := by
  have hr (v : V) : G.Reachable (E.cycleEmb 0) v := by
    apply edist_ne_top_iff_reachable.mp
    have h : G.edist (E.cycleEmb 0) v ≤ 4 :=
      edist_le_eccent.trans (E.cycle_eccent_le_four 0)
    exact ne_top_of_le_ne_top (by simp) h
  letI : Nonempty V := ⟨E.cycleEmb 0⟩
  exact ⟨fun u v => (hr u).symm.trans (hr v)⟩

/-- A finite quotient retaining all possible edges (and attachment loops). -/
def tagRel : Fin 18 → Fin 18 → Prop := fun a b =>
  if ha : a.val < 6 then
    if hb : b.val < 6 then (cycleGraph 6).Adj ⟨a.val, by omega⟩ ⟨b.val, by omega⟩
    else if b.val < 12 then a.val = b.val - 6
    else a.val = b.val - 12 ∨ (a.val + 5) % 6 = b.val - 12
  else if a.val < 12 then
    if b.val < 6 then b.val = a.val - 6
    else if b.val < 12 then a = b else False
  else if b.val < 6 then b.val = a.val - 12 ∨ (b.val + 5) % 6 = a.val - 12
  else False

instance : DecidableRel tagRel := fun a b => by unfold tagRel; infer_instance

noncomputable def tag (E : RadiusFourExtension G) (v : V) : Fin 18 :=
  if hc : ∃ i, E.cycleEmb i = v then ⟨hc.choose.val, by omega⟩
  else if ha : ∃ i, v ∈ E.attach i then ⟨ha.choose.val + 6, by omega⟩
  else ⟨(E.exhaustive v |>.resolve_left hc |>.resolve_left ha).choose.val + 12, by omega⟩

theorem tag_cycle (E : RadiusFourExtension G) (i : Fin 6) :
    E.tag (E.cycleEmb i) = ⟨i.val, by omega⟩ := by
  have h : ∃ j, E.cycleEmb j = E.cycleEmb i := ⟨i, rfl⟩
  simp only [tag, dite_eq_left h]
  have he := E.cycleEmb.injective h.choose_spec
  simp only [he]

theorem tag_attach (E : RadiusFourExtension G) (i : Fin 6) (v : V)
    (hv : v ∈ E.attach i) : E.tag v = ⟨i.val + 6, by omega⟩ := by
  have hc : ¬ ∃ j, E.cycleEmb j = v := by
    rintro ⟨j, hj⟩
    exact E.attach_off_cycle i v hv j hj
  have ha : ∃ j, v ∈ E.attach j := ⟨i, hv⟩
  have he : ha.choose = i := by
    by_contra hn
    exact Set.disjoint_left.mp (E.attach_pairwise hn) ha.choose_spec hv
  simp only [tag, dite_eq_right hc, dite_eq_left ha, he]

theorem tag_edge (E : RadiusFourExtension G) (i : Fin 6) (v : V)
    (hv : E.edgeVert i = some v) : E.tag v = ⟨i.val + 12, by omega⟩ := by
  have hc : ¬ ∃ j, E.cycleEmb j = v := by
    rintro ⟨j, hj⟩
    exact E.edge_off_cycle i v hv j hj
  have ha : ¬ ∃ j, v ∈ E.attach j := by
    rintro ⟨j, hj⟩
    exact E.edge_off_attach i v j v hv hj rfl
  have he := E.exhaustive v |>.resolve_left hc |>.resolve_left ha
  have hi : he.choose = i := E.edge_inj _ _ v he.choose_spec hv
  simp only [tag, dite_eq_right hc, dite_eq_right ha, hi]

theorem tag_adj (E : RadiusFourExtension G) {v w : V} (h : G.Adj v w) :
    tagRel (E.tag v) (E.tag w) := by
  rcases E.exhaustive v with ⟨i, rfl⟩ | ⟨i, hi⟩ | ⟨i, hi⟩ <;>
    rcases E.exhaustive w with ⟨j, rfl⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
  · simpa [E.tag_cycle, tagRel] using (E.cycle_induced i j).mp h
  · have hh := (E.trace j w hj i).mp h.symm
    subst j
    simp [E.tag_cycle, E.tag_attach i w hj, tagRel]
  · rcases (E.edge_adj j w hj _).mp h.symm with hh | hh
    · have he := E.cycleEmb.injective hh
      subst i
      simp [E.tag_cycle, E.tag_edge j w hj, tagRel]
    · have he := E.cycleEmb.injective hh
      subst i
      rw [E.tag_cycle, E.tag_edge j w hj]
      have hf : ∀ j : Fin 6, tagRel ⟨(j + 1).val, by omega⟩ ⟨j.val + 12, by omega⟩ := by decide
      exact hf j
  · have hh := (E.trace i v hi j).mp h
    subst j
    simp [E.tag_attach i v hi, E.tag_cycle, tagRel]
  · have he : i = j := by
      by_contra hn
      exact E.no_cross hn v hi w hj h
    subst j
    simp [E.tag_attach i v hi, E.tag_attach i w hj, tagRel]
  · rcases (E.edge_adj j w hj v).mp h.symm with he | he
    · exact (E.attach_off_cycle i v hi j he.symm).elim
    · exact (E.attach_off_cycle i v hi (j + 1) he.symm).elim
  · rcases (E.edge_adj i v hi _).mp h with hh | hh
    · have he := E.cycleEmb.injective hh
      subst j
      simp [E.tag_cycle, E.tag_edge i v hi, tagRel]
    · have he := E.cycleEmb.injective hh
      subst j
      rw [E.tag_cycle, E.tag_edge i v hi]
      have hf : ∀ i : Fin 6, tagRel ⟨i.val + 12, by omega⟩ ⟨(i + 1).val, by omega⟩ := by decide
      exact hf i
  · rcases (E.edge_adj i v hi w).mp h with he | he
    · exact (E.attach_off_cycle j w hj i he.symm).elim
    · exact (E.attach_off_cycle j w hj (i + 1) he.symm).elim
  · rcases (E.edge_adj i v hi w).mp h with he | he
    · exact (E.edge_off_cycle j w hj i he.symm).elim
    · exact (E.edge_off_cycle j w hj (i + 1) he.symm).elim

theorem tag_fiber_unique (E : RadiusFourExtension G) {v w : V}
    (he : E.tag v = E.tag w) (hu : (E.tag v).val < 6 ∨ 12 ≤ (E.tag v).val) : v = w := by
  rcases E.exhaustive v with ⟨i, rfl⟩ | ⟨i, hi⟩ | ⟨i, hi⟩
  · rw [E.tag_cycle] at he
    rcases E.exhaustive w with ⟨j, rfl⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [E.tag_cycle] at he
      have hv : i.val = j.val := congrArg (fun k : Fin 18 => k.val) he
      exact congrArg E.cycleEmb (Fin.ext hv)
    · rw [E.tag_attach j w hj] at he
      have := congrArg Fin.val he
      dsimp at this
      omega
    · rw [E.tag_edge j w hj] at he
      have := congrArg Fin.val he
      dsimp at this
      omega
  · rw [E.tag_attach i v hi] at hu
    dsimp at hu
    omega
  · rw [E.tag_edge i v hi] at he
    rcases E.exhaustive w with ⟨j, rfl⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
    · rw [E.tag_cycle] at he
      have := congrArg Fin.val he
      dsimp at this
      omega
    · rw [E.tag_attach j w hj] at he
      have := congrArg Fin.val he
      dsimp at this
      omega
    · rw [E.tag_edge j w hj] at he
      have hij : i = j := Fin.ext (by have := congrArg Fin.val he; dsimp at this; omega)
      subst j
      exact Option.some.inj (hi.symm.trans hj)

def tagDistance (i : Fin 6) (a : Fin 18) : ℕ :=
  let d := fun j : ℕ => min ((j + 6 - i.val) % 6) ((i.val + 6 - j) % 6)
  if a.val < 6 then 1 + d a.val
  else if a.val < 12 then
    if a.val = i.val + 6 then 0 else 2 + d (a.val - 6)
  else 2 + min (d (a.val - 12)) (d ((a.val - 11) % 6))

theorem tagDistance_certificate :
    (∀ i : Fin 6, tagDistance i ⟨i.val + 6, by omega⟩ = 0) ∧
    (∀ a : Fin 18, ∃ i : Fin 6, 4 ≤ tagDistance i a) ∧
    (∀ i : Fin 6, ∀ a b : Fin 18, tagRel a b → tagDistance i a ≤ 1 + tagDistance i b) := by
  decide

theorem walk_tagDistance (E : RadiusFourExtension G) (i : Fin 6) {u v : V}
    (p : G.Walk u v) : tagDistance i (E.tag u) ≤ p.length + tagDistance i (E.tag v) := by
  induction p with
  | nil => simp
  | @cons u w p h ih =>
    have hh := tagDistance_certificate.2.2 i _ _ (E.tag_adj h)
    simp only [Walk.length_cons]
    omega

theorem radius_eq_four [Fintype V] (E : RadiusFourExtension G) : radiusNat G = 4 := by
  have hl : (4 : ℕ∞) ≤ G.radius := by
    rw [radius]
    apply le_iInf
    intro v
    obtain ⟨i, hi⟩ := tagDistance_certificate.2.1 (E.tag v)
    obtain ⟨w, hw⟩ := E.attach_nonempty i
    obtain ⟨p, hp⟩ := E.connected.exists_walk_length_eq_edist v w
    have ht := E.walk_tagDistance i p
    rw [E.tag_attach i w hw, tagDistance_certificate.1 i, Nat.add_zero] at ht
    have hd : (4 : ℕ∞) ≤ G.edist v w := by
      rw [← hp]
      exact_mod_cast hi.trans ht
    exact hd.trans edist_le_eccent
  have hu : G.radius ≤ 4 := G.radius_le_eccent.trans (E.cycle_eccent_le_four 0)
  simp [radiusNat, le_antisymm hu hl]

theorem tag_c4_certificate : ∀ a b c d : Fin 18,
    tagRel a b → tagRel b c → tagRel c d → tagRel d a →
    (a = c ∧ (a.val < 6 ∨ 12 ≤ a.val)) ∨
    (b = d ∧ (b.val < 6 ∨ 12 ≤ b.val)) ∨
    (6 ≤ a.val ∧ a.val < 12 ∧ a = b ∧ a = d) ∨
    (6 ≤ b.val ∧ b.val < 12 ∧ b = a ∧ b = c) ∨
    (6 ≤ c.val ∧ c.val < 12 ∧ c = b ∧ c = d) ∨
    (6 ≤ d.val ∧ d.val < 12 ∧ d = a ∧ d = c) := by
  decide

theorem attach_of_tag (E : RadiusFourExtension G) {v w : V} (i : Fin 6)
    (hv : v ∈ E.attach i) (h : E.tag v = E.tag w) : w ∈ E.attach i := by
  rcases E.exhaustive w with ⟨j, rfl⟩ | ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [E.tag_attach i v hv, E.tag_cycle] at h
    have := congrArg Fin.val h
    dsimp at this
    omega
  · rw [E.tag_attach i v hv, E.tag_attach j w hj] at h
    have he : i = j := Fin.ext (by have := congrArg Fin.val h; dsimp at this; omega)
    simpa [he] using hj
  · rw [E.tag_attach i v hv, E.tag_edge j w hj] at h
    have := congrArg Fin.val h
    dsimp at this
    omega

theorem same_attach_neighbors (E : RadiusFourExtension G) {a b c : V}
    (ha : 6 ≤ (E.tag a).val ∧ (E.tag a).val < 12)
    (hb : E.tag a = E.tag b) (hc : E.tag a = E.tag c)
    (hab : G.Adj a b) (hac : G.Adj a c) : b = c := by
  rcases E.exhaustive a with ⟨i, rfl⟩ | ⟨i, hi⟩ | ⟨i, hi⟩
  · rw [E.tag_cycle] at ha; dsimp at ha; omega
  · exact E.matching i a hi c (E.attach_of_tag i hi hc) hac b (E.attach_of_tag i hi hb) hab
  · rw [E.tag_edge i a hi] at ha; dsimp at ha; omega

theorem strongC4Free (E : RadiusFourExtension G) : StrongC4Free G := by
  rintro ⟨f⟩
  have he (i j : Fin 4) (h : (cycleGraph 4).Adj i j) : G.Adj (f i) (f j) := f.toHom.map_adj h
  have h01 := he 0 1 (by decide)
  have h12 := he 1 2 (by decide)
  have h23 := he 2 3 (by decide)
  have h30 := he 3 0 (by decide)
  rcases tag_c4_certificate _ _ _ _ (E.tag_adj h01) (E.tag_adj h12)
      (E.tag_adj h23) (E.tag_adj h30) with h | h | h | h | h | h
  · have := f.injective (E.tag_fiber_unique h.1 h.2)
    contradiction
  · have := f.injective (E.tag_fiber_unique h.1 h.2)
    contradiction
  · have := f.injective (E.same_attach_neighbors ⟨h.1, h.2.1⟩ h.2.2.1 h.2.2.2 h01 h30.symm)
    contradiction
  · have := f.injective (E.same_attach_neighbors ⟨h.1, h.2.1⟩ h.2.2.1 h.2.2.2 h01.symm h12)
    contradiction
  · have := f.injective (E.same_attach_neighbors ⟨h.1, h.2.1⟩ h.2.2.1 h.2.2.2 h12.symm h23)
    contradiction
  · have := f.injective (E.same_attach_neighbors ⟨h.1, h.2.1⟩ h.2.2.1 h.2.2.2 h30 h23.symm)
    contradiction

theorem converse [Fintype V] (E : RadiusFourExtension G) :
    G.Connected ∧ StrongC4Free G ∧ radiusNat G = 4 ∧ inducedPathOrder G = 7 :=
  ⟨E.connected, E.strongC4Free, E.radius_eq_four, E.inducedPathOrder_eq_seven⟩

end RadiusFourExtension
end InducedPaths
