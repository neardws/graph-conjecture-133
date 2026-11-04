/-
Section 4 local octagon calculations.

The earlier StatementsCore.lemma_4_1 omitted the P₈-free hypothesis of the
paper (main.tex, Lemma `lem:c8`). That statement is false: an octagon with one
pendant leaf has radius four. The public lemma now restores the hypothesis;
the standalone proof below does not invoke any StatementsCore proof gaps.
-/
module

public import InducedPaths.C6Trace
public meta import Mathlib.Data.Fintype.Defs
public meta import Mathlib.Combinatorics.SimpleGraph.CycleGraph

open scoped SimpleGraph
open SimpleGraph

@[expose] public section

namespace InducedPaths

/-- Adjacency on an octagon and one external vertex with prescribed trace. -/
def octTraceAdj (t : Fin 8 → Bool) : Option (Fin 8) → Option (Fin 8) → Prop
  | none, none => False
  | none, some j => t j = true
  | some i, none => t i = true
  | some i, some j => (cycleGraph 8).Adj i j

instance (t : Fin 8 → Bool) : DecidableRel (octTraceAdj t) := fun a b => by
  cases a <;> cases b <;> unfold octTraceAdj <;> infer_instance

/-- A path starting outside the octagon and proceeding in either direction. -/
def octTracePath (start : Fin 8) (reverse : Bool) (k : Fin 8) : Option (Fin 8) :=
  if k = 0 then none else some (if reverse then start - (k - 1) else start + (k - 1))

/-- Cycle distance at most two, expressed without a shortest-path computation. -/
def octNear (i j : Fin 8) : Prop :=
  i = j ∨ (cycleGraph 8).Adj i j ∨
    ∃ k, (cycleGraph 8).Adj i k ∧ (cycleGraph 8).Adj k j

instance : DecidableRel octNear := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The finite trace certificate, including explicit induced P₈ witnesses for
all traces excluded by the paper's P₈-free hypothesis. -/
theorem octTrace_certificate : ∀ t : Fin 8 → Bool,
    (∃ i, t i = true) →
    (∀ i, ¬ (t i = true ∧ t (i + 2) = true)) →
    ((∀ i, ∃ j, t j = true ∧ octNear i j) ∧
      ∃ i j, t i = true ∧ t j = true ∧
        (j = i + 4 ∨ (cycleGraph 8).Adj j (i + 4))) ∨
    (∃ start reverse, Function.Injective (octTracePath start reverse) ∧
      ∀ a b, octTraceAdj t (octTracePath start reverse a) (octTracePath start reverse b) ↔
        (pathGraph 8).Adj a b) := by
  native_decide

/-- Strong C₄-freeness forbids two contacts separated by two cycle edges. -/
theorem octTrace_no_distance_two {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 8 ↪g G) {w : V}
    (hw : ∀ i, c i ≠ w) (i : Fin 8) :
    ¬ (G.Adj w (c i) ∧ G.Adj w (c (i + 2))) := by
  rintro ⟨ha, hb⟩
  have hfin : ∀ i : Fin 8,
      (cycleGraph 8).Adj i (i + 1) ∧
      (cycleGraph 8).Adj (i + 1) (i + 2) ∧ i ≠ i + 2 := by native_decide
  obtain ⟨h₁, h₂, hne⟩ := hfin i
  exact hC (fourCycle_isContained ha ((c.map_rel_iff).2 h₁) ((c.map_rel_iff).2 h₂)
    hb.symm (hw (i + 1)).symm (fun h => hne (c.injective h)))

/-- The two distance consequences of the trace computation. -/
theorem octTrace_spread {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (hp : IsPkFree G 8) (c : cycleGraph 8 ↪g G)
    {w : V} (hw : ∀ i, c i ≠ w) (hne : ∃ i, G.Adj w (c i)) :
    (∀ i, ∃ j, G.Adj w (c j) ∧ octNear i j) ∧
      ∃ i j, G.Adj w (c i) ∧ G.Adj w (c j) ∧
        (j = i + 4 ∨ (cycleGraph 8).Adj j (i + 4)) := by
  classical
  let t : Fin 8 → Bool := fun i => decide (G.Adj w (c i))
  have ht : ∃ i, t i = true := by simpa [t] using hne
  have htwo : ∀ i, ¬ (t i = true ∧ t (i + 2) = true) := by
    simpa [t] using octTrace_no_distance_two hC c hw
  rcases octTrace_certificate t ht htwo with hgood | ⟨start, reverse, hinj, hpath⟩
  · simpa [t] using hgood
  · exfalso
    apply hp
    let f : Option (Fin 8) → V := fun x => x.elim w c
    have hf : Function.Injective f := by
      intro a b hab
      cases a with
      | none =>
          cases b with
          | none => rfl
          | some j => exact False.elim (hw j hab.symm)
      | some i =>
          cases b with
          | none => exact False.elim (hw i hab)
          | some j => exact congrArg some (c.injective hab)
    have hadj : ∀ a b, G.Adj (f a) (f b) ↔ octTraceAdj t a b := by
      intro a b
      cases a <;> cases b <;> simp [f, octTraceAdj, t, adj_comm]
    exact ⟨{
      toEmbedding := ⟨f ∘ octTracePath start reverse, hf.comp hinj⟩
      map_rel_iff' := by
        intro a b
        exact (hadj _ _).trans (hpath a b)
    }⟩

/-- A short cycle route yields an extended-distance bound in the host graph. -/
theorem octNear_edist_le_two {V : Type*} {G : SimpleGraph V}
    (c : cycleGraph 8 ↪g G) {i j : Fin 8} (h : octNear i j) :
    G.edist (c i) (c j) ≤ 2 := by
  rcases h with h | h | ⟨k, ha, hb⟩
  · subst j; simp
  · exact ((c.map_rel_iff).2 h).toWalk.edist_le.trans (by simp)
  · let p := ((c.map_rel_iff).2 ha).toWalk.append ((c.map_rel_iff).2 hb).toWalk
    exact p.edist_le.trans (by simp [p])

/-- Every cycle vertex other than the antipode is at cycle distance at most three. -/
theorem octCycle_edist_le_three {V : Type*} {G : SimpleGraph V}
    (c : cycleGraph 8 ↪g G) {i j : Fin 8} (h : j ≠ i + 4) :
    G.edist (c i) (c j) ≤ 3 := by
  have hfin : ∀ i j : Fin 8, j ≠ i + 4 →
      octNear i j ∨ ∃ k, octNear i k ∧ (cycleGraph 8).Adj k j := by native_decide
  rcases hfin i j h with hnear | ⟨k, hnear, hadj⟩
  · exact (octNear_edist_le_two c hnear).trans (by decide)
  · calc
      G.edist (c i) (c j) ≤ G.edist (c i) (c k) + G.edist (c k) (c j) :=
        G.edist_triangle
      _ ≤ 2 + 1 := add_le_add (octNear_edist_le_two c hnear)
        (((c.map_rel_iff).2 hadj).toWalk.edist_le.trans (by simp))
      _ = 3 := by decide

/-- With the P₈-free hypothesis from the paper, any external vertex makes
some cycle vertex have eccentricity at most three. -/
theorem octTrace_eccent_le_three {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (hp : IsPkFree G 8) (c : cycleGraph 8 ↪g G)
    (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i))
    {w : V} (hw : ∀ i, c i ≠ w) : ∃ i : Fin 8, G.eccent (c i) ≤ 3 := by
  classical
  obtain ⟨a, ha⟩ := hdom w
  have hwa : G.Adj w (c a) := ha.resolve_left (hw a).symm
  obtain ⟨_, i, j, hwi, hwj, hj⟩ := octTrace_spread hC hp c hw ⟨a, hwa⟩
  have hanti : G.edist (c i) (c (i + 4)) ≤ 3 := by
    rcases hj with hj | hj
    · subst j
      let p := hwi.symm.toWalk.append hwj.toWalk
      exact p.edist_le.trans (by simp [p]; decide)
    · let p := (hwi.symm.toWalk.append hwj.toWalk).append ((c.map_rel_iff).2 hj).toWalk
      exact p.edist_le.trans (by simp [p])
  refine ⟨i, ?_⟩
  rw [eccent_le_iff]
  intro v
  by_cases hv : ∃ j, c j = v
  · obtain ⟨j, rfl⟩ := hv
    by_cases hj : j = i + 4
    · simpa [hj] using hanti
    · exact octCycle_edist_le_three c hj
  · have hvout : ∀ j, c j ≠ v := by simpa using hv
    obtain ⟨a, ha⟩ := hdom v
    have hva : G.Adj v (c a) := ha.resolve_left (hvout a).symm
    obtain ⟨hspread, _⟩ := octTrace_spread hC hp c hvout ⟨a, hva⟩
    obtain ⟨j, hvj, hnear⟩ := hspread i
    calc
      G.edist (c i) v ≤ G.edist (c i) (c j) + G.edist (c j) v := G.edist_triangle
      _ ≤ 2 + 1 := add_le_add (octNear_edist_le_two c hnear)
        (hvj.symm.toWalk.edist_le.trans (by simp))
      _ = 3 := by decide

/-- Paper Lemma 4.1, with its necessary P₈-free hypothesis. -/
theorem lemma_4_1_with_p8_free {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] (_hconn : G.Connected) (hC : StrongC4Free G)
    (hp : IsPkFree G 8) (c : cycleGraph 8 ↪g G)
    (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i))
    (hr : 4 ≤ radiusNat G) : Nonempty (G ≃g cycleGraph 8) := by
  have hsurj : Function.Surjective c := by
    intro w
    by_contra hw
    have hout : ∀ i, c i ≠ w := by simpa using hw
    obtain ⟨i, hi⟩ := octTrace_eccent_le_three hC hp c hdom hout
    have hrad : G.radius ≤ 3 := (G.radius_le_eccent (u := c i)).trans hi
    have hradNat : radiusNat G ≤ 3 := by
      unfold radiusNat
      exact ENat.toNat_le_toNat hrad (by simp)
    omega
  let iso : cycleGraph 8 ≃g G :=
    { toEquiv := Equiv.ofBijective c ⟨c.injective, hsurj⟩
      map_rel_iff' := c.map_rel_iff' }
  exact ⟨iso.symm⟩

/-- The C₈ branch of Theorem 4.2: its forward assumptions suffice for the
paper's corrected lemma, without any change to Theorem 4.2's assumptions. -/
theorem theorem_4_2_dominating_octagon {V : Type*} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] (hconn : G.Connected) (hC : StrongC4Free G)
    (hr : radiusNat G = 4) (hp : inducedPathOrder G = 7)
    (c : cycleGraph 8 ↪g G) (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i)) :
    Nonempty (G ≃g cycleGraph 8) := by
  apply lemma_4_1_with_p8_free hconn hC ?_ c hdom (by omega)
  exact (isPkFree_iff_inducedPathOrder_lt G 8).2 (by omega)

/-! ### A checked obstruction to the uncorrected StatementsCore statement -/

/-- An octagon with one pendant leaf at vertex zero. -/
def octagonWithLeaf : SimpleGraph (Option (Fin 8)) where
  Adj := octTraceAdj (fun i => decide (i = 0))
  symm := ⟨by
    intro a b h
    cases a <;> cases b
    · simp [octTraceAdj] at h
    · exact h
    · exact h
    · exact h.symm⟩
  loopless := ⟨by intro a h; cases a <;> simp [octTraceAdj] at h⟩

instance : DecidableRel octagonWithLeaf.Adj := inferInstanceAs
  (DecidableRel (octTraceAdj (fun i => decide (i = 0))))

/-- The original octagon remains induced. -/
def octagonWithLeaf_cycle : cycleGraph 8 ↪g octagonWithLeaf where
  toEmbedding := ⟨some, Option.some_injective _⟩
  map_rel_iff' := by intros; rfl

theorem octagonWithLeaf_dominating : ∀ v, ∃ i,
    v = octagonWithLeaf_cycle i ∨ octagonWithLeaf.Adj v (octagonWithLeaf_cycle i) := by
  intro v
  cases v with
  | none => exact ⟨0, Or.inr (by decide)⟩
  | some i => exact ⟨i, Or.inl rfl⟩

theorem octagonWithLeaf_connected : octagonWithLeaf.Connected := by
  have hc : ∀ i j : Fin 8, octagonWithLeaf.Reachable (some i) (some j) := by
    intro i j
    exact ((connected_cycleGraph_add_one (n := 7)) i j).map octagonWithLeaf_cycle.toHom
  have hl : octagonWithLeaf.Reachable none (some 0) := (show octagonWithLeaf.Adj none (some 0) by decide).reachable
  refine ⟨?_⟩
  intro a b
  cases a with
  | none =>
      cases b with
      | none => exact Reachable.refl _
      | some j => exact hl.trans (hc 0 j)
  | some i =>
      cases b with
      | none => exact (hc i 0).trans hl.symm
      | some j => exact hc i j

theorem octagonWithLeaf_strongC4Free : StrongC4Free octagonWithLeaf := by
  have hfinite : ∀ a b c d, octagonWithLeaf.Adj a b → octagonWithLeaf.Adj b c →
      octagonWithLeaf.Adj c d → octagonWithLeaf.Adj d a → a = c ∨ b = d := by native_decide
  rintro ⟨f⟩
  have h01 : (cycleGraph 4).Adj 0 1 := by decide
  have h12 : (cycleGraph 4).Adj 1 2 := by decide
  have h23 : (cycleGraph 4).Adj 2 3 := by decide
  have h30 : (cycleGraph 4).Adj 3 0 := by decide
  rcases hfinite _ _ _ _ (f.toHom.map_rel' h01) (f.toHom.map_rel' h12)
      (f.toHom.map_rel' h23) (f.toHom.map_rel' h30) with h | h
  · have := f.injective h; exact (by decide : (0 : Fin 4) ≠ 2) this
  · have := f.injective h; exact (by decide : (1 : Fin 4) ≠ 3) this

/-- Explicit distance labels, used only as lower-bound certificates. -/
def octLeafLabel (a b : Option (Fin 8)) : ℕ :=
  let cyc (i j : Fin 8) := min ((i - j).val) ((j - i).val)
  match a, b with
  | none, none => 0
  | none, some j => 1 + cyc 0 j
  | some i, none => cyc i 0 + 1
  | some i, some j => cyc i j

theorem octLeafLabel_certificate :
    (∀ a, octLeafLabel a a = 0) ∧
    (∀ a b c, octagonWithLeaf.Adj b c → octLeafLabel a c ≤ octLeafLabel a b + 1) ∧
    (∀ a, ∃ b, 4 ≤ octLeafLabel a b) := by native_decide

/-- A Lipschitz integer label bounds from below the length of every walk. -/
theorem octLeafLabel_walk {a b : Option (Fin 8)} (p : octagonWithLeaf.Walk a b) :
    octLeafLabel a b ≤ p.length := by
  have hbound : ∀ {u v} (p : octagonWithLeaf.Walk u v),
      ∀ a, octLeafLabel a v ≤ octLeafLabel a u + p.length := by
    intro u v p
    induction p with
    | nil => intro a; simp
    | @cons u v w h p ih =>
        intro a
        have hstep := octLeafLabel_certificate.2.1 a u v h
        have hrest := ih a
        simp only [Walk.length_cons]
        omega
  simpa [octLeafLabel_certificate.1 a] using hbound p a

theorem octagonWithLeaf_radius_at_least_four : 4 ≤ radiusNat octagonWithLeaf := by
  have hlower : (4 : ℕ∞) ≤ octagonWithLeaf.radius := by
    change (4 : ℕ∞) ≤ ⨅ a, octagonWithLeaf.eccent a
    refine le_iInf fun a => ?_
    obtain ⟨b, hb⟩ := octLeafLabel_certificate.2.2 a
    obtain ⟨p, hp⟩ := octagonWithLeaf_connected.exists_walk_length_eq_edist a b
    have hl : 4 ≤ p.length := hb.trans (octLeafLabel_walk p)
    have he : (4 : ℕ∞) ≤ octagonWithLeaf.edist a b := by
      rw [← hp]
      exact_mod_cast hl
    exact he.trans octagonWithLeaf.edist_le_eccent
  have hne := octagonWithLeaf.radius_ne_top_iff.mpr octagonWithLeaf_connected
  exact ENat.toNat_le_toNat hlower hne

theorem octagonWithLeaf_not_iso : ¬ Nonempty (octagonWithLeaf ≃g cycleGraph 8) := by
  rintro ⟨f⟩
  have hcard := Fintype.card_congr f.toEquiv
  norm_num at hcard

/-- The exact hypothesis/conclusion combination in StatementsCore.lemma_4_1
has a finite counterexample; no unproved theorem is used here. -/
theorem lemma_4_1_counterexample :
    octagonWithLeaf.Connected ∧ StrongC4Free octagonWithLeaf ∧
    (∀ v, ∃ i, v = octagonWithLeaf_cycle i ∨ octagonWithLeaf.Adj v (octagonWithLeaf_cycle i)) ∧
    4 ≤ radiusNat octagonWithLeaf ∧ ¬ Nonempty (octagonWithLeaf ≃g cycleGraph 8) :=
  ⟨octagonWithLeaf_connected, octagonWithLeaf_strongC4Free, octagonWithLeaf_dominating,
    octagonWithLeaf_radius_at_least_four, octagonWithLeaf_not_iso⟩

/-! ### Canonical octagon properties for the reverse classification -/

theorem cycle8_strongC4Free : StrongC4Free (cycleGraph 8) := by
  have hfinite : ∀ a b c d : Fin 8, (cycleGraph 8).Adj a b → (cycleGraph 8).Adj b c →
      (cycleGraph 8).Adj c d → (cycleGraph 8).Adj d a → a = c ∨ b = d := by native_decide
  rintro ⟨f⟩
  rcases hfinite _ _ _ _ (f.toHom.map_rel' (by decide : (cycleGraph 4).Adj 0 1))
      (f.toHom.map_rel' (by decide : (cycleGraph 4).Adj 1 2))
      (f.toHom.map_rel' (by decide : (cycleGraph 4).Adj 2 3))
      (f.toHom.map_rel' (by decide : (cycleGraph 4).Adj 3 0)) with h | h
  · exact (by decide : (0 : Fin 4) ≠ 2) (f.injective h)
  · exact (by decide : (1 : Fin 4) ≠ 3) (f.injective h)

/-- The first seven vertices induce a path in the octagon. -/
def cycle8_path7 : pathGraph 7 ↪g cycleGraph 8 where
  toEmbedding := Fin.castLEEmb (by decide)
  map_rel_iff' := by native_decide

/-- A spanning path embedding in the octagon contradicts the endpoint degree. -/
theorem cycle8_p8_free : IsPkFree (cycleGraph 8) 8 := by
  rintro ⟨f⟩
  have hsurj := (Finite.injective_iff_surjective).1 f.injective
  have htwo : ∀ i : Fin 8, ∃ a b, a ≠ b ∧ (cycleGraph 8).Adj i a ∧ (cycleGraph 8).Adj i b := by native_decide
  obtain ⟨a, b, hab, ha, hb⟩ := htwo (f 0)
  obtain ⟨u, rfl⟩ := hsurj a
  obtain ⟨v, rfl⟩ := hsurj b
  have hu : u = 1 := by
    have h := f.map_rel_iff.1 ha
    rw [pathGraph_adj] at h
    apply Fin.ext
    rcases h with h | h
    · simpa using h.symm
    · simp at h
  have hv : v = 1 := by
    have h := f.map_rel_iff.1 hb
    rw [pathGraph_adj] at h
    apply Fin.ext
    rcases h with h | h
    · simpa using h.symm
    · simp at h
  exact hab (congrArg f (hu.trans hv.symm))

theorem cycle8_inducedPathOrder : inducedPathOrder (cycleGraph 8) = 7 := by
  have hlo : 7 ≤ inducedPathOrder (cycleGraph 8) :=
    le_csSup (inducedPathOrder_bddAbove _) (show pathGraph 7 ⊴ cycleGraph 8 from ⟨cycle8_path7⟩)
  have hhi := (isPkFree_iff_inducedPathOrder_lt (cycleGraph 8) 8).1 cycle8_p8_free
  omega

/-- Cycle distance labels, with an elementary finite Lipschitz certificate. -/
def octDistance (i j : Fin 8) : ℕ := min (i - j).val (j - i).val

theorem octDistance_certificate :
    (∀ a, octDistance a a = 0) ∧
    (∀ a b c, (cycleGraph 8).Adj b c → octDistance a c ≤ octDistance a b + 1) ∧
    (∀ a, octDistance a (a + 4) = 4) := by native_decide

theorem octDistance_walk {a b : Fin 8} (p : (cycleGraph 8).Walk a b) : octDistance a b ≤ p.length := by
  have hbound : ∀ {u v} (p : (cycleGraph 8).Walk u v), ∀ a,
      octDistance a v ≤ octDistance a u + p.length := by
    intro u v p
    induction p with
    | nil => intro a; simp
    | @cons u v w h p ih =>
        intro a
        have hstep := octDistance_certificate.2.1 a u v h
        have hrest := ih a
        simp only [Walk.length_cons]
        omega
  simpa [octDistance_certificate.1 a] using hbound p a

theorem cycle8_radius : radiusNat (cycleGraph 8) = 4 := by
  have hc : (cycleGraph 8).Connected := connected_cycleGraph_add_one (n := 7)
  have hlo : (4 : ℕ∞) ≤ (cycleGraph 8).radius := by
    change (4 : ℕ∞) ≤ ⨅ a, (cycleGraph 8).eccent a
    refine le_iInf fun a => ?_
    obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_edist a (a + 4)
    have hl : 4 ≤ p.length := by simpa [octDistance_certificate.2.2 a] using octDistance_walk p
    have he : (4 : ℕ∞) ≤ (cycleGraph 8).edist a (a + 4) := by
      rw [← hp]
      exact_mod_cast hl
    exact he.trans (cycleGraph 8).edist_le_eccent
  have hhi : (cycleGraph 8).radius ≤ 4 := by
    apply (cycleGraph 8).radius_le_eccent.trans (show (cycleGraph 8).eccent 0 ≤ 4 from ?_)
    rw [eccent_le_iff]
    intro j
    by_cases hj : j = 4
    · subst j
      let p := (show (cycleGraph 8).Adj 0 1 by decide).toWalk |>.append
        (show (cycleGraph 8).Adj 1 2 by decide).toWalk |>.append
        (show (cycleGraph 8).Adj 2 3 by decide).toWalk |>.append
        (show (cycleGraph 8).Adj 3 4 by decide).toWalk
      exact p.edist_le.trans (by simp [p])
    · have hj' : j ≠ (0 : Fin 8) + 4 := by simpa using hj
      exact (octCycle_edist_le_three (SimpleGraph.Iso.refl : cycleGraph 8 ≃g cycleGraph 8).toEmbedding hj').trans (by decide : (3 : ℕ∞) ≤ 4)
  have heq : (cycleGraph 8).radius = 4 := le_antisymm hhi hlo
  simp [radiusNat, heq]

/-- The canonical octagon satisfies the complete left-hand side of Theorem 4.2. -/
theorem cycle8_radius_four_properties :
    (cycleGraph 8).Connected ∧ StrongC4Free (cycleGraph 8) ∧
      radiusNat (cycleGraph 8) = 4 ∧ inducedPathOrder (cycleGraph 8) = 7 :=
  ⟨connected_cycleGraph_add_one (n := 7), cycle8_strongC4Free, cycle8_radius, cycle8_inducedPathOrder⟩

/-- A graph homomorphism cannot increase extended distance. -/
theorem graphHom_edist_le {A B : Type*} {J : SimpleGraph A} {K : SimpleGraph B}
    (f : J →g K) (a b : A) : K.edist (f a) (f b) ≤ J.edist a b := by
  by_cases hr : J.Reachable a b
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    exact (p.map f).edist_le.trans_eq (by simpa using hp)
  · simp [edist_eq_top_of_not_reachable hr]

/-- Extended graph distance is preserved by a graph isomorphism. -/
theorem graphIso_edist {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (u v : V) : H.edist (e u) (e v) = G.edist u v := by
  apply le_antisymm (graphHom_edist_le e.toHom u v)
  simpa using graphHom_edist_le e.symm.toHom (e u) (e v)

/-- Eccentricity is preserved by a graph isomorphism. -/
theorem graphIso_eccent {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (u : V) : H.eccent (e u) = G.eccent u := by
  apply le_antisymm
  · rw [eccent_le_iff]
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    rw [graphIso_edist]
    exact G.edist_le_eccent
  · rw [eccent_le_iff]
    intro v
    rw [← graphIso_edist e u v]
    exact H.edist_le_eccent

/-- Radius is preserved by a graph isomorphism. -/
theorem graphIso_radius {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : H.radius = G.radius := by
  apply le_antisymm
  · change H.radius ≤ ⨅ a, G.eccent a
    refine le_iInf fun a => ?_
    rw [← graphIso_eccent e a]
    exact H.radius_le_eccent
  · change G.radius ≤ ⨅ b, H.eccent b
    refine le_iInf fun b => ?_
    rw [← graphIso_eccent e.symm b]
    exact G.radius_le_eccent

/-- The entire octagon branch transports to any isomorphic host graph. -/
theorem cycle8_iso_radius_four_properties {V : Type*} {G : SimpleGraph V}
    [Fintype V] (e : G ≃g cycleGraph 8) :
    G.Connected ∧ StrongC4Free G ∧ radiusNat G = 4 ∧ inducedPathOrder G = 7 := by
  have hc : G.Connected := by
    have hr : ∀ u v : V, G.Reachable u v := by
      intro u v
      have h := (connected_cycleGraph_add_one (n := 7)) (e u) (e v)
      simpa using h.map e.symm.toHom
    have hn : Nonempty V := ⟨e.symm 0⟩
    exact ⟨hr⟩
  refine ⟨hc, ?_, ?_, ?_⟩
  · rintro ⟨f⟩
    apply cycle8_strongC4Free
    exact ⟨e.toCopy.comp f⟩
  · unfold radiusNat
    rw [← graphIso_radius e]
    exact cycle8_radius
  · rw [inducedPathOrder_iso e]
    exact cycle8_inducedPathOrder

end InducedPaths
