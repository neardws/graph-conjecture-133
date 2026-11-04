module

public import InducedPaths.C6Trace
public meta import Mathlib.Data.Fintype.Defs
public meta import Mathlib.Combinatorics.SimpleGraph.CycleGraph

open scoped SimpleGraph
open SimpleGraph

@[expose] public section
namespace InducedPaths

/-- The local trace types relevant to the radius-four classification. -/
def HexLocalTrace (t : Fin 6 → Bool) : Prop :=
  (∃ i, ∀ j, t j = true ↔ j = i) ∨
  (∃ i, ∀ j, t j = true ↔ j = i ∨ j = i + 1) ∨
  (∃ i, ∀ j, t j = true ↔ j = i ∨ j = i + 3)

instance (t : Fin 6 → Bool) : Decidable (HexLocalTrace t) :=
  inferInstanceAs (Decidable ((_ : Prop) ∨ _ ∨ _))

theorem hexRadius_trace_certificate : ∀ t : Fin 6 → Bool,
    (∃ i, t i = true) → (∀ i, ¬ (t i = true ∧ t (i + 2) = true)) →
    HexLocalTrace t := by native_decide

/-- Strong C₄-freeness alone gives precisely the three possible nonempty
traces; unlike the P₆-free trace lemma, singleton and edge traces remain. -/
theorem hexRadius_trace_types {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 6 ↪g G)
    {w : V} (hw : ∀ i, c i ≠ w) (hne : ∃ i, G.Adj w (c i)) :
    (∃ i, ∀ j, G.Adj w (c j) ↔ j = i) ∨
    (∃ i, ∀ j, G.Adj w (c j) ↔ j = i ∨ j = i + 1) ∨
    (∃ i, ∀ j, G.Adj w (c j) ↔ j = i ∨ j = i + 3) := by
  classical
  let t : Fin 6 → Bool := fun i => decide (G.Adj w (c i))
  have ht : ∃ i, t i = true := by simpa [t] using hne
  have htwo : ∀ i, ¬ (t i = true ∧ t (i + 2) = true) := by
    simpa [t] using hexTrace_no_distance_two hC c hw
  simpa [HexLocalTrace, t] using hexRadius_trace_certificate t ht htwo

/-- If one cycle vertex reaches the whole dominating cycle within two steps,
it reaches the entire graph within three. -/
theorem hexRadius_eccent_le_three {V : Type*} {G : SimpleGraph V}
    (c : cycleGraph 6 ↪g G) (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i))
    (i : Fin 6) (hcycle : ∀ j, G.edist (c i) (c j) ≤ 2) :
    G.eccent (c i) ≤ 3 := by
  rw [eccent_le_iff]
  intro v
  obtain ⟨j, rfl | hj⟩ := hdom v
  · exact (hcycle j).trans (by decide)
  · calc
      G.edist (c i) v ≤ G.edist (c i) (c j) + G.edist (c j) v := G.edist_triangle
      _ ≤ 2 + 1 := add_le_add (hcycle j) (hj.symm.toWalk.edist_le.trans (by simp))
      _ = 3 := by decide

/-- A radius of at least four excludes any vertex of eccentricity at most three. -/
theorem hexRadius_not_eccent_le_three {V : Type*} {G : SimpleGraph V}
    [Fintype V] (hr : 4 ≤ radiusNat G) (v : V) : ¬ G.eccent v ≤ 3 := by
  intro hv
  have hrad : G.radius ≤ 3 := G.radius_le_eccent.trans hv
  have hn : radiusNat G ≤ 3 := ENat.toNat_le_toNat hrad (by simp)
  omega

/-- An antipodal contact would make its endpoint a centre of eccentricity
at most three, independently of any induced-path restriction. -/
theorem hexRadius_no_antipodal {V : Type*} {G : SimpleGraph V}
    [Fintype V] (hr : 4 ≤ radiusNat G)
    (c : cycleGraph 6 ↪g G) (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i))
    {w : V} (i : Fin 6) : ¬ (G.Adj w (c i) ∧ G.Adj w (c (i + 3))) := by
  rintro ⟨ha, hb⟩
  apply hexRadius_not_eccent_le_three hr (c i)
  apply hexRadius_eccent_le_three c hdom i
  intro j
  have hfin : ∀ i j : Fin 6, i = j ∨ (cycleGraph 6).Adj i j ∨ j = i + 3 ∨
      ∃ k, (cycleGraph 6).Adj i k ∧ (cycleGraph 6).Adj k j := by native_decide
  rcases hfin i j with h | h | h | ⟨k, h₁, h₂⟩
  · subst j; simp
  · exact ((c.map_rel_iff).2 h).toWalk.edist_le.trans (by simp)
  · subst j
    let p := ha.symm.toWalk.append hb.toWalk
    exact p.edist_le.trans (by simp [p])
  · let p := ((c.map_rel_iff).2 h₁).toWalk.append ((c.map_rel_iff).2 h₂).toWalk
    exact p.edist_le.trans (by simp [p])

/-- Every external vertex of a dominating hexagon at radius at least four
has either a singleton trace or a trace on a cycle edge. -/
theorem hexRadius_local_traces {V : Type*} {G : SimpleGraph V}
    [Fintype V] (hC : StrongC4Free G) (hr : 4 ≤ radiusNat G)
    (c : cycleGraph 6 ↪g G) (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i))
    {w : V} (hw : ∀ i, c i ≠ w) :
    (∃ i, ∀ j, G.Adj w (c j) ↔ j = i) ∨
    (∃ i, ∀ j, G.Adj w (c j) ↔ j = i ∨ j = i + 1) := by
  obtain ⟨a, ha⟩ := hdom w
  have hwa := ha.resolve_left (hw a).symm
  rcases hexRadius_trace_types hC c hw ⟨a, hwa⟩ with hs | he | ⟨i, hi⟩
  · exact Or.inl hs
  · exact Or.inr he
  · exact False.elim (hexRadius_no_antipodal hr c hdom i
      ⟨(hi i).2 (Or.inl rfl), (hi (i + 3)).2 (Or.inr rfl)⟩)

/-- A route of at most two edges on the hexagon. -/
def hexRadiusNear (i j : Fin 6) : Prop :=
  i = j ∨ (cycleGraph 6).Adj i j ∨
    ∃ k, (cycleGraph 6).Adj i k ∧ (cycleGraph 6).Adj k j

instance : DecidableRel hexRadiusNear := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem hexRadiusNear_edist {V : Type*} {G : SimpleGraph V}
    (c : cycleGraph 6 ↪g G) {i j : Fin 6} (h : hexRadiusNear i j) :
    G.edist (c i) (c j) ≤ 2 := by
  rcases h with h | h | ⟨k, ha, hb⟩
  · subst j; simp
  · exact ((c.map_rel_iff).2 h).toWalk.edist_le.trans (by simp)
  · let p := ((c.map_rel_iff).2 ha).toWalk.append ((c.map_rel_iff).2 hb).toWalk
    exact p.edist_le.trans (by simp [p])

/-- A local trace other than the singleton at `i` has a contact close to the
opposite cycle vertex. -/
theorem hexRadius_witness_certificate : ∀ (i : Fin 6) (t : Fin 6 → Bool),
    HexLocalTrace t → (¬ ∀ j, t j = true ↔ j = i) →
    ∃ j, t j = true ∧ hexRadiusNear (i + 3) j := by native_decide

/-- Every cycle vertex has a nonempty singleton attachment class. More
precisely, its class contains a vertex farther than three from the antipode,
which is the witness needed in the forbidden P₈ constructions. -/
theorem hexRadius_witness {V : Type*} {G : SimpleGraph V}
    [Fintype V] (hC : StrongC4Free G) (hr : 4 ≤ radiusNat G)
    (c : cycleGraph 6 ↪g G) (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i))
    (i : Fin 6) : ∃ w, (∀ j, c j ≠ w) ∧
      (∀ j, G.Adj w (c j) ↔ j = i) ∧ ¬ G.edist (c (i + 3)) w ≤ 3 := by
  classical
  have hnot := hexRadius_not_eccent_le_three hr (c (i + 3))
  rw [eccent_le_iff] at hnot
  push Not at hnot
  obtain ⟨w, hwfar⟩ := hnot
  have hcycle : ∀ j : Fin 6, G.edist (c (i + 3)) (c j) ≤ 3 := by
    intro j
    have hfin : ∀ a j : Fin 6, hexRadiusNear a j ∨
        ∃ k, hexRadiusNear a k ∧ (cycleGraph 6).Adj k j := by native_decide
    rcases hfin (i + 3) j with hn | ⟨k, hn, he⟩
    · exact (hexRadiusNear_edist c hn).trans (by decide)
    · calc
        G.edist (c (i + 3)) (c j) ≤ G.edist (c (i + 3)) (c k) + G.edist (c k) (c j) := G.edist_triangle
        _ ≤ 2 + 1 := add_le_add (hexRadiusNear_edist c hn)
          (((c.map_rel_iff).2 he).toWalk.edist_le.trans (by simp))
        _ = 3 := by decide
  have hout : ∀ j, c j ≠ w := by
    intro j hj
    exact (not_le_of_gt hwfar) (hj ▸ hcycle j)
  refine ⟨w, hout, ?_, not_le_of_gt hwfar⟩
  by_contra htrace
  obtain ⟨a, ha⟩ := hdom w
  have hwa := ha.resolve_left (hout a).symm
  let t : Fin 6 → Bool := fun j => decide (G.Adj w (c j))
  have hlocal : HexLocalTrace t := by
    simpa [HexLocalTrace, t] using hexRadius_trace_types hC c hout ⟨a, hwa⟩
  have hnotsingle : ¬ ∀ j, t j = true ↔ j = i := by simpa [t] using htrace
  obtain ⟨j, hj, hnear⟩ := hexRadius_witness_certificate i t hlocal hnotsingle
  have hwj : G.Adj w (c j) := by simpa [t] using hj
  apply (not_le_of_gt hwfar)
  calc
    G.edist (c (i + 3)) w ≤ G.edist (c (i + 3)) (c j) + G.edist (c j) w := G.edist_triangle
    _ ≤ 2 + 1 := add_le_add (hexRadiusNear_edist c hnear)
      (hwj.symm.toWalk.edist_le.trans (by simp))
    _ = 3 := by decide

/-- A distance-four witness has no external neighbour with a different
attachment class. This supplies all witness non-edges in the paper's P₈s. -/
theorem hexRadius_witness_neighbours {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 6 ↪g G)
    (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i))
    (i : Fin 6) {w : V} (hw : ∀ j, c j ≠ w)
    (htrace : ∀ j, G.Adj w (c j) ↔ j = i)
    (hfar : ¬ G.edist (c (i + 3)) w ≤ 3)
    {z : V} (hz : ∀ j, c j ≠ z) (hwz : G.Adj w z) :
    ∀ j, G.Adj z (c j) ↔ j = i := by
  have hcontact : ∀ j, G.Adj z (c j) → j = i := by
    intro j hzj
    by_contra hji
    have hfin : ∀ i j : Fin 6, j ≠ i →
        (cycleGraph 6).Adj i j ∨ j = i + 3 ∨ (cycleGraph 6).Adj (i + 3) j := by native_decide
    rcases hfin i j hji with hadj | heq | hadj
    · exact hC (fourCycle_isContained ((htrace i).2 rfl) ((c.map_rel_iff).2 hadj)
        hzj.symm hwz.symm (hw j).symm (hz i))
    · subst j
      apply hfar
      let p := hzj.symm.toWalk.append hwz.symm.toWalk
      exact p.edist_le.trans (by simp [p]; decide)
    · apply hfar
      let p := (((c.map_rel_iff).2 hadj).toWalk.append hzj.symm.toWalk).append hwz.symm.toWalk
      exact p.edist_le.trans (by simp [p])
  obtain ⟨a, ha⟩ := hdom z
  have hza : G.Adj z (c a) := ha.resolve_left (hz a).symm
  have hai : a = i := hcontact a hza
  intro j
  constructor
  · exact hcontact j
  · intro hji
    simpa [hai, hji] using hza

/-- Distinct singleton classes are disjoint, simply by their traces. -/
theorem hexRadius_singleton_disjoint {V : Type*} {G : SimpleGraph V}
    (c : cycleGraph 6 ↪g G) {i j : Fin 6} (hij : i ≠ j) :
    Disjoint {w | ∀ k, G.Adj w (c k) ↔ k = i}
      {w | ∀ k, G.Adj w (c k) ↔ k = j} := by
  rw [Set.disjoint_left]
  intro w hi hj
  exact hij ((hj i).1 ((hi i).2 rfl))

/-- Neighbourhood matching gives the matching condition inside each singleton
class before any P₈ exclusions are needed. -/
theorem hexRadius_singleton_matching {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 6 ↪g G) (i : Fin 6)
    {v w w' : V} (hv : G.Adj v (c i)) (hw : G.Adj w (c i))
    (hw' : G.Adj w' (c i)) (hvw : G.Adj v w) (hvw' : G.Adj v w') : w' = w := by
  have hne : v ≠ c i := hv.ne
  exact commonNeighbors_subsingleton hC hne ⟨hvw', hw'.symm⟩ ⟨hvw, hw.symm⟩

/-- At most one external vertex has a given cycle-edge trace. -/
theorem hexRadius_edge_unique {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 6 ↪g G) (i : Fin 6)
    {v w : V} (hv : G.Adj v (c i)) (hv' : G.Adj v (c (i + 1)))
    (hw : G.Adj w (c i)) (hw' : G.Adj w (c (i + 1))) : v = w := by
  have hfin : ∀ i : Fin 6, i ≠ i + 1 := by native_decide
  exact commonNeighbors_subsingleton hC (fun h => hfin i (c.injective h))
    ⟨hv.symm, hv'.symm⟩ ⟨hw.symm, hw'.symm⟩

/-- Two singleton classes on adjacent cycle vertices have no cross edge. -/
theorem hexRadius_no_adjacent_cross {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 6 ↪g G) {i j : Fin 6}
    (hij : (cycleGraph 6).Adj i j) {x y : V}
    (hx : ∀ k, c k ≠ x) (hy : ∀ k, c k ≠ y)
    (hxi : G.Adj x (c i)) (hyj : G.Adj y (c j)) : ¬ G.Adj x y := by
  intro hxy
  exact hC (fourCycle_isContained hxi ((c.map_rel_iff).2 hij) hyj.symm hxy.symm
    (hx j).symm (hy i))

/-- A trace code is a singleton (`false`) or a consecutive pair (`true`). -/
def hexAttachContact (p : Bool × Fin 6) (j : Fin 6) : Prop :=
  j = p.2 ∨ (p.1 = true ∧ j = p.2 + 1)

instance (p : Bool × Fin 6) (j : Fin 6) : Decidable (hexAttachContact p j) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The cycle with two adjacent external vertices. Used to identify all cases
already ruled out by strong C₄-freeness. -/
def hexPairAdj (p q : Bool × Fin 6) : Fin 8 → Fin 8 → Prop := fun a b =>
  if ha : a.val < 6 then
    if hb : b.val < 6 then (cycleGraph 6).Adj ⟨a.val, ha⟩ ⟨b.val, hb⟩
    else if b = 6 then hexAttachContact p ⟨a.val, ha⟩ else hexAttachContact q ⟨a.val, ha⟩
  else if hb : b.val < 6 then
    if a = 6 then hexAttachContact p ⟨b.val, hb⟩ else hexAttachContact q ⟨b.val, hb⟩
  else a ≠ b

instance (p q : Bool × Fin 6) : DecidableRel (hexPairAdj p q) := fun a b => by
  unfold hexPairAdj
  infer_instance

/-- A finite witness to a four-cycle among the cycle and a candidate edge. -/
def hexPairFourCycle (p q : Bool × Fin 6) : Prop :=
  ∃ a b c d : Fin 8, a ≠ c ∧ b ≠ d ∧ hexPairAdj p q a b ∧
    hexPairAdj p q b c ∧ hexPairAdj p q c d ∧ hexPairAdj p q d a

instance (p q : Bool × Fin 6) : Decidable (hexPairFourCycle p q) :=
  inferInstanceAs (Decidable (∃ _ _ _ _ : Fin 8, _))

/-- The only legal external edge joins singleton vertices in the same class.
This purely finite case split produces the two pairs of cycle vertices used
in the paper's displayed P₈s for every case not excluded by a C₄. -/
def hexPairPathOK (p q : Bool × Fin 6) (a b c d : Fin 6) : Prop :=
  a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
  (cycleGraph 6).Adj a b ∧ (cycleGraph 6).Adj c d ∧
  ¬ (cycleGraph 6).Adj a c ∧ ¬ (cycleGraph 6).Adj a d ∧
  ¬ (cycleGraph 6).Adj b c ∧ ¬ (cycleGraph 6).Adj b d ∧
  (∀ k, (k = a ∨ k = b ∨ k = c ∨ k = d) →
    (hexAttachContact p k ↔ k = b) ∧ (hexAttachContact q k ↔ k = c)) ∧
  ¬ hexAttachContact p a ∧ ¬ hexAttachContact q a ∧
  ¬ hexAttachContact p d ∧ ¬ hexAttachContact q d

instance (p q : Bool × Fin 6) (a b c d : Fin 6) : Decidable (hexPairPathOK p q a b c d) := by
  unfold hexPairPathOK
  infer_instance

theorem hexPair_certificate : ∀ p q : Bool × Fin 6,
    (p.1 = false ∧ q.1 = false ∧ p.2 = q.2) ∨ hexPairFourCycle p q ∨
    ∃ a b c d, hexPairPathOK p q a b c d := by native_decide

/-- Realization of the eight-vertex cycle-plus-edge template. -/
def hexPairMap {V : Type*} {G : SimpleGraph V} (c : cycleGraph 6 ↪g G)
    (x y : V) (k : Fin 8) : V :=
  if h : k.val < 6 then c ⟨k.val, h⟩ else if k = 6 then x else y

theorem hexPairMap_injective {V : Type*} {G : SimpleGraph V}
    (c : cycleGraph 6 ↪g G) {x y : V} (hx : ∀ i, c i ≠ x)
    (hy : ∀ i, c i ≠ y) (hxy : x ≠ y) : Function.Injective (hexPairMap c x y) := by
  intro a b hab
  unfold hexPairMap at hab
  split_ifs at hab with ha hb h6 h6' hb h6' <;> try omega
  · have h := congrArg Fin.val (c.injective hab)
    exact Fin.ext h
  all_goals first
    | exact False.elim (hx _ hab)
    | exact False.elim (hy _ hab)
    | exact False.elim (hx _ hab.symm)
    | exact False.elim (hy _ hab.symm)
    | exact False.elim (hxy hab)
    | exact False.elim (hxy hab.symm)

theorem hexPairMap_adj {V : Type*} {G : SimpleGraph V}
    (c : cycleGraph 6 ↪g G) {x y : V} (p q : Bool × Fin 6)
    (hxp : ∀ i, G.Adj x (c i) ↔ hexAttachContact p i)
    (hyq : ∀ i, G.Adj y (c i) ↔ hexAttachContact q i)
    (hxy : G.Adj x y) (a b : Fin 8) :
    G.Adj (hexPairMap c x y a) (hexPairMap c x y b) ↔ hexPairAdj p q a b := by
  unfold hexPairMap hexPairAdj
  split_ifs <;> simp_all [c.map_rel_iff, adj_comm]
  all_goals omega

/-- A finite four-cycle certificate lifts to a forbidden subgraph in the host. -/
theorem hexPair_no_fourCycle {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 6 ↪g G)
    {x y : V} (hx : ∀ i, c i ≠ x) (hy : ∀ i, c i ≠ y)
    (p q : Bool × Fin 6)
    (hxp : ∀ i, G.Adj x (c i) ↔ hexAttachContact p i)
    (hyq : ∀ i, G.Adj y (c i) ↔ hexAttachContact q i)
    (hxy : G.Adj x y) : ¬ hexPairFourCycle p q := by
  rintro ⟨a, b, d, e, had, hbe, hab, hbd, hde, hea⟩
  have hf := hexPairMap_injective c hx hy hxy.ne
  apply hC
  exact fourCycle_isContained
    ((hexPairMap_adj c p q hxp hyq hxy a b).2 hab)
    ((hexPairMap_adj c p q hxp hyq hxy b d).2 hbd)
    ((hexPairMap_adj c p q hxp hyq hxy d e).2 hde)
    ((hexPairMap_adj c p q hxp hyq hxy e a).2 hea)
    (fun h => had (hf h)) (fun h => hbe (hf h))

/-- The path used for every surviving bad edge: two witnesses, four cycle
vertices, and the two ends of the bad edge. -/
def hexPairPath (a b d e : Fin 6) : Fin 8 → Fin 10 :=
  ![8, ⟨a.val, by omega⟩, ⟨b.val, by omega⟩, 6, 7,
    ⟨d.val, by omega⟩, ⟨e.val, by omega⟩, 9]

/-- Adjacency of the ten-vertex template, with witness neighbourhoods confined
to their own singleton classes. -/
def hexWitnessAdj (p q : Bool × Fin 6) (a e : Fin 6) (u v : Fin 10) : Prop :=
  if hu : u.val < 8 then
    if hv : v.val < 8 then hexPairAdj p q ⟨u.val, hu⟩ ⟨v.val, hv⟩
    else if v = 8 then u.val = a.val else u.val = e.val
  else if _hv : v.val < 8 then
    if u = 8 then v.val = a.val else v.val = e.val
  else False

instance (p q : Bool × Fin 6) (a e : Fin 6) : DecidableRel (hexWitnessAdj p q a e) :=
  fun u v => by unfold hexWitnessAdj; infer_instance

/-- This certificate checks every chord and every distinctness condition in
all of the paper's forbidden paths at once. -/
theorem hexWitness_path_certificate : ∀ (p q : Bool × Fin 6) (a b d e : Fin 6),
    hexPairPathOK p q a b d e →
    Function.Injective (hexPairPath a b d e) ∧
    ∀ u v, hexWitnessAdj p q a e (hexPairPath a b d e u) (hexPairPath a b d e v) ↔
      (pathGraph 8).Adj u v := by native_decide

/-- Two different trace codes define different neighbourhoods. -/
theorem hexAttachContact_injective : ∀ p q : Bool × Fin 6,
    (∀ j, hexAttachContact p j ↔ hexAttachContact q j) → p = q := by native_decide

/-- The external vertices needed by a forbidden-path certificate have pairwise
different traces. -/
theorem hexPairPathOK_trace_distinct : ∀ (p q : Bool × Fin 6) (a b d e : Fin 6),
    hexPairPathOK p q a b d e →
    (false, a) ≠ p ∧ (false, a) ≠ q ∧ (false, e) ≠ p ∧
    (false, e) ≠ q ∧ a ≠ e := by native_decide

/-- Different trace codes force different vertices, without requiring the
vertices to lie outside the cycle. -/
theorem hexRadius_trace_ne {V : Type*} {G : SimpleGraph V}
    (c : cycleGraph 6 ↪g G) {x y : V} {p q : Bool × Fin 6} (hpq : p ≠ q)
    (hx : ∀ j, G.Adj x (c j) ↔ hexAttachContact p j)
    (hy : ∀ j, G.Adj y (c j) ↔ hexAttachContact q j) : x ≠ y := by
  intro h
  subst y
  exact hpq (hexAttachContact_injective p q (fun j => (hx j).symm.trans (hy j)))

/-- A distance-four witness is nonadjacent to any external vertex whose trace
is not its singleton class. -/
theorem hexRadius_witness_nonadjacent {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) (c : cycleGraph 6 ↪g G)
    (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i))
    {i : Fin 6} {w z : V} (hw : ∀ j, c j ≠ w)
    (htrace : ∀ j, G.Adj w (c j) ↔ j = i)
    (hfar : ¬ G.edist (c (i + 3)) w ≤ 3) (hz : ∀ j, c j ≠ z)
    {p : Bool × Fin 6} (hztrace : ∀ j, G.Adj z (c j) ↔ hexAttachContact p j)
    (hp : p ≠ (false, i)) : ¬ G.Adj w z := by
  intro hwz
  have hs := hexRadius_witness_neighbours hC c hdom i hw htrace hfar hz hwz
  apply hp
  apply hexAttachContact_injective
  intro j
  simpa [hexAttachContact] using (hztrace j).symm.trans (hs j)

/-- Realization of the ten-vertex forbidden-path template. -/
def hexWitnessMap {V : Type*} {G : SimpleGraph V} (c : cycleGraph 6 ↪g G)
    (x y wa we : V) : Fin 10 → V :=
  ![c 0, c 1, c 2, c 3, c 4, c 5, x, y, wa, we]

theorem hexWitnessMap_injective {V : Type*} {G : SimpleGraph V}
    (c : cycleGraph 6 ↪g G) {x y wa we : V}
    (hx : ∀ i, c i ≠ x) (hy : ∀ i, c i ≠ y)
    (hwa : ∀ i, c i ≠ wa) (hwe : ∀ i, c i ≠ we)
    (hxy : x ≠ y) (hax : wa ≠ x) (hay : wa ≠ y)
    (hex : we ≠ x) (hey : we ≠ y) (hae : wa ≠ we) :
    Function.Injective (hexWitnessMap c x y wa we) := by
  intro u v huv
  fin_cases u <;> fin_cases v <;>
    simp_all [hexWitnessMap, c.injective.eq_iff, Ne.symm]

theorem hexWitnessMap_adj {V : Type*} {G : SimpleGraph V}
    (c : cycleGraph 6 ↪g G) {x y wa we : V}
    (p q : Bool × Fin 6) (a e : Fin 6)
    (hxp : ∀ i, G.Adj x (c i) ↔ hexAttachContact p i)
    (hyq : ∀ i, G.Adj y (c i) ↔ hexAttachContact q i)
    (hat : ∀ i, G.Adj wa (c i) ↔ i = a)
    (het : ∀ i, G.Adj we (c i) ↔ i = e)
    (hxy : G.Adj x y) (hax : ¬ G.Adj wa x) (hay : ¬ G.Adj wa y)
    (hex : ¬ G.Adj we x) (hey : ¬ G.Adj we y) (hae : ¬ G.Adj wa we)
    (u v : Fin 10) :
    G.Adj (hexWitnessMap c x y wa we u) (hexWitnessMap c x y wa we v) ↔
      hexWitnessAdj p q a e u v := by
  have hax' : ¬ G.Adj x wa := fun h => hax h.symm
  have hay' : ¬ G.Adj y wa := fun h => hay h.symm
  have hex' : ¬ G.Adj x we := fun h => hex h.symm
  have hey' : ¬ G.Adj y we := fun h => hey h.symm
  fin_cases u <;> fin_cases v <;>
    simp [hexWitnessMap, hexWitnessAdj, hexPairAdj, hxp, hyq, hat, het,
      c.map_rel_iff, adj_comm, hxy, hax', hay', hex', hey', hae, Fin.ext_iff] <;>
    first | decide | omega

/-- Every external edge joins two vertices with the same singleton trace.
This is the core edge-classification step of the forward direction. -/
theorem hexRadius_external_edge {V : Type*} {G : SimpleGraph V}
    [Fintype V] (hC : StrongC4Free G) (hp : IsPkFree G 8) (hr : 4 ≤ radiusNat G)
    (c : cycleGraph 6 ↪g G) (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i))
    {x y : V} (hx : ∀ i, c i ≠ x) (hy : ∀ i, c i ≠ y)
    (p q : Bool × Fin 6)
    (hxp : ∀ i, G.Adj x (c i) ↔ hexAttachContact p i)
    (hyq : ∀ i, G.Adj y (c i) ↔ hexAttachContact q i)
    (hxy : G.Adj x y) : p.1 = false ∧ q.1 = false ∧ p.2 = q.2 := by
  classical
  rcases hexPair_certificate p q with hgood | hfour | ⟨a, b, d, e, hpath⟩
  · exact hgood
  · exact False.elim (hexPair_no_fourCycle hC c hx hy p q hxp hyq hxy hfour)
  · exfalso
    obtain ⟨wa, hwa, hat, haf⟩ := hexRadius_witness hC hr c hdom a
    obtain ⟨we, hwe, het, hef⟩ := hexRadius_witness hC hr c hdom e
    obtain ⟨hap, haq, hep, heq, hae⟩ := hexPairPathOK_trace_distinct p q a b d e hpath
    have hat' : ∀ i, G.Adj wa (c i) ↔ hexAttachContact (false, a) i := by simpa [hexAttachContact] using hat
    have het' : ∀ i, G.Adj we (c i) ↔ hexAttachContact (false, e) i := by simpa [hexAttachContact] using het
    have hax := hexRadius_trace_ne c hap hat' hxp
    have hay := hexRadius_trace_ne c haq hat' hyq
    have hex := hexRadius_trace_ne c hep het' hxp
    have hey := hexRadius_trace_ne c heq het' hyq
    have haene : wa ≠ we := hexRadius_trace_ne c (by simpa using hae) hat' het'
    have hnax := hexRadius_witness_nonadjacent hC c hdom hwa hat haf hx hxp hap.symm
    have hnay := hexRadius_witness_nonadjacent hC c hdom hwa hat haf hy hyq haq.symm
    have hnex := hexRadius_witness_nonadjacent hC c hdom hwe het hef hx hxp hep.symm
    have hney := hexRadius_witness_nonadjacent hC c hdom hwe het hef hy hyq heq.symm
    have hnae : ¬ G.Adj wa we := hexRadius_witness_nonadjacent hC c hdom hwa hat haf hwe het'
      (by simpa using hae.symm)
    have hf := hexWitnessMap_injective c hx hy hwa hwe hxy.ne hax hay hex hey haene
    obtain ⟨hinj, hrel⟩ := hexWitness_path_certificate p q a b d e hpath
    apply hp
    exact ⟨{
      toEmbedding := ⟨hexWitnessMap c x y wa we ∘ hexPairPath a b d e, hf.comp hinj⟩
      map_rel_iff' := by
        intro u v
        exact (hexWitnessMap_adj c p q a e hxp hyq hat het hxy hnax hnay hnex hney hnae _ _).trans (hrel u v)
    }⟩

/-- Every external vertex has a singleton/edge code. -/
theorem hexRadius_trace_code {V : Type*} {G : SimpleGraph V}
    [Fintype V] (hC : StrongC4Free G) (hr : 4 ≤ radiusNat G)
    (c : cycleGraph 6 ↪g G) (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i))
    {w : V} (hw : ∀ i, c i ≠ w) :
    ∃ p : Bool × Fin 6, ∀ j, G.Adj w (c j) ↔ hexAttachContact p j := by
  rcases hexRadius_local_traces hC hr c hdom hw with ⟨i, hi⟩ | ⟨i, hi⟩
  · exact ⟨(false, i), by simpa [hexAttachContact] using hi⟩
  · exact ⟨(true, i), by simpa [hexAttachContact] using hi⟩

/-- The attachment sets are defined intrinsically by their singleton traces. -/
def hexRadiusAttach {V : Type*} {G : SimpleGraph V} (c : cycleGraph 6 ↪g G)
    (i : Fin 6) : Set V := {w | (∀ j, c j ≠ w) ∧ ∀ j, G.Adj w (c j) ↔ j = i}

/-- Construction data for every graph satisfying the forward hypotheses and
possessing a dominating induced hexagon. -/
noncomputable def radiusFourExtension_of_dominating_hexagon {V : Type*} {G : SimpleGraph V}
    [Fintype V] (hC : StrongC4Free G) (hp : IsPkFree G 8) (hr : 4 ≤ radiusNat G)
    (c : cycleGraph 6 ↪g G) (hdom : ∀ v, ∃ i, v = c i ∨ G.Adj v (c i)) :
    RadiusFourExtension G := by
  classical
  let edgeSet : Fin 6 → Set V := fun i => {w | (∀ j, c j ≠ w) ∧
    ∀ j, G.Adj w (c j) ↔ hexAttachContact (true, i) j}
  let edge : Fin 6 → Option V := fun i => if h : (edgeSet i).Nonempty then some h.choose else none
  have hedge : ∀ i w, edge i = some w ↔ w ∈ edgeSet i := by
    intro i w
    dsimp [edge]
    split_ifs with h
    · constructor
      · intro hw
        have heq : h.choose = w := Option.some.inj hw
        exact heq ▸ h.choose_spec
      · intro hw
        have ht₁ := h.choose_spec.2
        have ht₂ := hw.2
        have heq : h.choose = w := hexRadius_edge_unique hC c i
          ((ht₁ i).2 (by simp [hexAttachContact]))
          ((ht₁ (i + 1)).2 (by simp [hexAttachContact]))
          ((ht₂ i).2 (by simp [hexAttachContact]))
          ((ht₂ (i + 1)).2 (by simp [hexAttachContact]))
        exact congrArg some heq
    · simp only [false_iff]
      exact fun hw => h ⟨w, hw⟩
  refine {
    cycleEmb := c.toEmbedding
    cycle_induced := fun i j => c.map_rel_iff
    attach := hexRadiusAttach c
    attach_nonempty := ?_
    attach_off_cycle := ?_
    attach_pairwise := ?_
    trace := ?_
    no_cross := ?_
    matching := ?_
    no_extra_attach := ?_
    edgeVert := edge
    edge_off_cycle := ?_
    edge_off_attach := ?_
    edge_inj := ?_
    edge_adj := ?_
    exhaustive := ?_
  }
  · intro i
    obtain ⟨w, hw, ht, _⟩ := hexRadius_witness hC hr c hdom i
    exact ⟨w, hw, ht⟩
  · intro i w hw
    exact hw.1
  · intro i j hij
    rw [Set.disjoint_left]
    intro w hi hj
    exact hij ((hj.2 i).1 ((hi.2 i).2 rfl))
  · intro i w hw
    exact hw.2
  · intro i j hij x hx y hy hxy
    have htx : ∀ k, G.Adj x (c k) ↔ hexAttachContact (false, i) k := by simpa [hexAttachContact] using hx.2
    have hty : ∀ k, G.Adj y (c k) ↔ hexAttachContact (false, j) k := by simpa [hexAttachContact] using hy.2
    exact hij (hexRadius_external_edge hC hp hr c hdom hx.1 hy.1 _ _ htx hty hxy).2.2
  · intro i v hv w hw hvw w' hw' hvw'
    exact hexRadius_singleton_matching hC c i ((hv.2 i).2 rfl)
      ((hw.2 i).2 rfl) ((hw'.2 i).2 rfl) hvw hvw'
  · intro i v w hv hvw
    by_cases hw : ∃ j, c j = w
    · obtain ⟨j, rfl⟩ := hw
      exact Or.inl (congrArg c ((hv.2 j).1 hvw))
    · have hwout : ∀ j, c j ≠ w := by simpa using hw
      obtain ⟨p, ht⟩ := hexRadius_trace_code hC hr c hdom hwout
      have hvtrace : ∀ k, G.Adj v (c k) ↔ hexAttachContact (false, i) k := by simpa [hexAttachContact] using hv.2
      obtain ⟨_, hpfalse, hip⟩ := hexRadius_external_edge hC hp hr c hdom hv.1 hwout _ p hvtrace ht hvw
      refine Or.inr ⟨hwout, ?_⟩
      simpa [hexAttachContact, hpfalse, ← hip] using ht
  · intro i w hw
    exact ((hedge i w).1 hw).1
  · intro i v j w hv hw heq
    have hvtrace := ((hedge i v).1 hv).2
    have hwtrace : ∀ k, G.Adj w (c k) ↔ hexAttachContact (false, j) k := by simpa [hexAttachContact] using hw.2
    have hcode := hexAttachContact_injective (true, i) (false, j)
      (fun k => (hvtrace k).symm.trans (heq ▸ hwtrace k))
    exact Bool.noConfusion (congrArg Prod.fst hcode)
  · intro i j w hi hj
    have hti := ((hedge i w).1 hi).2
    have htj := ((hedge j w).1 hj).2
    exact congrArg Prod.snd (hexAttachContact_injective (true, i) (true, j)
      (fun k => (hti k).symm.trans (htj k)))
  · intro i v hv w
    have hvdata := (hedge i v).1 hv
    constructor
    · intro hvw
      by_cases hw : ∃ j, c j = w
      · obtain ⟨j, rfl⟩ := hw
        have hj := (hvdata.2 j).1 hvw
        simpa [hexAttachContact] using hj
      · have hwout : ∀ j, c j ≠ w := by simpa using hw
        obtain ⟨p, ht⟩ := hexRadius_trace_code hC hr c hdom hwout
        have hbad := (hexRadius_external_edge hC hp hr c hdom hvdata.1 hwout (true, i) p hvdata.2 ht hvw).1
        exact Bool.noConfusion hbad
    · rintro (rfl | rfl)
      · exact (hvdata.2 i).2 (by simp [hexAttachContact])
      · exact (hvdata.2 (i + 1)).2 (by simp [hexAttachContact])
  · intro v
    by_cases hv : ∃ i, c i = v
    · exact Or.inl hv
    · have hout : ∀ i, c i ≠ v := by simpa using hv
      rcases hexRadius_local_traces hC hr c hdom hout with ⟨i, hi⟩ | ⟨i, hi⟩
      · exact Or.inr (Or.inl ⟨i, hout, hi⟩)
      · refine Or.inr (Or.inr ⟨i, (hedge i v).2 ⟨hout, ?_⟩⟩)
        simpa [hexAttachContact] using hi

end InducedPaths
