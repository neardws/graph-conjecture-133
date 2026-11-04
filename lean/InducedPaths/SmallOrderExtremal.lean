/-
Small-order cases of Theorem 3.6, independent of StatementsCore.
The finite search ranges over 2^(n choose 2) Boolean codes (at most 32768),
not over arbitrary n-by-n adjacency relations. Decoding completeness,
copy-test soundness, mass semantics, and isomorphism transport are proved
before using native_decide for the finite checks. No P6-free assumption
is necessary for these five orders.
-/
module

public import InducedPaths.CanonicalMass
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public meta import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public meta import Mathlib.Combinatorics.SimpleGraph.Star

open Finset SimpleGraph
open scoped SimpleGraph

@[expose] public section
namespace InducedPaths
namespace SmallOrder

/-- Independent Boolean choices only for the strict upper triangle. -/
abbrev EdgeSlot (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev Code (n : ℕ) := EdgeSlot n → Bool

def decode {n : ℕ} (b : Code n) : SimpleGraph (Fin n) where
  Adj i j := (∃ h : i < j, b ⟨(i,j), h⟩ = true) ∨
    (∃ h : j < i, b ⟨(j,i), h⟩ = true)
  symm := by constructor; intro i j h; exact h.symm
  loopless := by
    constructor
    intro i h
    rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact lt_irrefl i h

instance {n : ℕ} (b : Code n) : DecidableRel (decode b).Adj :=
  fun i j => inferInstanceAs (Decidable ((∃ h : i < j, b ⟨(i,j), h⟩ = true) ∨
    (∃ h : j < i, b ⟨(j,i), h⟩ = true)))

def encode {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Code n :=
  fun p => decide (G.Adj p.val.1 p.val.2)

@[simp] theorem decode_encode {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] : decode (encode G) = G := by
  ext i j
  simp only [decode, encode, decide_eq_true_eq]
  constructor
  · rintro (⟨_, h⟩ | ⟨_, h⟩)
    · exact h
    · exact h.symm
  · intro h
    rcases lt_or_gt_of_ne h.ne with hlt | hgt
    · exact Or.inl ⟨hlt, h⟩
    · exact Or.inr ⟨hgt, h.symm⟩

/-- A computable mass expression, justified by the strong-C4-free identity. -/
def score {n : ℕ} (b : Code n) : ℕ :=
  2 * (decode b).edgeFinset.card - 3 * ((decode b).cliqueFinset 3).card

theorem mass_eq_score {n : ℕ} (b : Code n) (h : StrongC4Free (decode b)) :
    neighbourhoodIndependenceSum (decode b) = score b :=
  strongC4Free_S_identity h

/-- Finite copy test, with the graph-theoretic transport proved separately. -/
def C4Free {n : ℕ} (b : Code n) : Prop :=
  ∀ f : Fin 4 → Fin n, Function.Injective f →
    ¬ ∀ i j, (cycleGraph 4).Adj i j → (decode b).Adj (f i) (f j)

instance {n : ℕ} (b : Code n) : Decidable (C4Free b) := by
  unfold C4Free Function.Injective
  infer_instance

theorem c4Free_iff {n : ℕ} (b : Code n) : C4Free b ↔ StrongC4Free (decode b) := by
  constructor
  · intro h ⟨f⟩
    exact h f f.injective (fun i j hij => f.toHom.map_adj hij)
  · intro h f hi hf
    exact h ⟨{ toHom := { toFun := f, map_rel' := fun {i j} => hf i j }, injective' := hi }⟩

/-- Isomorphism search over vertex permutations, not over adjacency matrices. -/
def IsoTo {n : ℕ} (b : Code n) (H : SimpleGraph (Fin n)) : Prop :=
  ∃ e : Equiv.Perm (Fin n), ∀ i j, (decode b).Adj i j ↔ H.Adj (e i) (e j)

instance {n : ℕ} (b : Code n) (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    Decidable (IsoTo b H) := by unfold IsoTo; infer_instance

theorem isoTo_iff {n : ℕ} (b : Code n) (H : SimpleGraph (Fin n)) :
    IsoTo b H ↔ Nonempty (decode b ≃g H) := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨{ toEquiv := e, map_rel_iff' := fun {i j} => (he i j).symm }⟩
  · rintro ⟨e⟩
    exact ⟨e.toEquiv, fun i j => e.map_rel_iff.symm⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem check2 : ∀ b : Code 2, (decode b).Connected → C4Free b →
    score b ≤ 2 ∧ (score b = 2 ↔ IsoTo b k2Graph) := by native_decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem check3 : ∀ b : Code 3, (decode b).Connected → C4Free b →
    score b ≤ 4 ∧ (score b = 4 ↔ IsoTo b p3Graph) := by native_decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem check4 : ∀ b : Code 4, (decode b).Connected → C4Free b →
    score b ≤ 6 ∧ (score b = 6 ↔ IsoTo b p4Graph ∨ IsoTo b clawGraph) := by
  native_decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem check5 : ∀ b : Code 5, (decode b).Connected → C4Free b →
    score b ≤ 10 ∧ (score b = 10 ↔ IsoTo b (cycleGraph 5)) := by native_decide

/-- The leaf example relabelled onto a computable six-element type. -/
def leaf6 : SimpleGraph (Fin 6) := c5PlusLeaf.comap (finSuccEquiv 5)

instance : DecidableRel leaf6.Adj := fun i j => by
  change Decidable (c5PlusLeaf.Adj (finSuccEquiv 5 i) (finSuccEquiv 5 j))
  unfold c5PlusLeaf addLeaf simpleOf
  cases finSuccEquiv 5 i <;> cases finSuccEquiv 5 j <;> dsimp <;> infer_instance

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem check6_forward : ∀ b : Code 6, C4Free b →
    score b ≤ 12 ∧ (score b = 12 → IsoTo b (cycleGraph 6) ∨ IsoTo b leaf6) := by
  native_decide

theorem leaf6_mass : neighbourhoodIndependenceSum leaf6 = 12 := by
  have ht : ∀ a b c, leaf6.Adj a b → leaf6.Adj b c → ¬ leaf6.Adj a c := by
    native_decide
  rw [mass_eq_degree_sum_of_no_triangle ht]
  native_decide

theorem check6 : ∀ b : Code 6, (decode b).Connected → C4Free b →
    score b ≤ 12 ∧ (score b = 12 ↔ IsoTo b (cycleGraph 6) ∨ IsoTo b leaf6) := by
  intro b _ hC
  obtain ⟨hle, he⟩ := check6_forward b hC
  refine ⟨hle, he, ?_⟩
  intro h
  rw [← mass_eq_score b ((c4Free_iff b).mp hC)]
  rcases h with h | h
  · obtain ⟨e⟩ := (isoTo_iff b _).mp h
    rw [neighbourhoodIndependenceSum_iso e, cycle6_mass]
  · obtain ⟨e⟩ := (isoTo_iff b _).mp h
    rw [neighbourhoodIndependenceSum_iso e, leaf6_mass]

/-- Relabel any finite graph without inspecting or enumerating all binary relations. -/
def relabel {V : Type*} {n : ℕ} (G : SimpleGraph V) (e : Fin n ≃ V) :
    SimpleGraph (Fin n) := G.comap e

instance decidableRelabel {V : Type*} {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) : DecidableRel (relabel G e).Adj :=
  fun i j => inferInstanceAs (Decidable (G.Adj (e i) (e j)))

def relabelIso {V : Type*} {n : ℕ} (G : SimpleGraph V) (e : Fin n ≃ V) :
    relabel G e ≃g G := { toEquiv := e, map_rel_iff' := Iff.rfl }

/-- Generic soundness bridge from a checked code theorem to arbitrary vertex types. -/
theorem transfer {V : Type*} [Fintype V] {n m : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (e : Fin n ≃ V) (H : SimpleGraph (Fin n))
    (hc : ∀ b : Code n, (decode b).Connected → C4Free b →
      score b ≤ m ∧ (score b = m ↔ IsoTo b H))
    (hconn : G.Connected) (hC : StrongC4Free G) :
    neighbourhoodIndependenceSum G ≤ m ∧
      (neighbourhoodIndependenceSum G = m ↔ Nonempty (G ≃g H)) := by
  let K := relabel G e
  letI : DecidableRel K.Adj := decidableRelabel G e
  let b := encode K
  have hb : decode b = K := decode_encode K
  let iso := relabelIso G e
  have hconnK : K.Connected := iso.connected_iff.mpr hconn
  have hCK : StrongC4Free K := by
    intro h
    exact hC (h.trans iso.isContained)
  have hCb : C4Free b := (c4Free_iff b).mpr (hb ▸ hCK)
  have hmass : neighbourhoodIndependenceSum G = score b := by
    rw [← neighbourhoodIndependenceSum_iso iso]
    change neighbourhoodIndependenceSum K = score b
    rw [← hb]
    exact mass_eq_score b ((c4Free_iff b).mp hCb)
  obtain ⟨hle, heq⟩ := hc b (hb ▸ hconnK) hCb
  rw [hmass]
  refine ⟨hle, heq.trans ?_⟩
  rw [isoTo_iff, hb]
  exact ⟨fun ⟨f⟩ => ⟨iso.symm.trans f⟩, fun ⟨f⟩ => ⟨iso.trans f⟩⟩

/-- The same soundness bridge for a two-member equality list. -/
theorem transferTwo {V : Type*} [Fintype V] {n m : ℕ} (G : SimpleGraph V)
    [DecidableRel G.Adj] (e : Fin n ≃ V) (H J : SimpleGraph (Fin n))
    (hc : ∀ b : Code n, (decode b).Connected → C4Free b →
      score b ≤ m ∧ (score b = m ↔ IsoTo b H ∨ IsoTo b J))
    (hconn : G.Connected) (hC : StrongC4Free G) :
    neighbourhoodIndependenceSum G ≤ m ∧
      (neighbourhoodIndependenceSum G = m ↔
        Nonempty (G ≃g H) ∨ Nonempty (G ≃g J)) := by
  let K := relabel G e
  letI : DecidableRel K.Adj := decidableRelabel G e
  let b := encode K
  have hb : decode b = K := decode_encode K
  let iso := relabelIso G e
  have hconnK : K.Connected := iso.connected_iff.mpr hconn
  have hCK : StrongC4Free K := fun h => hC (h.trans iso.isContained)
  have hCb : C4Free b := (c4Free_iff b).mpr (hb ▸ hCK)
  have hmass : neighbourhoodIndependenceSum G = score b := by
    rw [← neighbourhoodIndependenceSum_iso iso]
    change neighbourhoodIndependenceSum K = score b
    rw [← hb]
    exact mass_eq_score b ((c4Free_iff b).mp hCb)
  obtain ⟨hle, heq⟩ := hc b (hb ▸ hconnK) hCb
  rw [hmass]
  refine ⟨hle, heq.trans ?_⟩
  have hi (L : SimpleGraph (Fin n)) : IsoTo b L ↔ Nonempty (G ≃g L) := by
    rw [isoTo_iff, hb]
    exact ⟨fun ⟨f⟩ => ⟨iso.symm.trans f⟩, fun ⟨f⟩ => ⟨iso.trans f⟩⟩
  exact or_congr (hi H) (hi J)

end SmallOrder

/-- The order-two bound and its complete equality classification. -/
theorem small_order_two {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : Fintype.card V = 2)
    (hconn : G.Connected) (hC : StrongC4Free G) :
    neighbourhoodIndependenceSum G ≤ 2 ∧
      (neighbourhoodIndependenceSum G = 2 ↔ Nonempty (G ≃g k2Graph)) := by
  classical
  let e : Fin 2 ≃ V := (Fintype.equivFinOfCardEq hn).symm
  exact SmallOrder.transfer G e k2Graph SmallOrder.check2 hconn hC

/-- The order-three bound and its complete equality classification. -/
theorem small_order_three {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : Fintype.card V = 3)
    (hconn : G.Connected) (hC : StrongC4Free G) :
    neighbourhoodIndependenceSum G ≤ 4 ∧
      (neighbourhoodIndependenceSum G = 4 ↔ Nonempty (G ≃g p3Graph)) := by
  classical
  let e : Fin 3 ≃ V := (Fintype.equivFinOfCardEq hn).symm
  exact SmallOrder.transfer G e p3Graph SmallOrder.check3 hconn hC

/-- The order-five bound and its complete equality classification. -/
theorem small_order_five {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : Fintype.card V = 5)
    (hconn : G.Connected) (hC : StrongC4Free G) :
    neighbourhoodIndependenceSum G ≤ 10 ∧
      (neighbourhoodIndependenceSum G = 10 ↔ Nonempty (G ≃g cycleGraph 5)) := by
  classical
  let e : Fin 5 ≃ V := (Fintype.equivFinOfCardEq hn).symm
  exact SmallOrder.transfer G e (cycleGraph 5) SmallOrder.check5 hconn hC

/-- The order-four bound, with both tree equality cases. -/
theorem small_order_four {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : Fintype.card V = 4)
    (hconn : G.Connected) (hC : StrongC4Free G) :
    neighbourhoodIndependenceSum G ≤ 6 ∧
      (neighbourhoodIndependenceSum G = 6 ↔
        Nonempty (G ≃g p4Graph) ∨ Nonempty (G ≃g clawGraph)) := by
  classical
  let e : Fin 4 ≃ V := (Fintype.equivFinOfCardEq hn).symm
  exact SmallOrder.transferTwo G e p4Graph clawGraph SmallOrder.check4 hconn hC

/-- The order-six bound, with the cycle and pendant-cycle equality cases.
The stronger induced-P6-free assumption is not needed at these orders. -/
theorem small_order_six {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hn : Fintype.card V = 6)
    (hconn : G.Connected) (hC : StrongC4Free G) :
    neighbourhoodIndependenceSum G ≤ 12 ∧
      (neighbourhoodIndependenceSum G = 12 ↔
        Nonempty (G ≃g cycleGraph 6) ∨ Nonempty (G ≃g c5PlusLeaf)) := by
  classical
  let e : Fin 6 ≃ V := (Fintype.equivFinOfCardEq hn).symm
  have h := SmallOrder.transferTwo G e (cycleGraph 6) SmallOrder.leaf6
    SmallOrder.check6 hconn hC
  have iso : SmallOrder.leaf6 ≃g c5PlusLeaf :=
    { toEquiv := finSuccEquiv 5, map_rel_iff' := Iff.rfl }
  have hi : Nonempty (G ≃g SmallOrder.leaf6) ↔ Nonempty (G ≃g c5PlusLeaf) :=
    ⟨fun ⟨f⟩ => ⟨f.trans iso⟩, fun ⟨f⟩ => ⟨f.trans iso.symm⟩⟩
  simpa only [hi] using h

/-- Equality list restricted to the five small orders; independent of StatementsCore. -/
def IsSmallP6Extremal {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  match Fintype.card V with
  | 2 => Nonempty (G ≃g k2Graph)
  | 3 => Nonempty (G ≃g p3Graph)
  | 4 => Nonempty (G ≃g p4Graph) ∨ Nonempty (G ≃g clawGraph)
  | 5 => Nonempty (G ≃g cycleGraph 5)
  | 6 => Nonempty (G ≃g cycleGraph 6) ∨ Nonempty (G ≃g c5PlusLeaf)
  | _ => False

/-- The complete small-order density bound and equality classification for Theorem 3.6. -/
theorem small_order_density_classification {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hlo : 2 ≤ Fintype.card V) (hhi : Fintype.card V ≤ 6) :
    ell G ≤ extremalDensity (Fintype.card V) ∧
      (ell G = extremalDensity (Fintype.card V) ↔ IsSmallP6Extremal G) := by
  have hpos : (0 : ℚ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
  have helper (m : ℕ) (P : Prop)
      (h : neighbourhoodIndependenceSum G ≤ m ∧
        (neighbourhoodIndependenceSum G = m ↔ P)) :
      ell G ≤ (m : ℚ) / Fintype.card V ∧
        (ell G = (m : ℚ) / Fintype.card V ↔ P) := by
    unfold ell
    constructor
    · exact (div_le_div_iff_of_pos_right hpos).mpr (by exact_mod_cast h.1)
    · rw [div_left_inj' (ne_of_gt hpos)]
      exact (Nat.cast_inj (R := ℚ)).trans h.2
  interval_cases hn : Fintype.card V
  · convert helper 2 _ (small_order_two G hn hconn hC) using 1 <;>
      norm_num [IsSmallP6Extremal, extremalDensity, hn]
  · convert helper 4 _ (small_order_three G hn hconn hC) using 1 <;>
      norm_num [IsSmallP6Extremal, extremalDensity, hn]
  · convert helper 6 _ (small_order_four G hn hconn hC) using 1 <;>
      norm_num [IsSmallP6Extremal, extremalDensity, hn]
  · convert helper 10 _ (small_order_five G hn hconn hC) using 1 <;>
      norm_num [IsSmallP6Extremal, extremalDensity, hn]
  · convert helper 12 _ (small_order_six G hn hconn hC) using 1 <;>
      norm_num [IsSmallP6Extremal, extremalDensity, hn]

/-- In particular, no small-order graph reaches Petersen's mass density. -/
theorem small_order_mass_lt_three_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hlo : 2 ≤ Fintype.card V) (hhi : Fintype.card V ≤ 6) :
    neighbourhoodIndependenceSum G < 3 * Fintype.card V := by
  interval_cases hn : Fintype.card V
  · have h := (small_order_two G hn hconn hC).1; omega
  · have h := (small_order_three G hn hconn hC).1; omega
  · have h := (small_order_four G hn hconn hC).1; omega
  · have h := (small_order_five G hn hconn hC).1; omega
  · have h := (small_order_six G hn hconn hC).1; omega

end InducedPaths
