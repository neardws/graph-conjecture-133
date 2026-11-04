/-
A closing tree annotated with the node-local checker correctness obligation.
This separates finite trace-witness checking from ambient graph semantics.
-/
module

public import InducedPaths.StatementsCore
public import InducedPaths.ExtensionSoundness
public import InducedPaths.MaskGraph
public import InducedPaths.IsoLoss
public import InducedPaths.ReplaySoundness
public import InducedPaths.RealizedLoss

@[expose] public section

namespace InducedPaths.Certificate

/-- A semantic closing tree carrying an additional invariant at every visited
node. The choice at each node is part of the proof, just as in `Closed`. -/
inductive AnnotatedClosed (Q : List ℕ → Prop) : List ℕ → Prop where
  | node {g : List ℕ} (c : ℕ) (inRange : c < g.length)
      (deficient : loss g c < 4) (annotation : Q g)
      (children : ∀ k ∈ extensions g (1 <<< c), AnnotatedClosed Q k) :
      AnnotatedClosed Q g

/-- Forgetting annotations leaves an ordinary semantic closing proof. -/
theorem AnnotatedClosed.closed {Q : List ℕ → Prop} {g : List ℕ}
    (h : AnnotatedClosed Q g) : Closed g := by
  induction h with
  | node c hc hl hq children ih => exact Closed.node c hc hl ih

/-- Annotations can be weakened independently at every node. -/
theorem AnnotatedClosed.map {Q R : List ℕ → Prop}
    (imp : ∀ g, Q g → R g) {g : List ℕ} (h : AnnotatedClosed Q g) :
    AnnotatedClosed R g := by
  induction h with
  | node c hc hl hq children ih => exact .node c hc hl (imp _ hq) ih

/-- Abstract no-realization induction with a node-local invariant and a
realization invariant. Normalization, for example, belongs in `P`, and the
finite trace-witness property belongs in `Q`. -/
theorem AnnotatedClosed.not_property {Q P : List ℕ → Prop}
    (extend : ∀ g, Q g → P g → ∀ c, c < g.length → loss g c < 4 →
      ∃ k ∈ extensions g (1 <<< c), P k)
    {g : List ℕ} (h : AnnotatedClosed Q g) : ¬ P g := by
  induction h with
  | node c hc hl hq children ih =>
    intro hp
    obtain ⟨k, hk, hpk⟩ := extend _ hq hp c hc hl
    exact ih k hk hpk

/-- The concrete annotation needed to turn this checker's closing tree into a
mathematical obstruction. No correctness of `componentList` is assumed. -/
abbrev WitnessClosed := AnnotatedClosed HasTracePathWitnesses

/-- Ambient extension step, with deficiency-to-outside-neighbour and mask
construction isolated as one explicit mathematical hypothesis. The rejection
checks and preservation of normalization are discharged by proved semantics. -/
theorem witnessClosed_not_realizes_of_extension {V : Type*} {G : SimpleGraph V}
    (hC : InducedPaths.StrongC4Free G) (hP7 : InducedPaths.IsPkFree G 7)
    (outside : ∀ (g : List ℕ) (r : Realizes G g) (c : Fin g.length),
      loss g c.val < 4 →
      ∃ (x : V) (m : ℕ), (∀ i, x ≠ r.vertices i) ∧ m < 2 ^ g.length ∧
        (∀ i : Fin g.length, m.testBit i.val = true ↔ G.Adj x (r.vertices i)) ∧
        G.Adj x (r.vertices c))
    {g : List ℕ} (closed : WitnessClosed g) (hg : Normalized g) :
    ¬ Nonempty (Realizes G g) := by
  have h := closed.not_property (P := fun k => Normalized k ∧ Nonempty (Realizes G k))
    (fun k hw ⟨hn, ⟨r⟩⟩ c hc hl => by
      let ci : Fin k.length := ⟨c, hc⟩
      obtain ⟨x, m, hx, hm, hmask, hxc⟩ := outside k r ci hl
      obtain ⟨hmem, hnorm, hreal⟩ :=
        actual_extension_of_traceWitnesses hw r hn hC hP7 x hx hm hmask ci hxc
      exact ⟨withNew k m, hmem, hnorm, hreal⟩)
  exact fun hr => h ⟨hg, hr⟩

/-- A witnessed closing tree has no realization in an ambient graph whose
vertices all have deletion loss at least four. This uses the actual executable
extension enumeration, with no abstract extension-preservation assumption. -/
theorem WitnessClosed.not_realizes {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : InducedPaths.StrongC4Free G) (hP7 : InducedPaths.IsPkFree G 7)
    (hlarge : ∀ v, 4 ≤ InducedPaths.deletionLoss G v)
    {g : List ℕ} (closed : WitnessClosed g) (hg : Normalized g) :
    ¬ Nonempty (Realizes G g) := by
  apply witnessClosed_not_realizes_of_extension hC hP7 ?_ closed hg
  intro k r c hc
  obtain ⟨x, hxc, hx⟩ := r.exists_neighbor_outside hC hlarge c hc
  exact ⟨x, ambientMask G r x, hx, ambientMask_lt_two_pow r x,
    ambientMask_testBit r x, hxc⟩

/-- Equivalently, any realized witnessed closing tree forces an actual ambient
vertex with deletion loss at most three. -/
theorem WitnessClosed.exists_loss_le_three {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hC : InducedPaths.StrongC4Free G) (hP7 : InducedPaths.IsPkFree G 7)
    {g : List ℕ} (closed : WitnessClosed g) (hg : Normalized g)
    (r : Realizes G g) : ∃ v, InducedPaths.deletionLoss G v ≤ 3 := by
  classical
  by_contra h
  have hlarge : ∀ v, 4 ≤ InducedPaths.deletionLoss G v := by
    intro v
    have hn : ¬ InducedPaths.deletionLoss G v ≤ 3 := fun hv => h ⟨v, hv⟩
    omega
  exact WitnessClosed.not_realizes hC hP7 hlarge closed hg ⟨r⟩

end InducedPaths.Certificate
