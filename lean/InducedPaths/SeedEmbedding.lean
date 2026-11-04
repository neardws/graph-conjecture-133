/-
The four two-triangle certificate rows as induced graph embeddings.
This module intentionally does not import Statements.
-/
module

public import InducedPaths.Basic
public import InducedPaths.Certificate

set_option maxHeartbeats 1000000

@[expose] public section

namespace InducedPaths

open SimpleGraph

/-- The order-five shared-vertex seed, with adjacency read from the actual
certificate bit masks (rather than from a separately specified edge list). -/
def sharedSeedGraph : SimpleGraph (Fin 5) where
  Adj i j := Certificate.edge (Certificate.seed 0) i.val j.val = true
  symm.symm := by decide
  loopless.irrefl := by decide

lemma sharedSeedGraph_adj (i j : Fin 5) :
    sharedSeedGraph.Adj i j ↔
      (i = 0 ∧ j ≠ 0) ∨ (j = 0 ∧ i ≠ 0) ∨
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
      (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) := by
  change Certificate.edge (Certificate.seed 0) i.val j.val = true ↔ _
  revert i j
  decide

/-- Two triangles sharing exactly their hub induce the distance-zero seed in a
strongly `C₄`-free graph. The four inequalities assert that the other vertices of
the triangles are disjoint; all remaining distinctness follows from adjacency. -/
def sharedSeedEmbedding {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) {u a b c d : V}
    (hT1 : G.Adj u a ∧ G.Adj a b ∧ G.Adj b u)
    (hT2 : G.Adj u c ∧ G.Adj c d ∧ G.Adj d u)
    (hcross : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) :
    sharedSeedGraph ↪g G := by
  have hac : ¬ G.Adj a c := by
    intro h
    exact hC (fourCycle_isContained h hT2.2.1 hT2.2.2 hT1.1
      hcross.2.1 hT2.1.ne.symm)
  have had : ¬ G.Adj a d := by
    intro h
    exact hC (fourCycle_isContained h hT2.2.1.symm hT2.1.symm hT1.1
      hcross.1 hT2.2.2.ne)
  have hbc : ¬ G.Adj b c := by
    intro h
    exact hC (fourCycle_isContained h hT2.2.1 hT2.2.2 hT1.2.2.symm
      hcross.2.2.2 hT2.1.ne.symm)
  have hbd : ¬ G.Adj b d := by
    intro h
    exact hC (fourCycle_isContained h hT2.2.1.symm hT2.1.symm hT1.2.2.symm
      hcross.2.2.1 hT2.2.2.ne)
  have hua : u ≠ a := hT1.1.ne
  have hub : u ≠ b := hT1.2.2.ne.symm
  have hab : a ≠ b := hT1.2.1.ne
  have huc : u ≠ c := hT2.1.ne
  have hud : u ≠ d := hT2.2.2.ne.symm
  have hcd : c ≠ d := hT2.2.1.ne
  let f : Fin 5 → V
    | 0 => u
    | 1 => a
    | 2 => b
    | 3 => c
    | 4 => d
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, G.adj_comm]
  · intro i j
    change G.Adj (f i) (f j) ↔ sharedSeedGraph.Adj i j
    fin_cases i <;> fin_cases j <;>
      simp [sharedSeedGraph_adj, f, hT1.1, hT1.2.1, hT1.2.2,
        hT1.2.2.symm, hT2.1, hT2.2.1, hT2.2.2, hT2.2.2.symm,
        hac, had, hbc, hbd, G.adj_comm]

/-- The shared-vertex configuration contains the actual certificate's
order-five seed as an induced subgraph. -/
theorem sharedSeed_isIndContained {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) {u a b c d : V}
    (hT1 : G.Adj u a ∧ G.Adj a b ∧ G.Adj b u)
    (hT2 : G.Adj u c ∧ G.Adj c d ∧ G.Adj d u)
    (hcross : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) :
    sharedSeedGraph ⊴ G :=
  (sharedSeedEmbedding hC hT1 hT2 hcross).isIndContained

/-- The distance-one row, read directly from the certificate. -/
def adjacentSeedGraph : SimpleGraph (Fin 6) where
  Adj i j := Certificate.edge (Certificate.seed 1) i.val j.val = true
  symm.symm := by decide
  loopless.irrefl := by decide

lemma adjacentSeedGraph_adj (i j : Fin 6) :
    adjacentSeedGraph.Adj i j ↔
      (i < 3 ∧ j < 3 ∧ i ≠ j) ∨ (3 ≤ i ∧ 3 ≤ j ∧ i ≠ j) ∨
      (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) := by
  change Certificate.edge (Certificate.seed 1) i.val j.val = true ↔ _
  revert i j
  decide

/-- Disjoint triangles joined by an edge induce the distance-one certificate
seed: any additional cross edge would create a (not necessarily induced) `C₄`. -/
def adjacentSeedEmbedding {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) {u a b v c e : V}
    (hT1 : G.Adj u a ∧ G.Adj a b ∧ G.Adj b u)
    (hT2 : G.Adj v c ∧ G.Adj c e ∧ G.Adj e v)
    (hdisj : ({u, a, b} : Set V) ∩ {v, c, e} = ∅)
    (huv : G.Adj u v) : adjacentSeedGraph ↪g G := by
  have hsep {x y : V} (hx : x ∈ ({u, a, b} : Set V))
      (hy : y ∈ ({v, c, e} : Set V)) : x ≠ y := by
    intro hxy
    simpa [hdisj] using
      (show x ∈ ({u, a, b} : Set V) ∩ {v, c, e} from ⟨hx, hxy ▸ hy⟩)
  have huv_ne : u ≠ v := hsep (by simp) (by simp)
  have huc_ne : u ≠ c := hsep (by simp) (by simp)
  have hue_ne : u ≠ e := hsep (by simp) (by simp)
  have hav_ne : a ≠ v := hsep (by simp) (by simp)
  have hac_ne : a ≠ c := hsep (by simp) (by simp)
  have hae_ne : a ≠ e := hsep (by simp) (by simp)
  have hbv_ne : b ≠ v := hsep (by simp) (by simp)
  have hbc_ne : b ≠ c := hsep (by simp) (by simp)
  have hbe_ne : b ≠ e := hsep (by simp) (by simp)
  have huc : ¬ G.Adj u c := fun h =>
    hC (fourCycle_isContained h hT2.2.1 hT2.2.2 huv.symm hue_ne hT2.1.ne.symm)
  have hue : ¬ G.Adj u e := fun h =>
    hC (fourCycle_isContained h hT2.2.1.symm hT2.1.symm huv.symm huc_ne hT2.2.2.ne)
  have hav : ¬ G.Adj a v := fun h =>
    hC (fourCycle_isContained h.symm hT1.2.1 hT1.2.2 huv hbv_ne.symm hT1.1.ne.symm)
  have hbv : ¬ G.Adj b v := fun h =>
    hC (fourCycle_isContained h.symm hT1.2.1.symm hT1.1.symm huv hav_ne.symm hT1.2.2.ne)
  have hac : ¬ G.Adj a c := fun h =>
    hC (fourCycle_isContained h hT2.1.symm huv.symm hT1.1 hav_ne huc_ne.symm)
  have hae : ¬ G.Adj a e := fun h =>
    hC (fourCycle_isContained h hT2.2.2 huv.symm hT1.1 hav_ne hue_ne.symm)
  have hbc : ¬ G.Adj b c := fun h =>
    hC (fourCycle_isContained h hT2.1.symm huv.symm hT1.2.2.symm hbv_ne huc_ne.symm)
  have hbe : ¬ G.Adj b e := fun h =>
    hC (fourCycle_isContained h hT2.2.2 huv.symm hT1.2.2.symm hbv_ne hue_ne.symm)
  have hua : u ≠ a := hT1.1.ne
  have hub : u ≠ b := hT1.2.2.ne.symm
  have hab : a ≠ b := hT1.2.1.ne
  have hvc : v ≠ c := hT2.1.ne
  have hve : v ≠ e := hT2.2.2.ne.symm
  have hce : c ≠ e := hT2.2.1.ne
  let f : Fin 6 → V
    | 0 => u
    | 1 => a
    | 2 => b
    | 3 => v
    | 4 => c
    | 5 => e
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, G.adj_comm]
  · intro i j
    change G.Adj (f i) (f j) ↔ adjacentSeedGraph.Adj i j
    fin_cases i <;> fin_cases j <;>
      simp [adjacentSeedGraph_adj, f, hT1.1, hT1.2.1, hT1.2.2,
        hT1.2.2.symm, hT2.1, hT2.2.1, hT2.2.2, hT2.2.2.symm,
        huv, huc, hue, hav, hbv, hac, hae, hbc, hbe, G.adj_comm]

/-- The distance-two row, read directly from the certificate. -/
def distanceTwoSeedGraph : SimpleGraph (Fin 7) where
  Adj i j := Certificate.edge (Certificate.seed 2) i.val j.val = true
  symm.symm := by decide
  loopless.irrefl := by decide

lemma distanceTwoSeedGraph_adj (i j : Fin 7) :
    distanceTwoSeedGraph.Adj i j ↔
      (i < 3 ∧ j < 3 ∧ i ≠ j) ∨ (4 ≤ i ∧ 4 ≤ j ∧ i ≠ j) ∨
      (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
      (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) := by
  change Certificate.edge (Certificate.seed 2) i.val j.val = true ↔ _
  revert i j
  decide

/-- A length-two connecting path between triangles with no cross edges induces
exactly the certificate's distance-two seed. -/
def distanceTwoSeedEmbedding {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) {u a b v c e p : V}
    (hT1 : G.Adj u a ∧ G.Adj a b ∧ G.Adj b u)
    (hT2 : G.Adj v c ∧ G.Adj c e ∧ G.Adj e v)
    (hdisj : ({u, a, b} : Set V) ∩ {v, c, e} = ∅)
    (hcross : ∀ x ∈ ({u, a, b} : Set V), ∀ y ∈ ({v, c, e} : Set V), ¬ G.Adj x y)
    (hup : G.Adj u p) (hpv : G.Adj p v) : distanceTwoSeedGraph ↪g G := by
  have hsep {x y : V} (hx : x ∈ ({u, a, b} : Set V))
      (hy : y ∈ ({v, c, e} : Set V)) : x ≠ y := by
    intro hxy
    simpa [hdisj] using
      (show x ∈ ({u, a, b} : Set V) ∩ {v, c, e} from ⟨hx, hxy ▸ hy⟩)
  have huv_ne : u ≠ v := hsep (by simp) (by simp)
  have huc_ne : u ≠ c := hsep (by simp) (by simp)
  have hue_ne : u ≠ e := hsep (by simp) (by simp)
  have hav_ne : a ≠ v := hsep (by simp) (by simp)
  have hac_ne : a ≠ c := hsep (by simp) (by simp)
  have hae_ne : a ≠ e := hsep (by simp) (by simp)
  have hbv_ne : b ≠ v := hsep (by simp) (by simp)
  have hbc_ne : b ≠ c := hsep (by simp) (by simp)
  have hbe_ne : b ≠ e := hsep (by simp) (by simp)
  have huv : ¬ G.Adj u v := hcross u (by simp) v (by simp)
  have huc : ¬ G.Adj u c := hcross u (by simp) c (by simp)
  have hue : ¬ G.Adj u e := hcross u (by simp) e (by simp)
  have hav : ¬ G.Adj a v := hcross a (by simp) v (by simp)
  have hac : ¬ G.Adj a c := hcross a (by simp) c (by simp)
  have hae : ¬ G.Adj a e := hcross a (by simp) e (by simp)
  have hbv : ¬ G.Adj b v := hcross b (by simp) v (by simp)
  have hbc : ¬ G.Adj b c := hcross b (by simp) c (by simp)
  have hbe : ¬ G.Adj b e := hcross b (by simp) e (by simp)
  have hpa_ne : p ≠ a := by intro h; exact hav (h ▸ hpv)
  have hpb_ne : p ≠ b := by intro h; exact hbv (h ▸ hpv)
  have hpc_ne : p ≠ c := by intro h; exact huc (h ▸ hup)
  have hpe_ne : p ≠ e := by intro h; exact hue (h ▸ hup)
  have hap : ¬ G.Adj a p := fun h =>
    hC (fourCycle_isContained hT1.2.2 hup h.symm hT1.2.1 hpb_ne.symm hT1.1.ne)
  have hbp : ¬ G.Adj b p := fun h =>
    hC (fourCycle_isContained hT1.1.symm hup h.symm hT1.2.1.symm hpa_ne.symm hT1.2.2.ne.symm)
  have hcp : ¬ G.Adj c p := fun h =>
    hC (fourCycle_isContained hT2.2.2 hpv.symm h.symm hT2.2.1 hpe_ne.symm hT2.1.ne)
  have hep : ¬ G.Adj e p := fun h =>
    hC (fourCycle_isContained hT2.1.symm hpv.symm h.symm hT2.2.1.symm hpc_ne.symm hT2.2.2.ne.symm)
  have hua : u ≠ a := hT1.1.ne
  have hub : u ≠ b := hT1.2.2.ne.symm
  have hab : a ≠ b := hT1.2.1.ne
  have hvc : v ≠ c := hT2.1.ne
  have hve : v ≠ e := hT2.2.2.ne.symm
  have hce : c ≠ e := hT2.2.1.ne
  have hup_ne : u ≠ p := hup.ne
  have hpv_ne : p ≠ v := hpv.ne
  clear hcross hsep
  let f : Fin 7 → V
    | 0 => u
    | 1 => a
    | 2 => b
    | 3 => p
    | 4 => v
    | 5 => c
    | 6 => e
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, G.adj_comm]
  · intro i j
    change G.Adj (f i) (f j) ↔ distanceTwoSeedGraph.Adj i j
    fin_cases i <;> fin_cases j <;>
      simp [distanceTwoSeedGraph_adj, f, hT1.1, hT1.2.1, hT1.2.2,
        hT1.2.2.symm, hT2.1, hT2.2.1, hT2.2.2, hT2.2.2.symm,
        hup, hpv, hpv.symm, huv, huc, hue, hav, hbv, hac, hae, hbc, hbe,
        hap, hbp, hcp, hep, G.adj_comm]

/-- The distance-three row, read directly from the certificate. -/
def distanceThreeSeedGraph : SimpleGraph (Fin 8) where
  Adj i j := Certificate.edge (Certificate.seed 3) i.val j.val = true
  symm.symm := by decide
  loopless.irrefl := by decide

lemma distanceThreeSeedGraph_adj (i j : Fin 8) :
    distanceThreeSeedGraph.Adj i j ↔
      (i < 3 ∧ j < 3 ∧ i ≠ j) ∨ (5 ≤ i ∧ 5 ≤ j ∧ i ≠ j) ∨
      (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
      (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
      (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) := by
  change Certificate.edge (Certificate.seed 3) i.val j.val = true ↔ _
  revert i j
  decide

/-- A shortest length-three connection induces the distance-three seed. The
nonedge hypotheses state the consequences of shortestness that are needed;
`C₄`-freeness rules out the four remaining possible chords at the triangles. -/
def distanceThreeSeedEmbedding {V : Type*} {G : SimpleGraph V}
    (hC : StrongC4Free G) {u a b v c e p q : V}
    (hT1 : G.Adj u a ∧ G.Adj a b ∧ G.Adj b u)
    (hT2 : G.Adj v c ∧ G.Adj c e ∧ G.Adj e v)
    (hdisj : ({u, a, b} : Set V) ∩ {v, c, e} = ∅)
    (hcross : ∀ x ∈ ({u, a, b} : Set V), ∀ y ∈ ({v, c, e} : Set V), ¬ G.Adj x y)
    (hleft : ∀ x ∈ ({u, a, b} : Set V), ¬ G.Adj x q)
    (hright : ∀ y ∈ ({v, c, e} : Set V), ¬ G.Adj p y)
    (hup : G.Adj u p) (hpq : G.Adj p q) (hqv : G.Adj q v) :
    distanceThreeSeedGraph ↪g G := by
  have hsep {x y : V} (hx : x ∈ ({u, a, b} : Set V))
      (hy : y ∈ ({v, c, e} : Set V)) : x ≠ y := by
    intro hxy
    simpa [hdisj] using
      (show x ∈ ({u, a, b} : Set V) ∩ {v, c, e} from ⟨hx, hxy ▸ hy⟩)
  have huv_ne : u ≠ v := hsep (by simp) (by simp)
  have huc_ne : u ≠ c := hsep (by simp) (by simp)
  have hue_ne : u ≠ e := hsep (by simp) (by simp)
  have hav_ne : a ≠ v := hsep (by simp) (by simp)
  have hac_ne : a ≠ c := hsep (by simp) (by simp)
  have hae_ne : a ≠ e := hsep (by simp) (by simp)
  have hbv_ne : b ≠ v := hsep (by simp) (by simp)
  have hbc_ne : b ≠ c := hsep (by simp) (by simp)
  have hbe_ne : b ≠ e := hsep (by simp) (by simp)
  have huv : ¬ G.Adj u v := hcross u (by simp) v (by simp)
  have huc : ¬ G.Adj u c := hcross u (by simp) c (by simp)
  have hue : ¬ G.Adj u e := hcross u (by simp) e (by simp)
  have hav : ¬ G.Adj a v := hcross a (by simp) v (by simp)
  have hac : ¬ G.Adj a c := hcross a (by simp) c (by simp)
  have hae : ¬ G.Adj a e := hcross a (by simp) e (by simp)
  have hbv : ¬ G.Adj b v := hcross b (by simp) v (by simp)
  have hbc : ¬ G.Adj b c := hcross b (by simp) c (by simp)
  have hbe : ¬ G.Adj b e := hcross b (by simp) e (by simp)
  have huq : ¬ G.Adj u q := hleft u (by simp)
  have haq : ¬ G.Adj a q := hleft a (by simp)
  have hbq : ¬ G.Adj b q := hleft b (by simp)
  have hpv : ¬ G.Adj p v := hright v (by simp)
  have hpc : ¬ G.Adj p c := hright c (by simp)
  have hpe : ¬ G.Adj p e := hright e (by simp)
  have hpa_ne : p ≠ a := by intro h; exact haq (h ▸ hpq)
  have hpb_ne : p ≠ b := by intro h; exact hbq (h ▸ hpq)
  have hqc_ne : q ≠ c := by intro h; exact hpc (h ▸ hpq)
  have hqe_ne : q ≠ e := by intro h; exact hpe (h ▸ hpq)
  have hap : ¬ G.Adj a p := fun h =>
    hC (fourCycle_isContained hT1.2.2 hup h.symm hT1.2.1 hpb_ne.symm hT1.1.ne)
  have hbp : ¬ G.Adj b p := fun h =>
    hC (fourCycle_isContained hT1.1.symm hup h.symm hT1.2.1.symm hpa_ne.symm hT1.2.2.ne.symm)
  have hcq : ¬ G.Adj c q := fun h =>
    hC (fourCycle_isContained hT2.2.2 hqv.symm h.symm hT2.2.1 hqe_ne.symm hT2.1.ne)
  have heq : ¬ G.Adj e q := fun h =>
    hC (fourCycle_isContained hT2.1.symm hqv.symm h.symm hT2.2.1.symm hqc_ne.symm hT2.2.2.ne.symm)
  have hua : u ≠ a := hT1.1.ne
  have hub : u ≠ b := hT1.2.2.ne.symm
  have hab : a ≠ b := hT1.2.1.ne
  have hvc : v ≠ c := hT2.1.ne
  have hve : v ≠ e := hT2.2.2.ne.symm
  have hce : c ≠ e := hT2.2.1.ne
  have hup_ne : u ≠ p := hup.ne
  have hpq_ne : p ≠ q := hpq.ne
  have hqv_ne : q ≠ v := hqv.ne
  have huq_ne : u ≠ q := by intro h; exact huv (h.symm ▸ hqv)
  have haq_ne : a ≠ q := by intro h; exact hav (h.symm ▸ hqv)
  have hbq_ne : b ≠ q := by intro h; exact hbv (h.symm ▸ hqv)
  have hpv_ne : p ≠ v := by intro h; exact huv (h ▸ hup)
  have hpc_ne : p ≠ c := by intro h; exact huc (h ▸ hup)
  have hpe_ne : p ≠ e := by intro h; exact hue (h ▸ hup)
  clear hcross hleft hright hsep
  let f : Fin 8 → V
    | 0 => u
    | 1 => a
    | 2 => b
    | 3 => p
    | 4 => q
    | 5 => v
    | 6 => c
    | 7 => e
  refine ⟨⟨f, ?_⟩, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f, G.adj_comm]
  · intro i j
    change G.Adj (f i) (f j) ↔ distanceThreeSeedGraph.Adj i j
    fin_cases i <;> fin_cases j <;>
      simp [distanceThreeSeedGraph_adj, f, hT1.1, hT1.2.1, hT1.2.2,
        hT1.2.2.symm, hT2.1, hT2.2.1, hT2.2.2, hT2.2.2.symm,
        hup, hpq, hqv, hqv.symm, huv, huc, hue, hav, hbv, hac, hae, hbc, hbe,
        huq, haq, hbq, hpv, hpc, hpe,
        (show ¬ G.Adj v p from fun h => hpv h.symm),
        (show ¬ G.Adj c p from fun h => hpc h.symm),
        (show ¬ G.Adj e p from fun h => hpe h.symm),
        hap, hbp, hcq, heq, G.adj_comm]

end InducedPaths
