module
public import InducedPaths.Basic
public import InducedPaths.Graphs
public meta import Mathlib.Data.Fintype.Powerset
public meta import InducedPaths.Graphs
public meta import InducedPaths.Basic
set_option synthInstance.maxSize 100000
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
open Finset SimpleGraph
@[expose] public section
namespace InducedPaths
namespace SectionFiveGlobal

/-- An ordered induced path, including its injectivity certificate. -/
def PathCertificate {W : Type*} (H : SimpleGraph W) {k : ℕ} (f : Fin k → W) : Prop :=
  Function.Injective f ∧ ∀ i j, H.Adj (f i) (f j) ↔ (pathGraph k).Adj i j

instance {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] {k : ℕ} (f : Fin k → W) : Decidable (PathCertificate H f) :=
  inferInstanceAs (Decidable (Function.Injective f ∧ _))

def five (a b c d e : PetersenVertex) : Fin 5 → PetersenVertex :=
  ![a, b, c, d, e]

/-- Paper 1114: every nonedge of Petersen is the pair of ends of an induced P5. -/
theorem petersen_nonedge_P5 : ∀ a b : PetersenVertex,
    a ≠ b → ¬ petersenGraph.Adj a b →
    ∃ c d e : PetersenVertex, PathCertificate petersenGraph (five a c d e b) := by
  native_decide

/-- Paper 1116–1120, without choosing a labelling: an edge outside the closed
neighbourhood of the triangle edge starts an induced P5 avoiding that edge. -/
theorem petersen_remote_edge_P5 : ∀ u w a b : PetersenVertex,
    petersenGraph.Adj u w → petersenGraph.Adj a b →
    a ≠ u → a ≠ w → b ≠ u → b ≠ w →
    ¬ petersenGraph.Adj a u → ¬ petersenGraph.Adj a w →
    ¬ petersenGraph.Adj b u → ¬ petersenGraph.Adj b w →
    ∃ c d e : PetersenVertex,
      PathCertificate petersenGraph (five a b c d e) ∧
      ∀ i, five a b c d e i ≠ u ∧ five a b c d e i ≠ w := by
  native_decide

/-- Finite fact used in paper 1089: nonadjacent Petersen vertices have a common neighbour. -/
theorem petersen_common_neighbor : ∀ a b : PetersenVertex,
    a ≠ b → ¬ petersenGraph.Adj a b →
      ∃ c, petersenGraph.Adj a c ∧ petersenGraph.Adj b c := by
  native_decide

/-- Turn an ordered certificate into an actual induced embedding. -/
theorem PathCertificate.isIndContained {W : Type*} {H : SimpleGraph W}
    {k : ℕ} {f : Fin k → W} (h : PathCertificate H f) : pathGraph k ⊴ H :=
  ⟨{ toEmbedding := ⟨f, h.1⟩, map_rel_iff' := by intro i j; exact h.2 i j }⟩

/-- Every Petersen vertex is an end of a genuine induced P5. -/
theorem petersen_rooted_P5 (a : PetersenVertex) :
    ∃ f : pathGraph 5 ↪g petersenGraph, f 0 = a := by
  have h : ∀ a : PetersenVertex, ∃ b, a ≠ b ∧ ¬ petersenGraph.Adj a b := by
    native_decide
  obtain ⟨b, hab, hn⟩ := h a
  obtain ⟨c, d, e, hc⟩ := petersen_nonedge_P5 a b hab hn
  refine ⟨{ toEmbedding := ⟨five a c d e b, hc.1⟩
            map_rel_iff' := by intro i j; exact hc.2 i j }, ?_⟩
  simp [five]

end SectionFiveGlobal
end InducedPaths
