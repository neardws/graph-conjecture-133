/- Public paper statements, including the completed two-triangle certificate proof. -/
module

public import InducedPaths.StatementsCore
public import InducedPaths.LemmaFiveNine

open SimpleGraph

@[expose] public section
namespace InducedPaths
variable {V : Type*} {G : SimpleGraph V}

/-- Lemma 5.9, including actual seed embeddings, executable loss semantics,
normalized ambient extensions, and checked induced-path witnesses at every node. -/
theorem lemma_5_9 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 7) (htri : 2 ≤ triangleCount G) :
    ∃ v, deletionLoss G v ≤ 3 :=
  lemma_5_9_proof hconn hC hp htri

end InducedPaths
