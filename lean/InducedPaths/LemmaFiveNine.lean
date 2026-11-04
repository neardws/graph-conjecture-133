/- The actual four-seed certificate argument for Lemma 5.9. -/
module

public import InducedPaths.SeedRealization
public import InducedPaths.TraceWitnessCheck

@[expose] public section

namespace InducedPaths

open SimpleGraph Certificate

private theorem seed0_normalized : Normalized (seed 0) := by
  unfold Normalized
  decide
private theorem seed1_normalized : Normalized (seed 1) := by
  unfold Normalized
  decide
private theorem seed2_normalized : Normalized (seed 2) := by
  unfold Normalized
  decide
private theorem seed3_normalized : Normalized (seed 3) := by
  unfold Normalized
  decide

private def realizes_seed0 {V : Type*} {G : SimpleGraph V}
    (e : sharedSeedGraph ↪g G) : Realizes G (seed 0) where
  vertices := e.toEmbedding
  adj_iff _ _ := e.map_rel_iff

private def realizes_seed1 {V : Type*} {G : SimpleGraph V}
    (e : adjacentSeedGraph ↪g G) : Realizes G (seed 1) where
  vertices := e.toEmbedding
  adj_iff _ _ := e.map_rel_iff

private def realizes_seed2 {V : Type*} {G : SimpleGraph V}
    (e : distanceTwoSeedGraph ↪g G) : Realizes G (seed 2) where
  vertices := e.toEmbedding
  adj_iff _ _ := e.map_rel_iff

private def realizes_seed3 {V : Type*} {G : SimpleGraph V}
    (e : distanceThreeSeedGraph ↪g G) : Realizes G (seed 3) where
  vertices := e.toEmbedding
  adj_iff _ _ := e.map_rel_iff

/-- The full four-seed replay proof of Lemma 5.9, including extraction of a
seed, actual mask-loss semantics, ambient extension semantics, and independently
checked induced-path witnesses at every replay node. -/
theorem lemma_5_9_proof {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (hconn : G.Connected)
    (hC : StrongC4Free G) (hp : IsPkFree G 7) (htri : 2 ≤ triangleCount G) :
    ∃ v, deletionLoss G v ≤ 3 := by
  rcases four_seeds_witnessClosed with ⟨h0, h1, h2, h3⟩
  rcases exists_certificate_seed_embedding hconn hC hp htri with
    he | he | he | he
  all_goals obtain ⟨e⟩ := he
  · exact WitnessClosed.exists_loss_le_three hC hp h0 seed0_normalized (realizes_seed0 e)
  · exact WitnessClosed.exists_loss_le_three hC hp h1 seed1_normalized (realizes_seed1 e)
  · exact WitnessClosed.exists_loss_le_three hC hp h2 seed2_normalized (realizes_seed2 e)
  · exact WitnessClosed.exists_loss_le_three hC hp h3 seed3_normalized (realizes_seed3 e)

end InducedPaths
