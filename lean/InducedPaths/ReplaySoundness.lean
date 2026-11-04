/-
Abstract soundness of successful certificate replay.

This module does not identify bit-mask graphs with mathematical simple graphs.
It proves the generic bridge: a successful replay is a finite closing tree, and
no predicate with the stated deficient-vertex extension property can hold at its
root. Establishing that property for realizations in an actual graph requires
separate correctness results for `loss` and `extensions`.
-/
module

public import InducedPaths.Certificate

@[expose] public section

namespace InducedPaths.Certificate

/-- A finite semantic closing tree. A deficient vertex must be in range, and
*every* extension enumerated for that vertex must itself be closed. In
particular, a vertex with no enumerated extensions closes a leaf. -/
inductive Closed : List ℕ → Prop where
  | node {g : List ℕ} (c : ℕ)
      (inRange : c < g.length) (deficient : loss g c < 4)
      (children : ∀ k ∈ extensions g (1 <<< c), Closed k) : Closed g

/-- Consuming a list succeeds only if each child succeeds. This lemma deliberately
abstracts over the soundness of `go` at the fixed fuel. -/
theorem consume_closed_of_go_closed (fuel : ℕ)
    (sound : ∀ (g : List ℕ) (choices : List ℕ) (s : Replay) (rest : List ℕ),
      go g choices fuel = some (s, rest) → Closed g)
    (kids : List (List ℕ)) (choices : List ℕ) (s : Replay) (rest : List ℕ)
    (h : consume kids choices fuel = some (s, rest)) :
    ∀ k ∈ kids, Closed k := by
  induction kids generalizing choices s rest with
  | nil => simp
  | cons k ks ih =>
      cases hk : go k choices fuel with
      | none => simp [consume, hk] at h
      | some result =>
          rcases result with ⟨sk, cs⟩
          cases hs : consume ks cs fuel with
          | none => simp [consume, hk, hs] at h
          | some result =>
              rcases result with ⟨ss, rs⟩
              intro child hchild
              rcases List.mem_cons.mp hchild with heq | hmem
              · subst child
                exact sound k choices sk cs hk
              · exact ih cs ss rs hs child hmem

/-- Success at any fuel and with any unconsumed suffix gives a finite closing
proof. Neither exact consumption nor the replay statistics are needed. -/
theorem go_closed (g : List ℕ) (choices : List ℕ) (fuel : ℕ)
    (s : Replay) (rest : List ℕ)
    (h : go g choices fuel = some (s, rest)) : Closed g := by
  induction fuel generalizing g choices s rest with
  | zero => simp [go] at h
  | succ fuel ih =>
      cases choices with
      | nil => simp [go] at h
      | cons c cs =>
          by_cases hc : c < g.length
          · by_cases hl : loss g c < 4
            · cases hs : consume (extensions g (1 <<< c)) cs fuel with
              | none => simp [go, hc, hl, hs] at h
              | some result =>
                  rcases result with ⟨sub, suffix⟩
                  exact Closed.node c hc hl
                    (consume_closed_of_go_closed fuel ih
                      (extensions g (1 <<< c)) cs sub suffix hs)
            · simp [go, hc, hl] at h
          · simp [go, hc] at h

/-- Successful consumption closes every child in its input list. -/
theorem consume_closed (kids : List (List ℕ)) (choices : List ℕ) (fuel : ℕ)
    (s : Replay) (rest : List ℕ)
    (h : consume kids choices fuel = some (s, rest)) :
    ∀ k ∈ kids, Closed k :=
  consume_closed_of_go_closed fuel (fun g cs sub suffix => go_closed g cs fuel sub suffix)
    kids choices s rest h

/-- A successful complete certificate replay yields semantic closure. -/
theorem replay_closed (g : List ℕ) (choices : List ℕ) (s : Replay)
    (h : replay g choices = some s) : Closed g := by
  cases hg : go g choices (choices.length + 1) with
  | none => simp [replay, hg] at h
  | some result =>
      rcases result with ⟨sub, rest⟩
      exact go_closed g choices (choices.length + 1) sub rest hg

/-- The precise abstract obligation for a class of realizable mask graphs:
every deficient in-range vertex has at least one enumerated extension still
in that class. No correctness claim about the concrete graph checker is hidden
in this definition. -/
def ExtensionProperty (P : List ℕ → Prop) : Prop :=
  ∀ (g : List ℕ), P g → ∀ (c : ℕ), c < g.length → loss g c < 4 →
    ∃ k ∈ extensions g (1 <<< c), P k

/-- A finite closing tree rules out every property preserved by some child at
each deficient vertex. The argument is induction on the closing proof, not a
termination or finiteness assumption on the class described by `P`. -/
theorem Closed.not_property {P : List ℕ → Prop}
    (extend : ExtensionProperty P) {g : List ℕ} (closed : Closed g) : ¬ P g := by
  induction closed with
  | node c inRange deficient children ih =>
      intro hg
      obtain ⟨k, hk, hpk⟩ := extend _ hg c inRange deficient
      exact ih k hk hpk

/-- Abstract no-realization theorem for a successful replay. To use it for an
ambient mathematical graph, instantiate `P` with its realization relation and
prove `ExtensionProperty P` independently. -/
theorem replay_not_property {P : List ℕ → Prop}
    (extend : ExtensionProperty P) (g : List ℕ) (choices : List ℕ) (s : Replay)
    (h : replay g choices = some s) : ¬ P g :=
  (replay_closed g choices s h).not_property extend

/-- The four checked seed certificates exclude any class satisfying the abstract
extension obligation. This is not, by itself, a graph-theoretic seed exclusion. -/
theorem four_seeds_not_property {P : List ℕ → Prop}
    (extend : ExtensionProperty P) :
    ¬ P (seed 0) ∧ ¬ P (seed 1) ∧ ¬ P (seed 2) ∧ ¬ P (seed 3) := by
  rcases four_seed_replay with ⟨h0, h1, h2, h3⟩
  exact ⟨replay_not_property extend _ _ _ h0,
    replay_not_property extend _ _ _ h1,
    replay_not_property extend _ _ _ h2,
    replay_not_property extend _ _ _ h3⟩

end InducedPaths.Certificate
