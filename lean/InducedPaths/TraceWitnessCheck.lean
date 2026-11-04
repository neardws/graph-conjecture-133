/-
Executable, witness-producing verification of the trace obligations at replay nodes.
The original trace and extension enumerators are used without modification.
-/
module

public import InducedPaths.CertificateExclusion
public meta import InducedPaths.Certificate
public meta import InducedPaths.ExtensionSoundness

@[expose] public section

namespace InducedPaths.Certificate

/-- Adjacency on old indices together with the new sentinel `g.length`. -/
def traceEdge (g : List ℕ) (attachment a b : ℕ) : Bool :=
  if a = g.length then
    if b = g.length then false else attachment.testBit b
  else if b = g.length then attachment.testBit a
  else edge g a b

/-- A bounded greedy walk. Its output is independently checked below. -/
def traceWalk (g : List ℕ) (attachment : ℕ) (verts : List ℕ) :
    ℕ → ℕ → List ℕ → List ℕ
  | 0, _, _ => []
  | fuel + 1, current, visited =>
      current :: match verts.find? (fun v =>
          traceEdge g attachment current v && !visited.contains v && v != current) with
        | none => []
        | some next => traceWalk g attachment verts fuel next (current :: visited)

/-- Start at an endpoint, then produce seven candidate vertices. -/
def traceCandidate (g : List ℕ) (sm attachment : ℕ) : Fin 7 → Option (Fin g.length) :=
  let verts := (List.range g.length).filter sm.testBit ++ [g.length]
  let start := (verts.find? fun v =>
    decide ((verts.filter (traceEdge g attachment v)).length = 1)).getD g.length
  let walk := traceWalk g attachment verts 7 start []
  fun k =>
    let v := walk.getD k.val g.length
    if h : v < g.length then some ⟨v, h⟩ else none

def checkTracePath (g : List ℕ) (sm attachment : ℕ) : Bool :=
  decide (ValidTracePath g sm attachment (traceCandidate g sm attachment))

theorem checkTracePath_sound {g : List ℕ} {sm attachment : ℕ}
    (h : checkTracePath g sm attachment = true) :
    Nonempty (TracePathWitness g sm attachment) := by
  have hp : ValidTracePath g sm attachment (traceCandidate g sm attachment) :=
    of_decide_eq_true h
  exact ⟨hp.witness⟩

/-- Check every attachment of every trace, retaining actual path witnesses. -/
def checkTraceWitnesses (g : List ℕ) : Bool :=
  (p7Traces g).all fun tr => tr.2.all (checkTracePath g tr.1)

theorem checkTraceWitnesses_sound {g : List ℕ}
    (h : checkTraceWitnesses g = true) : HasTracePathWitnesses g := by
  intro sm attachments hmem attachment ha
  exact checkTracePath_sound
    (List.all_eq_true.mp (List.all_eq_true.mp h (sm, attachments) hmem) attachment ha)

mutual
  /-- Replay the original children, additionally verifying every local trace. -/
  def witnessConsume (kids : List (List ℕ)) (choices : List ℕ) (fuel : ℕ) :
      Option (List ℕ) :=
    match kids with
    | [] => some choices
    | k :: ks => (witnessGo k choices fuel).bind fun rest =>
        witnessConsume ks rest fuel
  termination_by (fuel, 1, kids.length)

  def witnessGo (g : List ℕ) (choices : List ℕ) (fuel : ℕ) : Option (List ℕ) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match choices with
      | [] => none
      | c :: cs =>
        if decide (c < g.length) && decide (loss g c < 4) && checkTraceWitnesses g then
          witnessConsume (extensions g (1 <<< c)) cs fuel
        else none
  termination_by (fuel, 0, 0)
end

theorem witnessConsume_closed_of_go_closed (fuel : ℕ)
    (sound : ∀ g choices rest, witnessGo g choices fuel = some rest → WitnessClosed g)
    (kids : List (List ℕ)) (choices rest : List ℕ)
    (h : witnessConsume kids choices fuel = some rest) :
    ∀ k ∈ kids, WitnessClosed k := by
  induction kids generalizing choices rest with
  | nil => simp
  | cons k ks ih =>
      cases hk : witnessGo k choices fuel with
      | none => simp [witnessConsume, hk] at h
      | some suffix =>
          have hs : witnessConsume ks suffix fuel = some rest := by
            simpa [witnessConsume, hk] using h
          intro child hc
          rcases List.mem_cons.mp hc with heq | hm
          · subst child; exact sound k choices suffix hk
          · exact ih suffix rest hs child hm

theorem witnessGo_closed (g : List ℕ) (choices : List ℕ) (fuel : ℕ)
    (rest : List ℕ) (h : witnessGo g choices fuel = some rest) : WitnessClosed g := by
  induction fuel generalizing g choices rest with
  | zero => simp [witnessGo] at h
  | succ fuel ih =>
    cases choices with
    | nil => simp [witnessGo] at h
    | cons c cs =>
      by_cases hc : c < g.length
      · by_cases hl : loss g c < 4
        · by_cases hw : checkTraceWitnesses g = true
          · have hs : witnessConsume (extensions g (1 <<< c)) cs fuel = some rest := by
              simpa [witnessGo, hc, hl, hw] using h
            exact AnnotatedClosed.node c hc hl (checkTraceWitnesses_sound hw)
              (witnessConsume_closed_of_go_closed fuel ih _ cs rest hs)
          · simp [witnessGo, hc, hl, hw] at h
        · simp [witnessGo, hc, hl] at h
      · simp [witnessGo, hc] at h

/-- Finite evidence covers the original 36 + 31 + 46 + 5 replay nodes. -/
theorem four_seed_trace_checks :
    witnessGo (seed 0) choicesDist0 (choicesDist0.length + 1) = some [] ∧
    witnessGo (seed 1) choicesDist1 (choicesDist1.length + 1) = some [] ∧
    witnessGo (seed 2) choicesDist2 (choicesDist2.length + 1) = some [] ∧
    witnessGo (seed 3) choicesDist3 (choicesDist3.length + 1) = some [] := by
  native_decide

theorem four_seeds_witnessClosed :
    WitnessClosed (seed 0) ∧ WitnessClosed (seed 1) ∧
    WitnessClosed (seed 2) ∧ WitnessClosed (seed 3) := by
  rcases four_seed_trace_checks with ⟨h0, h1, h2, h3⟩
  exact ⟨witnessGo_closed _ _ _ _ h0, witnessGo_closed _ _ _ _ h1,
    witnessGo_closed _ _ _ _ h2, witnessGo_closed _ _ _ _ h3⟩

end InducedPaths.Certificate
