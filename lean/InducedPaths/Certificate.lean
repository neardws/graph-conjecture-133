/-
Fuel-bounded checker for the four distance rows of Lemma 5.9.

The walk is the depth-first preorder of `certificates/gen3/verify_gen3.py`: at the
current mask graph, the certificate names a vertex `v` with deletion loss `< 4`,
and the children are the neighbourhoods of a new vertex that contain `v`, create
no `C₄` through that vertex, and create no induced `P₇`. A `C₄` through the new
vertex is an old vertex with two neighbours in the chosen mask. The induced-`P₇`
test is the one in Appendix A: for each 6-set, reject a neighbourhood whose trace
is exactly one end of each path component of a 4-edge or 5-edge induced subgraph
of maximum degree at most 2.

Only the four two-triangle rows are represented. The obsolete one-triangle
certificate (`None` / pairs, 169 nodes) is not a hypothesis of Lemma 5.9.

`replay` is a total function. It returns `none` if the choice list is not a
complete legal traversal, including when a node would have to be unrestricted.
Success therefore forces unrestricted count 0. `four_seed_replay` evaluates the
four lists. That replay does not prove Lemma 5.9: the embedding of the seeds and
the comparison of mask-loss with `L(v)` are separate.
-/
module

public import Mathlib.Tactic.NormNum

namespace InducedPaths.Certificate

/-- Bit count. The fuel is the value itself, which is at least the number of bits. -/
def popcount (n : ℕ) : ℕ :=
  go n n
where
  go : ℕ → ℕ → ℕ
    | _, 0 => 0
    | 0, _ => 0
    | fuel + 1, m => if m = 0 then 0 else (m &&& 1) + go fuel (m >>> 1)

def edge (g : List ℕ) (a b : ℕ) : Bool :=
  Nat.testBit (g.getD a 0) b

def setEdge (g : List ℕ) (a b : ℕ) : List ℕ :=
  (List.range g.length).map fun i =>
    let row := g.getD i 0
    if i = a then row ||| (1 <<< b) else if i = b then row ||| (1 <<< a) else row

def graphFromEdges (n : ℕ) (edges : List (ℕ × ℕ)) : List ℕ :=
  edges.foldl (fun g e => setEdge g e.1 e.2) (List.replicate n 0)

/-- Combinations of `k` elements, in the order of the input list. -/
def combinations : ℕ → List ℕ → List (List ℕ)
  | 0, _ => [[]]
  | _, [] => []
  | k + 1, x :: xs =>
      (combinations k xs).map (fun ys => x :: ys) ++ combinations (k + 1) xs
termination_by _ xs => xs

def sixMask (six : List ℕ) : ℕ :=
  six.foldl (fun acc v => acc ||| (1 <<< v)) 0

def inducedDegree (g : List ℕ) (sixMask : ℕ) (v : ℕ) : ℕ :=
  popcount ((g.getD v 0) &&& sixMask)

/-- Grow one component inside `rem`, which does not contain the queue. -/
def grow (g : List ℕ) : ℕ → List ℕ → List ℕ → List ℕ → List ℕ × List ℕ
  | 0, _, comp, rem => (comp, rem)
  | _ + 1, [], comp, rem => (comp, rem)
  | fuel + 1, v :: queue, comp, rem =>
      let fresh := rem.filter fun w => edge g v w
      let rem' := rem.filter fun w => !fresh.contains w
      grow g fuel (queue ++ fresh) (comp ++ fresh) rem'

def componentList (g : List ℕ) (verts : List ℕ) : List (List ℕ) :=
  let rec go (fuel : ℕ) (rem : List ℕ) (acc : List (List ℕ)) : List (List ℕ) :=
    match fuel with
    | 0 => acc
    | fuel + 1 =>
        match rem with
        | [] => acc
        | v :: rest =>
            let (comp, rem') :=
              grow g (verts.length + 1) [v] [v] (rest.filter fun w => w != v)
            go fuel rem' (comp :: acc)
  go (verts.length + 1) verts []

def productMasks (groups : List (List ℕ)) : List ℕ :=
  groups.foldl (fun acc grp => acc.flatMap fun m => grp.map fun v => m ||| (1 <<< v)) [0]

/-- One 6-set that can complete an induced `P₇`, together with the attachment masks. -/
def p7Trace (g : List ℕ) (six : List ℕ) : Option (ℕ × List ℕ) :=
  let sm := sixMask six
  let degs := six.map (inducedDegree g sm)
  let badDeg := degs.any fun d => decide (2 < d)
  let e := degs.foldl (· + ·) 0 / 2
  if badDeg || (decide (e ≠ 4) && decide (e ≠ 5)) then
    none
  else
    let comps := componentList g six
    let ends := comps.map fun c => c.filter fun v => decide (inducedDegree g sm v ≤ 1)
    if decide (comps.length ≠ six.length - e) || ends.any List.isEmpty then
      none
    else
      some (sm, productMasks ends)

/-- Every 6-set trace, computed once per graph. `extensions` scans masks against this list. -/
def p7Traces (g : List ℕ) : List (ℕ × List ℕ) :=
  (combinations 6 (List.range g.length)).filterMap (p7Trace g)

/-- `mask` meets some 6-set in a trace that completes an induced `P₇`. -/
def hitsP7 (g : List ℕ) (mask : ℕ) : Bool :=
  (p7Traces g).any fun p => p.2.contains (mask &&& p.1)

def createsC4 (g : List ℕ) (mask : ℕ) : Bool :=
  g.any fun row => decide (2 ≤ popcount (row &&& mask))

def withNew (g : List ℕ) (mask : ℕ) : List ℕ :=
  let n := g.length
  ((List.range n).map fun i =>
      let row := g.getD i 0
      if Nat.testBit mask i then row ||| (1 <<< n) else row) ++
    [mask]

/-- Legal one-vertex extensions whose neighbourhood contains `required`. -/
def extensions (g : List ℕ) (required : ℕ) : List (List ℕ) :=
  let n := g.length
  let traces := p7Traces g
  (List.range (2 ^ n)).filterMap fun m =>
    if m = 0 then
      none
    else if m &&& required = 0 then
      none
    else if createsC4 g m then
      none
    else if traces.any (fun p => p.2.contains (m &&& p.1)) then
      none
    else
      some (withNew g m)

/-- `2 * deg - 3 * (edges among neighbours)`, the mask form of `L(v)`. -/
def loss (g : List ℕ) (v : ℕ) : ℕ :=
  let row := g.getD v 0
  let ns := (List.range g.length).filter fun i => Nat.testBit row i
  let triangles :=
    ns.foldl (fun acc a =>
      acc + (ns.filter fun b => decide (a < b) && edge g a b).length) 0
  2 * ns.length - 3 * triangles

structure Replay where
  nodes : ℕ
  maxOrder : ℕ
  leaves : ℕ
  deriving DecidableEq, Repr

def Replay.add (a b : Replay) : Replay where
  nodes := a.nodes + b.nodes
  maxOrder := max a.maxOrder b.maxOrder
  leaves := a.leaves + b.leaves

mutual
  def consume (kids : List (List ℕ)) (choices : List ℕ) (fuel : ℕ) :
      Option (Replay × List ℕ) :=
    match kids with
    | [] => some ({ nodes := 0, maxOrder := 0, leaves := 0 }, choices)
    | k :: ks =>
        match go k choices fuel with
        | none => none
        | some (s1, cs1) =>
            match consume ks cs1 fuel with
            | none => none
            | some (s2, cs2) => some (s1.add s2, cs2)
  termination_by (fuel, 1, kids.length)

  def go (g : List ℕ) (choices : List ℕ) (fuel : ℕ) : Option (Replay × List ℕ) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match choices with
        | [] => none
        | c :: cs =>
            let kids := extensions g (1 <<< c)
            if decide (c < g.length) && decide (loss g c < 4) then
              match consume kids cs fuel with
              | none => none
              | some (sub, rest) =>
                  some ({
                    nodes := sub.nodes + 1
                    maxOrder := max g.length sub.maxOrder
                    leaves := sub.leaves + if kids.isEmpty then 1 else 0
                  }, rest)
            else
              none
  termination_by (fuel, 0, 0)
end

/-- Replay one certificate. `none` means the list is not a complete legal closing,
so in particular it is not an unrestricted branch. -/
def replay (g : List ℕ) (choices : List ℕ) : Option Replay :=
  match go g choices (choices.length + 1) with
  | some (s, []) => some s
  | _ => none

def bridge (d : ℕ) : List ℕ :=
  0 :: List.range' 3 d

/-- The distance-`d` seed of Lemma 5.9. `d = 0` is the order-5 shared-vertex seed.
For `d ≥ 1` the second triangle is joined by a path of length `d`. -/
def seed (d : ℕ) : List ℕ :=
  let first : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 0)]
  if d = 0 then
    graphFromEdges 5 (first ++ [(0, 3), (3, 4), (4, 0)])
  else
    let b := bridge d
    let a := b.getLast?.getD 0
    let pathEdges := b.zip b.tail
    let second : List (ℕ × ℕ) := [(a, a + 1), (a + 1, a + 2), (a + 2, a)]
    graphFromEdges (a + 3) (first ++ pathEdges ++ second)

def choicesDist0 : List ℕ :=
  [0, 1, 2, 1, 3, 4, 2, 3, 4, 6, 9, 9, 6, 9, 9, 7, 7, 4, 10, 6, 6, 3, 9, 6, 6, 2, 7, 9,
    9, 1, 3, 4, 6, 8, 10, 10]

def choicesDist1 : List ℕ :=
  [0, 3, 1, 2, 4, 5, 8, 8, 2, 1, 2, 1, 2, 1, 3, 7, 1, 2, 4, 5, 10, 10, 0, 3, 6, 1, 2, 4, 5,
    10, 10]

def choicesDist2 : List ℕ :=
  [0, 1, 2, 5, 4, 4, 5, 2, 5, 1, 5, 2, 1, 2, 1, 1, 2, 5, 4, 7, 1, 2, 4, 2, 1, 6, 6, 2, 6,
    1, 6, 2, 1, 1, 2, 4, 2, 1, 5, 5, 2, 1, 2, 5, 1, 5]

def choicesDist3 : List ℕ :=
  [1, 6, 1, 6, 1]

theorem choicesDist0_length : choicesDist0.length = 36 := rfl

theorem choicesDist1_length : choicesDist1.length = 31 := rfl

theorem choicesDist2_length : choicesDist2.length = 46 := rfl

theorem choicesDist3_length : choicesDist3.length = 5 := rfl

def expectedDist0 : Replay := { nodes := 36, maxOrder := 17, leaves := 7 }

def expectedDist1 : Replay := { nodes := 31, maxOrder := 15, leaves := 6 }

def expectedDist2 : Replay := { nodes := 46, maxOrder := 11, leaves := 21 }

def expectedDist3 : Replay := { nodes := 5, maxOrder := 10, leaves := 3 }

/-- Execution of the four replays. Each `some` result is a complete legal closing,
so the unrestricted count on every row is 0. -/
theorem four_seed_replay :
    replay (seed 0) choicesDist0 = some expectedDist0 ∧
      replay (seed 1) choicesDist1 = some expectedDist1 ∧
      replay (seed 2) choicesDist2 = some expectedDist2 ∧
      replay (seed 3) choicesDist3 = some expectedDist3 := by
  native_decide

end InducedPaths.Certificate
