/-
Semantic bridges for the actual one-vertex extension enumerator.
The P7 trace obligation is kept explicit until componentList is verified.
-/
module

public import InducedPaths.Certificate
public import InducedPaths.Basic

@[expose] public section

open scoped SimpleGraph

namespace InducedPaths.Certificate

universe u

/-- Exact sufficient conditions for the executable extension enumerator. -/
theorem withNew_mem_extensions {g : List ℕ} {m required : ℕ}
    (hbound : m < 2 ^ g.length) (hnonzero : m ≠ 0)
    (hrequired : m &&& required ≠ 0)
    (hc4 : createsC4 g m = false) (hp7 : hitsP7 g m = false) :
    withNew g m ∈ extensions g required := by
  apply List.mem_filterMap.mpr
  refine ⟨m, List.mem_range.mpr hbound, ?_⟩
  change (if m = 0 then none else if m &&& required = 0 then none else
    if createsC4 g m then none else if hitsP7 g m then none else
    some (withNew g m)) = some (withNew g m)
  rw [if_neg hnonzero, if_neg hrequired, hc4, hp7]
  rfl

/-- Meeting the requested singleton bit is exactly adjacency to that index. -/
theorem and_singleton_ne_zero {m c : ℕ} (h : m.testBit c = true) :
    m &&& (1 <<< c) ≠ 0 := by
  intro hz
  have hb := congrArg (fun n : ℕ => n.testBit c) hz
  simp [Nat.testBit_and, Nat.testBit_shiftLeft, h] at hb

/-- The bit counter cannot report two bits when its bit support is subsingleton.
This needs no normalization and remains true even with insufficient fuel. -/
theorem popcount_go_le_one_of_subsingleton (fuel m : ℕ)
    (h : ∀ i j, m.testBit i = true → m.testBit j = true → i = j) :
    popcount.go fuel m ≤ 1 := by
  induction fuel generalizing m with
  | zero => cases m <;> simp [popcount.go]
  | succ fuel ih =>
    by_cases hm : m = 0
    · subst m; simp [popcount.go]
    · have hgo : popcount.go (fuel + 1) m =
          (m &&& 1) + popcount.go fuel (m >>> 1) := by
        cases m <;> simp_all [popcount.go]
      rw [hgo]
      by_cases hbit : m.testBit 0 = true
      · have hshift : m >>> 1 = 0 := by
          apply Nat.eq_of_testBit_eq
          intro i
          simp only [Nat.testBit_shiftRight, Nat.zero_testBit]
          cases he : m.testBit (1 + i) with
          | false => rfl
          | true => have := h (1 + i) 0 he hbit; omega
        have hmod : m % 2 = 1 := Nat.mod_two_eq_one_iff_testBit_zero.mpr hbit
        simp [Nat.and_one_is_mod, hmod, hshift, popcount.go]
      · have hmod : m % 2 = 0 := by
          apply Nat.mod_two_eq_zero_iff_testBit_zero.mpr
          simpa using hbit
        simp only [Nat.and_one_is_mod, hmod, Nat.zero_add]
        apply ih
        intro i j hi hj
        have he := h (1 + i) (1 + j)
          (by simpa using hi) (by simpa using hj)
        omega

theorem popcount_le_one_of_subsingleton (m : ℕ)
    (h : ∀ i j, m.testBit i = true → m.testBit j = true → i = j) :
    popcount m ≤ 1 := popcount_go_le_one_of_subsingleton m m h

/-- An ambient induced realization of the in-range entries of a mask graph.
No claim is made about unused high row bits. -/
structure Realizes {V : Type*} (G : SimpleGraph V) (g : List ℕ) where
  vertices : Fin g.length ↪ V
  adj_iff : ∀ i j, G.Adj (vertices i) (vertices j) ↔ edge g i.val j.val = true

/-- Bits in a bounded mask are valid old vertex indices. -/
theorem lt_length_of_testBit {g : List ℕ} {m i : ℕ}
    (hm : m < 2 ^ g.length) (hi : m.testBit i = true) : i < g.length := by
  by_contra hn
  have hp : 2 ^ g.length ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
  have hb := Nat.ge_two_pow_of_testBit hi
  omega

/-- An actual ambient extension cannot trigger the C4 rejection test.
The new vertex is outside the old induced realization. -/
theorem createsC4_eq_false_of_realizes {V : Type*} {G : SimpleGraph V}
    {g : List ℕ} (r : Realizes G g) (hG : InducedPaths.StrongC4Free G)
    (x : V) (hx : ∀ i, x ≠ r.vertices i) {m : ℕ}
    (hm : m < 2 ^ g.length)
    (hmask : ∀ i : Fin g.length, m.testBit i.val = true ↔ G.Adj x (r.vertices i)) :
    createsC4 g m = false := by
  apply Bool.eq_false_iff.mpr
  intro hbad
  obtain ⟨row, hrow, htwo⟩ := List.any_eq_true.mp hbad
  obtain ⟨a, ha, harow⟩ := List.mem_iff_getElem.mp hrow
  have hrow' : g.getD a 0 = row := by simpa [List.getD, List.getElem?_eq_getElem ha] using harow
  have hsmall : popcount (row &&& m) ≤ 1 := by
    apply popcount_le_one_of_subsingleton
    intro i j hi hj
    have hi' : row.testBit i = true ∧ m.testBit i = true := by simpa using hi
    have hj' : row.testBit j = true ∧ m.testBit j = true := by simpa using hj
    let ai : Fin g.length := ⟨a, ha⟩
    let ii : Fin g.length := ⟨i, lt_length_of_testBit hm hi'.2⟩
    let ji : Fin g.length := ⟨j, lt_length_of_testBit hm hj'.2⟩
    have hai : G.Adj (r.vertices ai) (r.vertices ii) :=
      (r.adj_iff ai ii).mpr (by change (g.getD a 0).testBit i = true; rw [hrow']; exact hi'.1)
    have haj : G.Adj (r.vertices ai) (r.vertices ji) :=
      (r.adj_iff ai ji).mpr (by change (g.getD a 0).testBit j = true; rw [hrow']; exact hj'.1)
    have hxi := (hmask ii).mp hi'.2
    have hxj := (hmask ji).mp hj'.2
    have heq := InducedPaths.commonNeighbors_subsingleton hG (hx ai)
      (show r.vertices ii ∈ G.commonNeighbors x (r.vertices ai) from ⟨hxi, hai⟩)
      (show r.vertices ji ∈ G.commonNeighbors x (r.vertices ai) from ⟨hxj, haj⟩)
    exact congrArg Fin.val (r.vertices.injective heq)
  have : 2 ≤ popcount (row &&& m) := of_decide_eq_true htwo
  omega

@[simp] theorem length_withNew (g : List ℕ) (m : ℕ) :
    (withNew g m).length = g.length + 1 := by simp [withNew]

/-- Adjacencies among old vertices are unchanged. -/
theorem edge_withNew_old {g : List ℕ} {m i j : ℕ}
    (hi : i < g.length) (hj : j < g.length) :
    edge (withNew g m) i j = edge g i j := by
  have hs : (1 <<< g.length).testBit j = false := by
    simp [Nat.testBit_shiftLeft, show ¬g.length ≤ j from by omega]
  by_cases hb : m.testBit i = true <;>
    simp [edge, withNew, List.getD, List.getElem?_append, hi, hb, hs]

/-- The new last row is exactly the attachment mask. -/
theorem edge_withNew_last (g : List ℕ) (m j : ℕ) :
    edge (withNew g m) g.length j = m.testBit j := by
  simp [edge, withNew, List.getD, List.getElem?_append]

/-- Every old-to-new edge is exactly the corresponding attachment bit. -/
theorem edge_withNew_to_last {g : List ℕ} {m i : ℕ}
    (hi : i < g.length) :
    edge (withNew g m) i g.length = (edge g i g.length || m.testBit i) := by
  by_cases hb : m.testBit i = true
  · simp [edge, withNew, List.getD, List.getElem?_append, List.getElem?_range hi, hi, hb]
  · have hb' : m.testBit i = false := by simpa using hb
    simp [edge, withNew, List.getD, List.getElem?_append, List.getElem?_range hi, hi, hb']

/-- Unlike `WellFormed`, this excludes unused high bits. Such bits would
otherwise become spurious old-to-new edges in `withNew`. -/
def Normalized (g : List ℕ) : Prop := ∀ i < g.length, g.getD i 0 < 2 ^ g.length

theorem normalized_withNew {g : List ℕ} (hg : Normalized g) {m : ℕ}
    (hm : m < 2 ^ g.length) : Normalized (withNew g m) := by
  intro i hi
  rw [length_withNew] at hi ⊢
  by_cases hold : i < g.length
  · have hrow := hg i hold
    have hp : 2 ^ g.length < 2 ^ (g.length + 1) := by
      rw [pow_succ]; have := Nat.two_pow_pos g.length; omega
    have hpow : 1 <<< g.length < 2 ^ (g.length + 1) := by
      simpa [Nat.shiftLeft_eq] using hp
    have hor := Nat.or_lt_two_pow (Nat.lt_trans hrow hp) hpow
    simpa [withNew, List.getD, List.getElem?_append, List.getElem?_range hi, hold] using
      (show (if m.testBit i then g.getD i 0 ||| (1 <<< g.length) else
        g.getD i 0) < 2 ^ (g.length + 1) from by
          split
          · exact hor
          · exact Nat.lt_trans hrow hp)
  · have heq : i = g.length := by omega
    subst i
    have hp : 2 ^ g.length ≤ 2 ^ (g.length + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    simpa [withNew, List.getD, List.getElem?_append, List.getElem?_range hi] using Nat.lt_of_lt_of_le hm hp

/-- Normalization removes the possible high-bit contamination. -/
theorem edge_withNew_to_last_of_normalized {g : List ℕ} (hg : Normalized g)
    {m i : ℕ} (hi : i < g.length) :
    edge (withNew g m) i g.length = m.testBit i := by
  rw [edge_withNew_to_last hi]
  have hz : edge g i g.length = false := Nat.testBit_lt_two_pow (hg i hi)
  rw [hz]; rfl

/-- Concrete ambient completeness, with just the unproved P7 rejection obligation
left explicit. C4 rejection is discharged here, not supplied as an assumption. -/
theorem withNew_mem_extensions_of_realizes {V : Type*} {G : SimpleGraph V}
    {g : List ℕ} (r : Realizes G g) (hG : InducedPaths.StrongC4Free G)
    (x : V) (hx : ∀ i, x ≠ r.vertices i) {m : ℕ}
    (hm : m < 2 ^ g.length)
    (hmask : ∀ i : Fin g.length, m.testBit i.val = true ↔ G.Adj x (r.vertices i))
    (c : Fin g.length) (hc : G.Adj x (r.vertices c))
    (hp7 : hitsP7 g m = false) :
    withNew g m ∈ extensions g (1 <<< c.val) := by
  have hbit := (hmask c).mpr hc
  have hnonzero : m ≠ 0 := by intro hz; simp [hz] at hbit
  exact withNew_mem_extensions hm hnonzero (and_singleton_ne_zero hbit)
    (createsC4_eq_false_of_realizes r hG x hx hm hmask) hp7

/-- Extending an induced ambient realization uses the actual `withNew` rows. -/
def realizes_withNew {V : Type*} {G : SimpleGraph V} {g : List ℕ}
    (r : Realizes G g) (hg : Normalized g) (x : V)
    (hx : ∀ i, x ≠ r.vertices i) {m : ℕ} (hm : m < 2 ^ g.length)
    (hmask : ∀ i : Fin g.length, m.testBit i.val = true ↔ G.Adj x (r.vertices i)) :
    Realizes G (withNew g m) := by
  let f : Fin (withNew g m).length → V := fun i =>
    if h : i.val < g.length then r.vertices ⟨i.val, h⟩ else x
  have hinj : Function.Injective f := by
    intro i j hij
    dsimp [f] at hij
    split at hij <;> split at hij
    · exact Fin.ext (congrArg (fun k : Fin g.length => k.val) (r.vertices.injective hij))
    · exact False.elim (hx _ hij.symm)
    · exact False.elim (hx _ hij)
    · apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      simp only [length_withNew] at hi hj
      omega
  refine ⟨⟨f, hinj⟩, ?_⟩
  intro i j
  change G.Adj (f i) (f j) ↔ _
  by_cases hi : i.val < g.length <;> by_cases hj : j.val < g.length
  · rw [edge_withNew_old hi hj]
    simpa [f, hi, hj] using r.adj_iff ⟨i.val, hi⟩ ⟨j.val, hj⟩
  · have hjlast : j.val = g.length := by
      have := j.isLt; simp only [length_withNew] at this; omega
    rw [hjlast, edge_withNew_to_last_of_normalized hg hi]
    simpa [f, hi, hj, SimpleGraph.adj_comm] using (hmask ⟨i.val, hi⟩).symm
  · have hilast : i.val = g.length := by
      have := i.isLt; simp only [length_withNew] at this; omega
    rw [hilast, edge_withNew_last]
    simpa [f, hi, hj] using (hmask ⟨j.val, hj⟩).symm
  · have hilast : i.val = g.length := by
      have := i.isLt; simp only [length_withNew] at this; omega
    have hjlast : j.val = g.length := by
      have := j.isLt; simp only [length_withNew] at this; omega
    rw [hilast, hjlast, edge_withNew_last, Nat.testBit_lt_two_pow hm]
    simp [f, hi, hj]

/-- The exact outstanding semantic obligation: every rejected trace creates an
induced seven-vertex path in an ambient realization. This is intentionally a
proposition, not an axiom or an assertion that the checker has been verified. -/
def TraceRejectionSound : Prop :=
  ∀ {V : Type u} (G : SimpleGraph V) (g : List ℕ) (r : Realizes G g)
    (x : V), (∀ i, x ≠ r.vertices i) →
    ∀ m : ℕ, m < 2 ^ g.length →
    (∀ i : Fin g.length, m.testBit i.val = true ↔ G.Adj x (r.vertices i)) →
    ∀ sm attachments, (sm, attachments) ∈ p7Traces g →
      m &&& sm ∈ attachments → SimpleGraph.pathGraph 7 ⊴ G

/-- Once trace rejection soundness is established, P7-freeness discharges the
last executable rejection test. -/
theorem hitsP7_eq_false_of_traceRejectionSound (sound : TraceRejectionSound.{u})
    {V : Type u} {G : SimpleGraph V} {g : List ℕ} (r : Realizes G g)
    (x : V) (hx : ∀ i, x ≠ r.vertices i) {m : ℕ} (hm : m < 2 ^ g.length)
    (hmask : ∀ i : Fin g.length, m.testBit i.val = true ↔ G.Adj x (r.vertices i))
    (hP7 : InducedPaths.IsPkFree G 7) : hitsP7 g m = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  obtain ⟨⟨sm, attachments⟩, hmem, hhit⟩ := List.any_eq_true.mp hh
  exact hP7 (sound G g r x hx m hm hmask sm attachments hmem
    (List.contains_iff_mem.mp hhit))

/-- A small explicit witness can certify an individual trace without proving
correctness of the component-search implementation. `none` denotes the new
vertex, and `some i` denotes an old vertex in the trace's six-set. -/
structure TracePathWitness (g : List ℕ) (sm attachment : ℕ) where
  path : Fin 7 ↪ Option (Fin g.length)
  supported : ∀ k i, path k = some i → sm.testBit i.val = true
  path_adj : ∀ k l, (SimpleGraph.pathGraph 7).Adj k l ↔
    match path k, path l with
    | none, none => False
    | none, some j => attachment.testBit j.val = true
    | some i, none => attachment.testBit i.val = true
    | some i, some j => edge g i.val j.val = true

/-- Explicit path witnesses transport using only the trace intersection;
computing or checking these finite witnesses does not change checker semantics. -/
theorem TracePathWitness.isIndContained {V : Type*} {G : SimpleGraph V}
    {g : List ℕ} {sm attachment m : ℕ} (w : TracePathWitness g sm attachment)
    (r : Realizes G g) (x : V) (hx : ∀ i, x ≠ r.vertices i)
    (hmask : ∀ i : Fin g.length, m.testBit i.val = true ↔ G.Adj x (r.vertices i))
    (htrace : m &&& sm = attachment) : SimpleGraph.pathGraph 7 ⊴ G := by
  let f : Option (Fin g.length) → V := fun i => i.elim x r.vertices
  have hf : Function.Injective f := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact False.elim (hx j hij)
    | some i =>
      cases j with
      | none => exact False.elim (hx i hij.symm)
      | some j => exact congrArg some (r.vertices.injective hij)
  have hbit (k : Fin 7) (i : Fin g.length) (hi : w.path k = some i) :
      attachment.testBit i.val = m.testBit i.val := by
    rw [← htrace, Nat.testBit_and, w.supported k i hi, Bool.and_true]
  refine ⟨{ toEmbedding := w.path.trans ⟨f, hf⟩, map_rel_iff' := ?_ }⟩
  intro k l
  change G.Adj (f (w.path k)) (f (w.path l)) ↔ _
  rw [w.path_adj]
  cases hk : w.path k with
  | none =>
    cases hl : w.path l with
    | none => simp [f]
    | some j => simpa [f, hbit l j hl] using (hmask j).symm
  | some i =>
    cases hl : w.path l with
    | none => simpa [f, hbit k i hk, SimpleGraph.adj_comm] using (hmask i).symm
    | some j => exact r.adj_iff i j

/-- Node-local finite witness completeness is enough; there is no need to verify
`grow` globally if these witnesses are supplied for the actual replay nodes. -/
def HasTracePathWitnesses (g : List ℕ) : Prop :=
  ∀ sm attachments, (sm, attachments) ∈ p7Traces g →
    ∀ attachment ∈ attachments, Nonempty (TracePathWitness g sm attachment)

theorem hitsP7_eq_false_of_witnesses {V : Type*} {G : SimpleGraph V}
    {g : List ℕ} (hw : HasTracePathWitnesses g) (r : Realizes G g)
    (x : V) (hx : ∀ i, x ≠ r.vertices i) {m : ℕ}
    (hmask : ∀ i : Fin g.length, m.testBit i.val = true ↔ G.Adj x (r.vertices i))
    (hP7 : InducedPaths.IsPkFree G 7) : hitsP7 g m = false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  obtain ⟨⟨sm, attachments⟩, hmem, hhit⟩ := List.any_eq_true.mp hh
  obtain ⟨w⟩ := hw sm attachments hmem (m &&& sm) (List.contains_iff_mem.mp hhit)
  exact hP7 (w.isIndContained r x hx hmask rfl)

/-- A decidable finite specification, suitable for independent witness checking.
It deliberately avoids trusting the component enumeration implementation. -/
def ValidTracePath (g : List ℕ) (sm attachment : ℕ)
    (p : Fin 7 → Option (Fin g.length)) : Prop :=
  Function.Injective p ∧
  (∀ k i, p k = some i → sm.testBit i.val = true) ∧
  ∀ k l, (SimpleGraph.pathGraph 7).Adj k l ↔
    match p k, p l with
    | none, none => False
    | none, some j => attachment.testBit j.val = true
    | some i, none => attachment.testBit i.val = true
    | some i, some j => edge g i.val j.val = true

instance (g : List ℕ) (sm attachment : ℕ) (p : Fin 7 → Option (Fin g.length)) :
    Decidable (ValidTracePath g sm attachment p) := by
  unfold ValidTracePath
  letI : Decidable (Function.Injective p) :=
    decidable_of_iff (∀ a b, p a = p b → a = b) ⟨fun h => h, fun h => h⟩
  letI : DecidableRel (fun k l : Fin 7 =>
      match p k, p l with
      | none, none => False
      | none, some j => attachment.testBit j.val = true
      | some i, none => attachment.testBit i.val = true
      | some i, some j => edge g i.val j.val = true) := by
    intro k l
    dsimp only
    cases p k <;> cases p l <;> infer_instance
  infer_instance

def ValidTracePath.witness {g : List ℕ} {sm attachment : ℕ}
    {p : Fin 7 → Option (Fin g.length)} (h : ValidTracePath g sm attachment p) :
    TracePathWitness g sm attachment := ⟨⟨p, h.1⟩, h.2.1, h.2.2⟩

/-- Conditional but concrete end-to-end extension theorem: its sole checker
correctness prerequisite is the explicit finite path-witness property. -/
theorem actual_extension_of_traceWitnesses {V : Type*} {G : SimpleGraph V}
    {g : List ℕ} (hw : HasTracePathWitnesses g) (r : Realizes G g)
    (hg : Normalized g) (hG : InducedPaths.StrongC4Free G)
    (hP7 : InducedPaths.IsPkFree G 7) (x : V) (hx : ∀ i, x ≠ r.vertices i)
    {m : ℕ} (hm : m < 2 ^ g.length)
    (hmask : ∀ i : Fin g.length, m.testBit i.val = true ↔ G.Adj x (r.vertices i))
    (c : Fin g.length) (hc : G.Adj x (r.vertices c)) :
    withNew g m ∈ extensions g (1 <<< c.val) ∧
      Normalized (withNew g m) ∧ Nonempty (Realizes G (withNew g m)) := by
  refine ⟨withNew_mem_extensions_of_realizes r hG x hx hm hmask c hc ?_,
    normalized_withNew hg hm, ⟨realizes_withNew r hg x hx hm hmask⟩⟩
  exact hitsP7_eq_false_of_witnesses hw r x hx hmask hP7

private theorem testBit_foldl_mask (xs : List ℕ) (acc i : ℕ) :
    (xs.foldl (fun a v => a ||| (1 <<< v)) acc).testBit i = true ↔
      acc.testBit i = true ∨ i ∈ xs := by
  induction xs generalizing acc with
  | nil => simp
  | cons v xs ih =>
    rw [List.foldl_cons, ih]
    have hs : (1 <<< v).testBit i = decide (v = i) := by
      rw [Nat.shiftLeft_eq]; simp [Nat.testBit_two_pow]
    simp only [Nat.testBit_or, Bool.or_eq_true, hs, decide_eq_true_eq,
      List.mem_cons]
    tauto

theorem testBit_sixMask (xs : List ℕ) (i : ℕ) :
    (sixMask xs).testBit i = true ↔ i ∈ xs := by
  simpa [sixMask] using testBit_foldl_mask xs 0 i

theorem sixMask_lt_two_pow {xs : List ℕ} {n : ℕ} (h : ∀ i ∈ xs, i < n) :
    sixMask xs < 2 ^ n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  apply Bool.eq_false_iff.mpr
  intro hb
  have := h i ((testBit_sixMask xs i).mp hb)
  omega

/-- The actual ambient neighbourhood encoded as a bounded executable mask. -/
noncomputable def ambientMask {V : Type*} (G : SimpleGraph V) {g : List ℕ}
    (r : Realizes G g) (x : V) : ℕ := by
  classical
  exact sixMask ((List.finRange g.length).filterMap fun i =>
    if G.Adj x (r.vertices i) then some i.val else none)

theorem ambientMask_testBit {V : Type*} {G : SimpleGraph V} {g : List ℕ}
    (r : Realizes G g) (x : V) (i : Fin g.length) :
    (ambientMask G r x).testBit i.val = true ↔ G.Adj x (r.vertices i) := by
  classical
  rw [ambientMask, testBit_sixMask]
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨j, _, hj⟩
    split at hj
    · have heq : j = i := Fin.ext (Option.some.inj hj)
      subst j
      assumption
    · contradiction
  · intro hi
    exact ⟨i, List.mem_finRange i, by simp [hi]⟩

theorem ambientMask_lt_two_pow {V : Type*} {G : SimpleGraph V} {g : List ℕ}
    (r : Realizes G g) (x : V) : ambientMask G r x < 2 ^ g.length := by
  classical
  unfold ambientMask
  apply sixMask_lt_two_pow
  intro i hi
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hi
  split at hj
  · have heq := Option.some.inj hj
    rw [← heq]
    exact j.isLt
  · contradiction

end InducedPaths.Certificate
