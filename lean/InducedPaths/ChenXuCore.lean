module

public import InducedPaths.Basic
public import InducedPaths.ChenXuCounts
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Tactic

open scoped SimpleGraph
open Finset SimpleGraph

@[expose] public section
namespace InducedPaths
variable {V : Type*} {G : SimpleGraph V}

set_option maxHeartbeats 4000000 in
/-- Lemma 2.10. A triangle-free strong `C₄`-free `P₇`-free graph with no cut vertex
has no clique cutset: a 2-clique cutset would leave two components, and the three
vertices of a shortest path through each component, meeting at the cut edge, form
an induced `P₇`. -/
theorem chenXu_noCliqueCutset_of_noCutVertex [Fintype V] [DecidableEq V] (hconn : G.Connected)
    (htri : G.CliqueFree 3) (hC : StrongC4Free G) (hp : IsPkFree G 7)
    (hcut : ∀ v, ¬ IsCutVertex G v) : ¬ HasCliqueCutset G := by
  classical
  have _usedConn : Nonempty V := hconn.nonempty
  intro hHas
  obtain ⟨s, hscl, hsne, -, hnot⟩ := hHas
  have hcard : s.ncard = 2 := by
    have hpos : 0 < s.ncard := (Set.ncard_pos).mpr hsne
    have hle : s.ncard ≤ 2 := by
      by_contra hgt
      have h3 : 2 < s.ncard := by omega
      obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff).1 h3
      exact htri {a, b, c} (is3Clique_triple_iff.mpr
        ⟨hscl ha hb hab, hscl ha hc hac, hscl hb hc hbc⟩)
    have hne1 : s.ncard ≠ 1 := by
      intro h1
      obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp h1
      have hcutw : IsCutVertex G w := by
        rw [IsCutVertex]
        have hscomp : sᶜ = {x | x ≠ w} := by
          ext x
          simp [hw, Set.mem_compl_iff, Set.mem_singleton_iff]
        rw [hscomp] at hnot
        exact hnot
      exact hcut w hcutw
    omega
  obtain ⟨u, v, huv, hsuv⟩ := Set.ncard_eq_two.mp hcard
  have huv_adj : G.Adj u v := hscl (by simp [hsuv]) (by simp [hsuv]) huv
  let H := G.induce (sᶜ)
  obtain ⟨x, y, hxy⟩ : ∃ x y : ↥(sᶜ), ¬ H.Reachable x y := by
    rw [Preconnected] at hnot
    push Not at hnot
    exact hnot
  let Cof : ↥(sᶜ) → Set V := fun t => {w | ∃ hw : w ∈ sᶜ, H.Reachable t ⟨w, hw⟩}
  have hCof_uv (t : ↥(sᶜ)) : u ∉ Cof t ∧ v ∉ Cof t := by
    constructor
    · intro ⟨hw, _⟩
      exact hw (by simp [hsuv])
    · intro ⟨hw, _⟩
      exact hw (by simp [hsuv])
  have hsplit {z anchor other : V} (hanchor : anchor ∈ s) (hother : other ∈ s)
      (hane : anchor ≠ other) (hz : z ∈ s) : z = anchor ∨ z = other := by
    have hanc : anchor = u ∨ anchor = v := by
      simpa [hsuv, Set.mem_insert_iff, Set.mem_singleton_iff] using hanchor
    have hoth : other = u ∨ other = v := by
      simpa [hsuv, Set.mem_insert_iff, Set.mem_singleton_iff] using hother
    have hzuv : z = u ∨ z = v := by
      simpa [hsuv, Set.mem_insert_iff, Set.mem_singleton_iff] using hz
    rcases hanc with rfl | rfl <;> rcases hoth with rfl | rfl <;> rcases hzuv with rfl | rfl
    · exact (hane rfl).elim
    · exact (hane rfl).elim
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl
    · exact Or.inl rfl
    · exact (hane rfl).elim
    · exact (hane rfl).elim
  have exists_nbr {anchor other : V} (hanchor : anchor ∈ s) (hother : other ∈ s)
      (hane : anchor ≠ other) (t out : ↥(sᶜ)) (_hsep : ¬ H.Reachable t out) :
      ∃ a : ↥(sᶜ), H.Reachable t a ∧ G.Adj other a.val := by
    have htA : t.val ≠ anchor := fun h => t.2 (h.symm ▸ hanchor)
    have hoA : out.val ≠ anchor := fun h => out.2 (h.symm ▸ hanchor)
    have htO : t.val ≠ other := fun h => t.2 (h.symm ▸ hother)
    have hpre : (G.induce {w | w ≠ anchor}).Preconnected := by
      simpa [IsCutVertex] using hcut anchor
    obtain ⟨q0⟩ := hpre ⟨t.val, htA⟩ ⟨out.val, hoA⟩
    let emb := SimpleGraph.Embedding.induce (G := G) {w | w ≠ anchor}
    let qRaw := q0.map emb.toHom
    have hsq : emb ⟨t.val, htA⟩ = t.val := rfl
    have hoq : emb ⟨out.val, hoA⟩ = out.val := rfl
    let qG : G.Walk t.val out.val := qRaw.copy hsq hoq
    have hqG_ne {z : V} (hz : z ∈ qG.support) : z ≠ anchor := by
      have hz' : z ∈ qRaw.support := by simpa [qG, Walk.support_copy] using hz
      rw [Walk.support_map] at hz'
      obtain ⟨w, -, hw⟩ := List.mem_map.mp hz'
      have hval : emb.toHom w = w.val := by
        simp [emb, SimpleGraph.Embedding.induce, SimpleGraph.Embedding.comap_apply,
          Function.Embedding.subtype_apply]
      rw [← hw, hval]
      exact w.2
    haveI : Decidable (other ∈ qG.support) := Classical.propDecidable _
    by_cases hhit : other ∈ qG.support
    · have hex : ∃ i, qG.getVert i = other ∧ i ≤ qG.length :=
        (Walk.mem_support_iff_exists_getVert).1 hhit
      haveI : DecidablePred (fun i => qG.getVert i = other ∧ i ≤ qG.length) :=
        fun _ => Classical.propDecidable _
      let i0 := Nat.find hex
      have hi0 := Nat.find_spec hex
      have hi0pos : 0 < i0 := by
        by_contra h0
        have hstart : qG.getVert i0 = other := hi0.1
        rw [show i0 = 0 by omega] at hstart
        rw [Walk.getVert_zero] at hstart
        exact htO hstart
      have hbefore {k : ℕ} (hk : k < i0) (hkle : k ≤ qG.length) : qG.getVert k ∈ sᶜ := by
        rw [Set.mem_compl_iff]
        intro hws
        have hwne_a : qG.getVert k ≠ anchor := hqG_ne (qG.getVert_mem_support k)
        have hwne_o : qG.getVert k ≠ other := by
          intro h
          exact (Nat.find_min hex hk ⟨h, hkle⟩).elim
        rcases hsplit hanchor hother hane hws with hza | hzo
        · exact hwne_a hza
        · exact hwne_o hzo
      have htake_len : (qG.take (i0 - 1)).length = i0 - 1 := by
        rw [Walk.take_length, min_eq_left (by omega : i0 - 1 ≤ qG.length)]
      have hprefix_in : ∀ w ∈ (qG.take (i0 - 1)).support, w ∈ sᶜ := by
        intro w hw
        obtain ⟨k, hk, hkle⟩ := (Walk.mem_support_iff_exists_getVert).1 hw
        have hk' : k ≤ i0 - 1 := by simpa [htake_len] using hkle
        have hkw : qG.getVert k = w := by
          rw [Walk.take_getVert] at hk
          simpa [min_eq_right hk'] using hk
        rw [← hkw]
        exact hbefore (by omega) (by omega)
      have hpred_in : qG.getVert (i0 - 1) ∈ sᶜ := hbefore (by omega) (by omega)
      have hadj : G.Adj (qG.getVert (i0 - 1)) other := by
        have hadj' := qG.adj_getVert_succ (show i0 - 1 < qG.length by omega)
        have hidx : (i0 - 1) + 1 = i0 := by omega
        have hadj'' : G.Adj (qG.getVert (i0 - 1)) (qG.getVert i0) := by
          simpa [hidx] using hadj'
        exact hi0.1 ▸ hadj''
      let qH := (qG.take (i0 - 1)).induce (sᶜ) hprefix_in
      have hstart :
          (⟨t.val, hprefix_in _ (qG.take (i0 - 1)).start_mem_support⟩ : ↥(sᶜ)) = t :=
        Subtype.ext rfl
      have hend :
          (⟨qG.getVert (i0 - 1),
              hprefix_in _ (qG.take (i0 - 1)).end_mem_support⟩ : ↥(sᶜ)) =
            ⟨qG.getVert (i0 - 1), hpred_in⟩ :=
        Subtype.ext rfl
      refine ⟨⟨qG.getVert (i0 - 1), hpred_in⟩, ⟨qH.copy hstart hend⟩, hadj.symm⟩
    · have hprefix_in : ∀ w ∈ qG.support, w ∈ sᶜ := by
        intro w hw
        rw [Set.mem_compl_iff]
        intro hws
        have hwne_a : w ≠ anchor := hqG_ne hw
        have hwne_o : w ≠ other := fun hwo => hhit (hwo ▸ hw)
        rcases hsplit hanchor hother hane hws with hza | hzo
        · exact hwne_a hza
        · exact hwne_o hzo
      let qH := qG.induce (sᶜ) hprefix_in
      have hstart : (⟨t.val, hprefix_in _ qG.start_mem_support⟩ : ↥(sᶜ)) = t :=
        Subtype.ext rfl
      have hend : (⟨out.val, hprefix_in _ qG.end_mem_support⟩ : ↥(sᶜ)) = out :=
        Subtype.ext rfl
      exact (_hsep ⟨qH.copy hstart hend⟩).elim
  have through (t out : ↥(sᶜ)) (hsep : ¬ H.Reachable t out) :
      ∃ p : G.Walk u v, 4 ≤ p.length ∧ p.IsPath ∧
        (∀ i, 0 < i → i < p.length → p.getVert i ∈ Cof t) ∧
        ∀ i j, i ≤ p.length → j ≤ p.length → i + 2 ≤ j → ¬ (i = 0 ∧ j = p.length) →
          ¬ G.Adj (p.getVert i) (p.getVert j) := by
    obtain ⟨a, haR, hau⟩ :=
      exists_nbr (show v ∈ s from by simp [hsuv]) (show u ∈ s from by simp [hsuv])
        (Ne.symm huv) t out hsep
    obtain ⟨b, hbR, hbv⟩ :=
      exists_nbr (show u ∈ s from by simp [hsuv]) (show v ∈ s from by simp [hsuv])
        huv t out hsep
    obtain ⟨r⟩ := haR.symm.trans hbR
    let emb := SimpleGraph.Embedding.induce (G := G) (sᶜ)
    let rRaw := r.map emb.toHom
    have hra : emb a = a.val := rfl
    have hrb : emb b = b.val := rfl
    let rG : G.Walk a.val b.val := rRaw.copy hra hrb
    let p0 : G.Walk u v := (rG.cons hau).concat hbv.symm
    have hp0len : p0.length = r.length + 2 := by
      have h : p0.length = r.length + 1 + 1 := by
        simp [p0, rG, rRaw, Walk.length_concat, Walk.length_cons, Walk.length_copy,
          Walk.length_map]
      omega
    let lens : Set ℕ :=
      {n | ∃ p : G.Walk u v, p.length = n ∧ 2 ≤ p.length ∧
        ∀ i, 0 < i → i < p.length → p.getVert i ∈ Cof t}
    have hp0int : ∀ i, 0 < i → i < p0.length → p0.getVert i ∈ Cof t := by
      intro i hi0 hiL
      have hi : i ≤ r.length + 1 := by
        have := hiL
        simp only [hp0len] at this
        omega
      have hp0eq : p0 = (rG.cons hau).append hbv.symm.toWalk := rfl
      have hget : p0.getVert i = (r.getVert (i - 1)).val := by
        have hlen1 : (rG.cons hau).length = r.length + 1 := by
          simp [rG, rRaw, Walk.length_cons, Walk.length_copy, Walk.length_map]
        have hle : i ≤ (rG.cons hau).length := by rw [hlen1]; exact hi
        rw [hp0eq, Walk.getVert_append', ite_eq_left hle]
        rw [Walk.getVert_cons rG hau (by omega : i ≠ 0)]
        rw [Walk.getVert_copy, Walk.getVert_map]
        simp [emb, SimpleGraph.Embedding.induce, SimpleGraph.Embedding.comap_apply,
          Function.Embedding.subtype_apply]
      rw [hget]
      simp only [Cof, Set.mem_ofPred_eq]
      exact ⟨(r.getVert (i - 1)).2,
        haR.trans (⟨r.take (i - 1)⟩ : H.Reachable a (r.getVert (i - 1)))⟩
    have hp0ge : 2 ≤ p0.length := by
      rw [hp0len]
      omega
    have hne : lens.Nonempty := by
      refine ⟨p0.length, ?_⟩
      simp only [lens, Set.mem_ofPred_eq]
      exact ⟨p0, rfl, hp0ge, hp0int⟩
    have hmem := Nat.sInf_mem hne
    simp only [lens, Set.mem_ofPred_eq] at hmem
    obtain ⟨p, hlen, hpge, hint⟩ := hmem
    have hshort (q : G.Walk u v) (hqint : ∀ i, 0 < i → i < q.length → q.getVert i ∈ Cof t)
        (hqge : 2 ≤ q.length) : p.length ≤ q.length := by
      have hqmem : q.length ∈ lens := by
        simp only [lens, Set.mem_ofPred_eq]
        exact ⟨q, rfl, hqge, hqint⟩
      calc
        p.length = sInf lens := hlen
        _ ≤ q.length := Nat.sInf_le hqmem
    have hfalse : ∀ a b : ℕ, a < b → b ≤ p.length → p.getVert a = p.getVert b → False := by
      intro a b hab hbnd hget
      have htake_len : (p.take a).length = a := by
        rw [Walk.take_length, min_eq_left (by omega : a ≤ p.length)]
      let q := (p.take a).append ((p.drop b).copy hget.symm rfl)
      have hqlen : q.length = a + (p.length - b) := by
        simp only [q, Walk.length_append, Walk.length_copy, Walk.take_length, Walk.drop_length,
          min_eq_left (show a ≤ p.length by omega)]
      have hqlt : q.length < p.length := by
        rw [hqlen]
        omega
      have hqge : 2 ≤ q.length := by
        rw [hqlen]
        by_contra hlt
        have hle1 : a + (p.length - b) ≤ 1 := by omega
        have ha1 : a ≤ 1 := by omega
        by_cases ha0 : a = 0
        · rw [ha0] at hget
          by_cases hbEq : b = p.length
          · rw [hbEq, Walk.getVert_zero, Walk.getVert_length] at hget
            exact huv hget
          · have hb1 : b = p.length - 1 := by omega
            have hmemI := hint b (by omega) (by omega)
            rw [← hget, Walk.getVert_zero] at hmemI
            exact (hCof_uv t).1 hmemI
        · have ha1eq : a = 1 := by omega
          have hbEq : b = p.length := by omega
          have hmemI := hint a (by omega) (by omega)
          rw [ha1eq] at hget hmemI
          rw [hget, hbEq, Walk.getVert_length] at hmemI
          exact (hCof_uv t).2 hmemI
      have hqint : ∀ k, 0 < k → k < q.length → q.getVert k ∈ Cof t := by
        intro k hk0 hkL
        have hkL' : k < a + (p.length - b) := by simpa [hqlen] using hkL
        unfold q
        rw [Walk.getVert_append']
        simp only [htake_len]
        split_ifs with hka
        · rw [Walk.take_getVert, min_eq_right hka]
          exact hint k hk0 (by omega)
        · rw [Walk.getVert_copy, Walk.drop_getVert]
          exact hint (b + (k - a)) (by omega) (by omega)
      exact (lt_irrefl _ ((hshort q hqint hqge).trans_lt hqlt)).elim
    have hpath : p.IsPath := by
      apply Walk.IsPath.mk'
      by_contra hdup
      rw [List.nodup_iff_injective_getElem] at hdup
      obtain ⟨i, j, heq, hneij⟩ := Function.not_injective_iff.mp hdup
      have hgetij : p.getVert i.1 = p.getVert j.1 := by
        rw [← p.support_getElem_eq_getVert i.isLt, ← p.support_getElem_eq_getVert j.isLt]
        exact heq
      have hiL : i.1 ≤ p.length := by
        have hlt : i.1 < p.support.length := i.isLt
        have hlen : p.support.length = p.length + 1 := p.length_support
        omega
      have hjL : j.1 ≤ p.length := by
        have hlt : j.1 < p.support.length := j.isLt
        have hlen : p.support.length = p.length + 1 := p.length_support
        omega
      rcases lt_or_gt_of_ne (fun h => hneij (Fin.ext h)) with hij | hij
      · exact hfalse i.1 j.1 hij hjL hgetij
      · exact hfalse j.1 i.1 hij hiL hgetij.symm
    have hnot2 : p.length ≠ 2 := by
      intro h2
      have h01 : G.Adj u (p.getVert 1) := by
        simpa [Walk.getVert_zero] using p.adj_getVert_succ (by omega : (0 : ℕ) < p.length)
      have h1v : G.Adj (p.getVert 1) v := by
        have hadj := p.adj_getVert_succ (by omega : 1 < p.length)
        have hv : p.getVert 2 = v := by simpa [h2] using Walk.getVert_length p
        simpa [hv] using hadj
      exact htri {u, p.getVert 1, v} (is3Clique_triple_iff.mpr ⟨h01, huv_adj, h1v⟩)
    have hnot3 : p.length ≠ 3 := by
      intro h3
      have h01 : G.Adj u (p.getVert 1) := by
        simpa [Walk.getVert_zero] using p.adj_getVert_succ (by omega : 0 < p.length)
      have h12 : G.Adj (p.getVert 1) (p.getVert 2) := p.adj_getVert_succ (by omega : 1 < p.length)
      have h2v : G.Adj (p.getVert 2) v := by
        have hadj := p.adj_getVert_succ (by omega : 2 < p.length)
        have hv : p.getVert 3 = v := by simpa [h3] using Walk.getVert_length p
        simpa [hv] using hadj
      have hneU : u ≠ p.getVert 2 := by
        intro h
        exact (hCof_uv t).1 (h.symm ▸ hint 2 (by omega) (by omega))
      have hneV : p.getVert 1 ≠ v := by
        intro h
        exact (hCof_uv t).2 (h.symm ▸ hint 1 (by omega) (by omega))
      exact hC (fourCycle_isContained h01 h12 h2v huv_adj.symm hneU hneV)
    have hfar : ∀ i j, i ≤ p.length → j ≤ p.length → i + 2 ≤ j →
        ¬ (i = 0 ∧ j = p.length) → ¬ G.Adj (p.getVert i) (p.getVert j) := by
      intro i j hi hj hgap hnot hadj
      have htake_len : (p.take i).length = i := by
        rw [Walk.take_length, min_eq_left hi]
      let qf := (p.take i).append ((p.drop j).cons hadj)
      have hqflen : qf.length = i + ((p.length - j) + 1) := by
        simp only [qf, Walk.length_append, Walk.length_cons, Walk.drop_length, htake_len]
      have hqfge : 2 ≤ qf.length := by
        rw [hqflen]
        by_contra hlt
        exact hnot (by omega)
      have hqflt : qf.length < p.length := by
        rw [hqflen]
        omega
      have hqfint : ∀ k, 0 < k → k < qf.length → qf.getVert k ∈ Cof t := by
        intro k hk0 hkL
        have hkL' : k < i + ((p.length - j) + 1) := by simpa [hqflen] using hkL
        unfold qf
        rw [Walk.getVert_append']
        simp only [htake_len]
        split_ifs with hki
        · rw [Walk.take_getVert, min_eq_right hki]
          exact hint k hk0 (by omega)
        · have hm : k - i ≠ 0 := by omega
          rw [Walk.getVert_cons (p.drop j) hadj hm, Walk.drop_getVert]
          exact hint (j + ((k - i) - 1)) (by omega) (by omega)
      exact (lt_irrefl _ ((hshort qf hqfint hqfge).trans_lt hqflt)).elim
    exact ⟨p, by omega, hpath, hint, hfar⟩
  obtain ⟨p, hp4, hppath, hpint, hpfar⟩ := through x y hxy
  obtain ⟨q, hq4, hqpath, hqint, hqfar⟩ := through y x fun hryx => hxy hryx.symm
  have hCof_disj {a b : V} (ha : a ∈ Cof x) (hb : b ∈ Cof y) : a ≠ b := by
    intro hab
    rcases ha with ⟨ha', hax⟩
    rcases hb with ⟨hb', hby⟩
    have hab' : (⟨a, ha'⟩ : ↥(sᶜ)) = ⟨b, hb'⟩ := Subtype.ext hab
    exact hxy (hax.trans (hab' ▸ hby.symm))
  have hno_cross {a b : V} (ha : a ∈ Cof x) (hb : b ∈ Cof y) : ¬ G.Adj a b := by
    intro hadj
    rcases ha with ⟨ha', hax⟩
    rcases hb with ⟨hb', hby⟩
    have hadjH : H.Adj (⟨a, ha'⟩ : ↥(sᶜ)) (⟨b, hb'⟩ : ↥(sᶜ)) :=
      SimpleGraph.induce_adj.mpr hadj
    have hstep : H.Reachable (⟨a, ha'⟩ : ↥(sᶜ)) (⟨b, hb'⟩ : ↥(sᶜ)) := ⟨hadjH.toWalk⟩
    exact hxy (hax.trans (hstep.trans hby.symm))
  let x1 := p.getVert (p.length - 3)
  let y1 := p.getVert (p.length - 2)
  let z1 := p.getVert (p.length - 1)
  let x2 := q.getVert (q.length - 3)
  let y2 := q.getVert (q.length - 2)
  let z2 := q.getVert (q.length - 1)
  have hx1y1 : G.Adj x1 y1 := by
    have hadj := p.adj_getVert_succ (show p.length - 3 < p.length by omega)
    simpa [x1, y1, show (p.length - 3) + 1 = p.length - 2 by omega] using hadj
  have hy1z1 : G.Adj y1 z1 := by
    have hadj := p.adj_getVert_succ (show p.length - 2 < p.length by omega)
    simpa [y1, z1, show (p.length - 2) + 1 = p.length - 1 by omega] using hadj
  have hz1v : G.Adj z1 v := by
    have hadj := p.adj_getVert_succ (show p.length - 1 < p.length by omega)
    have hv : p.getVert p.length = v := Walk.getVert_length p
    simpa [z1, show (p.length - 1) + 1 = p.length by omega, hv] using hadj
  have hx2y2 : G.Adj x2 y2 := by
    have hadj := q.adj_getVert_succ (show q.length - 3 < q.length by omega)
    simpa [x2, y2, show (q.length - 3) + 1 = q.length - 2 by omega] using hadj
  have hy2z2 : G.Adj y2 z2 := by
    have hadj := q.adj_getVert_succ (show q.length - 2 < q.length by omega)
    simpa [y2, z2, show (q.length - 2) + 1 = q.length - 1 by omega] using hadj
  have hz2v : G.Adj z2 v := by
    have hadj := q.adj_getVert_succ (show q.length - 1 < q.length by omega)
    have hv : q.getVert q.length = v := Walk.getVert_length q
    simpa [z2, show (q.length - 1) + 1 = q.length by omega, hv] using hadj
  have hy2x2 : G.Adj y2 x2 := hx2y2.symm
  have hz2y2 : G.Adj z2 y2 := hy2z2.symm
  have hvz2 : G.Adj v z2 := hz2v.symm
  let w1 : G.Walk y2 x2 := hy2x2.toWalk
  let w2 : G.Walk z2 x2 := w1.cons hz2y2
  let w3 : G.Walk v x2 := w2.cons hvz2
  let w4 : G.Walk z1 x2 := w3.cons hz1v
  let w5 : G.Walk y1 x2 := w4.cons hy1z1
  let w : G.Walk x1 x2 := w5.cons hx1y1
  have hsup : w.support = [x1, y1, z1, v, z2, y2, x2] := by
    unfold w w5 w4 w3 w2 w1
    simp [Walk.support_cons, Walk.support_nil]
  have hwlen : w.length = 6 := by
    have hs := w.length_support
    rw [hsup] at hs
    simp at hs
    omega
  have hlist : ([x1, y1, z1, v, z2, y2, x2] : List V).length = 7 := by simp
  have hget (n : ℕ) (hn : n < 7) : w.getVert n =
      [x1, y1, z1, v, z2, y2, x2][n]'(by rw [hlist]; exact hn) := by
    have hlt : n < w.support.length := by
      rw [Walk.length_support, hwlen]
      omega
    simpa [hsup] using (w.support_getElem_eq_getVert hlt).symm
  have hpref (n : ℕ) (hn : n ≤ 3) : w.getVert n = p.getVert (p.length - 3 + n) := by
    interval_cases n
    · rw [Walk.getVert_zero]
      unfold x1
      exact congrArg p.getVert (by omega)
    · have h1 : w.getVert 1 = y1 := by simpa using hget 1 (by decide)
      rw [h1]
      unfold y1
      exact congrArg p.getVert (by omega)
    · have h2 : w.getVert 2 = z1 := by simpa using hget 2 (by decide)
      rw [h2]
      unfold z1
      exact congrArg p.getVert (by omega)
    · have h3 : w.getVert 3 = v := by simpa using hget 3 (by decide)
      rw [h3]
      have hv : p.getVert (p.length - 3 + 3) = v := by
        have : p.length - 3 + 3 = p.length := by omega
        simp [this]
      exact hv.symm
  have hright (n : ℕ) (hn0 : 3 ≤ n) (hn : n ≤ 6) :
      w.getVert n = q.getVert (q.length - (n - 3)) := by
    interval_cases n
    · have h3 : w.getVert 3 = v := by simpa using hget 3 (by decide)
      rw [h3]
      have hv : q.getVert (q.length - (3 - 3)) = v := by simp
      exact hv.symm
    · have h4 : w.getVert 4 = z2 := by simpa using hget 4 (by decide)
      rw [h4]
    · have h5 : w.getVert 5 = y2 := by simpa using hget 5 (by decide)
      rw [h5]
    · have h6 : w.getVert 6 = x2 := by simpa using hget 6 (by decide)
      rw [h6]
  have hleftC (n : ℕ) (hn : n ≤ 2) : w.getVert n ∈ Cof x := by
    rw [hpref n (by omega)]
    exact hpint (p.length - 3 + n) (by omega) (by omega)
  have hrightC (n : ℕ) (hn4 : 4 ≤ n) (hn : n ≤ 6) : w.getVert n ∈ Cof y := by
    rw [hright n (by omega) hn]
    exact hqint (q.length - (n - 3)) (by omega) (by omega)
  have hneq (i j : ℕ) (hj : j ≤ 6) (hij : i < j) : w.getVert i ≠ w.getVert j := by
    intro heq
    by_cases hj3 : j ≤ 3
    · have := hppath.getVert_injOn
        (Set.mem_ofPred.mpr (show p.length - 3 + i ≤ p.length by omega))
        (Set.mem_ofPred.mpr (show p.length - 3 + j ≤ p.length by omega))
        ((hpref i (by omega)).symm.trans (heq.trans (hpref j (by omega))))
      omega
    · by_cases hi3 : 3 ≤ i
      · have := hqpath.getVert_injOn
          (Set.mem_ofPred.mpr (show q.length - (j - 3) ≤ q.length by omega))
          (Set.mem_ofPred.mpr (show q.length - (i - 3) ≤ q.length by omega))
          ((hright j (by omega) hj).symm.trans (heq.symm.trans (hright i hi3 (by omega))))
        omega
      · exact hCof_disj (hleftC i (by omega)) (hrightC j (by omega) hj) heq
  have hbad (i j : ℕ) (hgap : i + 2 ≤ j) (hj : j ≤ 6) : ¬ G.Adj (w.getVert i) (w.getVert j) := by
    intro hadj
    by_cases hj3 : j ≤ 3
    · exact hpfar (p.length - 3 + i) (p.length - 3 + j) (by omega) (by omega) (by omega)
        (by rintro ⟨_, _⟩; omega)
        (by simpa [hpref i (by omega), hpref j (by omega)] using hadj)
    · by_cases hi3 : 3 ≤ i
      · exact hqfar (q.length - (j - 3)) (q.length - (i - 3)) (by omega) (by omega) (by omega)
          (by rintro ⟨_, _⟩; omega)
          (by simpa [hright j (by omega) hj, hright i hi3 (by omega)] using hadj.symm)
      · exact hno_cross (hleftC i (by omega)) (hrightC j (by omega) hj) hadj
  have hwpath : w.IsPath := by
    apply Walk.IsPath.mk'
    rw [List.nodup_iff_injective_getElem]
    intro i j heq
    by_contra hne
    have hij : i.1 ≠ j.1 := fun h => hne (Fin.ext h)
    have hlt_i : i.1 < w.support.length := i.isLt
    have hlt_j : j.1 < w.support.length := j.isLt
    have hgetij : w.getVert i.1 = w.getVert j.1 := by
      rw [← w.support_getElem_eq_getVert hlt_i, ← w.support_getElem_eq_getVert hlt_j]
      exact heq
    have hi6 : i.1 ≤ 6 := by
      have hlen : w.support.length = 7 := by rw [Walk.length_support, hwlen]
      omega
    have hj6 : j.1 ≤ 6 := by
      have hlen : w.support.length = 7 := by rw [Walk.length_support, hwlen]
      omega
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact hneq i.1 j.1 hj6 hlt hgetij
    · exact hneq j.1 i.1 hi6 hlt hgetij.symm
  have hwchord : w.IsChordless := by
    rw [Walk.isChordless_iff_forall_mem_edges]
    intro a b ha hb hab
    obtain ⟨i, hi, hiL⟩ := (Walk.mem_support_iff_exists_getVert).1 ha
    obtain ⟨j, hj, hjL⟩ := (Walk.mem_support_iff_exists_getVert).1 hb
    have hi6 : i ≤ 6 := by simpa [hwlen] using hiL
    have hj6 : j ≤ 6 := by simpa [hwlen] using hjL
    rcases lt_trichotomy i j with hij | hij | hij
    · by_cases hstep : j = i + 1
      · have hmem : s(w.getVert i, w.getVert (i + 1)) ∈ w.edges :=
          (Walk.mk_mem_edges_iff_exists w).2 ⟨i, by rw [hwlen]; omega, rfl⟩
        rw [← hi, ← hj, hstep]
        exact hmem
      · exact (hbad i j (by omega) hj6 (by simpa [hi, hj] using hab)).elim
    · exact (hab.ne (hi.symm.trans (hij ▸ hj))).elim
    · by_cases hstep : i = j + 1
      · have hmem : s(w.getVert j, w.getVert (j + 1)) ∈ w.edges :=
          (Walk.mk_mem_edges_iff_exists w).2 ⟨j, by rw [hwlen]; omega, rfl⟩
        rw [← hi, ← hj, hstep, Sym2.eq_swap]
        exact hmem
      · exact (hbad j i (by omega) hi6 (by simpa [hi, hj] using hab.symm)).elim
  have hind : w.toSubgraph.IsInduced := Walk.isInduced_toSubgraph.mpr hwchord
  have hcont : pathGraph (w.length + 1) ⊴ G :=
    hwpath.pathGraphIsoToSubgraph.isIndContained.trans hind.isIndContained
  have hlen7 : w.length + 1 = 7 := by simp [hwlen]
  rw [hlen7] at hcont
  exact hp hcont

/-- A component left after removing a vertex has a neighbour of the removed vertex. -/
lemma chenXu_component_neighbor (hconn : G.Connected) (s : V)
    (x : {w : V // w ≠ s}) :
    ∃ a : {w : V // w ≠ s},
      (G.induce {w | w ≠ s}).Reachable x a ∧ G.Adj s a := by
  classical
  let H := G.induce {w | w ≠ s}
  by_contra hn
  have hn' : ∀ a : {w : V // w ≠ s}, H.Reachable x a → ¬ G.Adj s a := by
    intro a ha hadj
    exact hn ⟨a, ha, hadj⟩
  have closed : ∀ u v, G.Adj u v →
      (∃ hu : u ≠ s, H.Reachable x ⟨u, hu⟩) →
      ∃ hv : v ≠ s, H.Reachable x ⟨v, hv⟩ := by
    intro u v huv ⟨hu, hr⟩
    have hv : v ≠ s := by
      rintro rfl
      exact hn' ⟨u, hu⟩ hr huv.symm
    exact ⟨hv, hr.trans (show H.Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv).reachable⟩
  have propagate {u v : V} (w : G.Walk u v) :
      (∃ hu : u ≠ s, H.Reachable x ⟨u, hu⟩) →
      ∃ hv : v ≠ s, H.Reachable x ⟨v, hv⟩ := by
    induction w with
    | nil => exact id
    | cons h w ih => exact fun hu => ih (closed _ _ h hu)
  obtain ⟨w⟩ := hconn.preconnected x.val s
  obtain ⟨hs, -⟩ := propagate w ⟨x.property, Reachable.rfl⟩
  exact hs rfl

/-- Triangle freeness forbids the third edge of a two-edge walk. -/
lemma chenXu_not_adj_of_two_edges (htri : G.CliqueFree 3) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) : ¬ G.Adj a c := by
  classical
  intro hac
  exact htri {a, b, c} (is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)

/-- At minimum degree two one can continue an edge without backtracking. -/
lemma chenXu_next [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hdeg : ∀ v, 2 ≤ G.degree v) (a b : V) :
    ∃ c, G.Adj b c ∧ c ≠ a := by
  classical
  by_contra hn
  have hsub : G.neighborFinset b ⊆ {a} := by
    intro c hc
    have hadj : G.Adj b c := by simpa using hc
    have heq : c = a := by by_contra h; exact hn ⟨c, hadj, h⟩
    simpa [heq]
  have hle := Finset.card_le_card hsub
  have hd := hdeg b
  simp only [Finset.card_singleton, card_neighborFinset_eq_degree] at hle
  omega

/-- In minimum degree two, every side of a vertex contains a rooted induced P4. -/
lemma chenXu_side_path [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (htri : G.CliqueFree 3) (hC : StrongC4Free G)
    (hdeg : ∀ v, 2 ≤ G.degree v) (s : V) (x : {w : V // w ≠ s}) :
    ∃ a b c : {w : V // w ≠ s},
      (G.induce {w | w ≠ s}).Reachable x a ∧
      (G.induce {w | w ≠ s}).Reachable x b ∧
      (G.induce {w | w ≠ s}).Reachable x c ∧
      G.Adj s a ∧ G.Adj a b ∧ G.Adj b c ∧
      ¬ G.Adj s b ∧ ¬ G.Adj s c ∧ ¬ G.Adj a c ∧ a ≠ c := by
  classical
  let H := G.induce {w | w ≠ s}
  obtain ⟨a, ha, hsa⟩ := chenXu_component_neighbor hconn s x
  obtain ⟨b, hab, hbs⟩ := chenXu_next hdeg s a
  have hsb := chenXu_not_adj_of_two_edges htri hsa hab
  obtain ⟨c, hbc, hca⟩ := chenXu_next hdeg a b
  have hac := chenXu_not_adj_of_two_edges htri hab hbc
  have hcs : c ≠ s := by
    rintro rfl
    exact hsb hbc.symm
  have hsc : ¬ G.Adj s c := by
    intro hsc
    exact hC (fourCycle_isContained hsa hab hbc hsc.symm
      hbs.symm (by exact Ne.symm hca))
  let b' : {w : V // w ≠ s} := ⟨b, hbs⟩
  let c' : {w : V // w ≠ s} := ⟨c, hcs⟩
  have hab' : H.Adj a b' := hab
  have hbc' : H.Adj b' c' := hbc
  exact ⟨a, b', c', ha, ha.trans hab'.reachable,
    (ha.trans hab'.reachable).trans hbc'.reachable,
    hsa, hab, hbc, hsb, hsc, hac, fun h => hca (congrArg Subtype.val h).symm⟩

set_option maxHeartbeats 2000000 in
/-- Two cyclic sides of a cut vertex force an induced P7. -/
lemma chenXu_noCutVertex_of_min_degree [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] (hconn : G.Connected) (htri : G.CliqueFree 3)
    (hC : StrongC4Free G) (hp : IsPkFree G 7) (hdeg : ∀ v, 2 ≤ G.degree v) :
    ∀ s, ¬ IsCutVertex G s := by
  classical
  intro s hs
  let H := G.induce {w | w ≠ s}
  obtain ⟨x, y, hxy⟩ : ∃ x y, ¬ H.Reachable x y := by
    change ¬ H.Preconnected at hs
    simpa only [Preconnected, not_forall] using hs
  obtain ⟨a, b, c, ha, hb, hc, hsa, hab, hbc, hsb, hsc, hac, hane⟩ :=
    chenXu_side_path hconn htri hC hdeg s x
  obtain ⟨d, e, f, hd, he, hf, hsd, hde, hef, hse, hsf, hdf, hdne⟩ :=
    chenXu_side_path hconn htri hC hdeg s y
  have cross_ne (u v : {w : V // w ≠ s}) (hu : H.Reachable x u)
      (hv : H.Reachable y v) : (u : V) ≠ v := by
    intro huv
    have huv' : u = v := Subtype.ext huv
    exact hxy (hu.trans (huv' ▸ hv.symm))
  have cross_adj (u v : {w : V // w ≠ s}) (hu : H.Reachable x u)
      (hv : H.Reachable y v) : ¬ G.Adj u v := by
    intro huv
    exact hxy (hu.trans ((show H.Adj u v from huv).reachable.trans hv.symm))
  have hne1 := cross_ne a d ha hd
  have hne2 := cross_ne a e ha he
  have hne3 := cross_ne a f ha hf
  have hne4 := cross_ne b d hb hd
  have hne5 := cross_ne b e hb he
  have hne6 := cross_ne b f hb hf
  have hne7 := cross_ne c d hc hd
  have hne8 := cross_ne c e hc he
  have hne9 := cross_ne c f hc hf
  have hn1 := cross_adj a d ha hd
  have hn2 := cross_adj a e ha he
  have hn3 := cross_adj a f ha hf
  have hn4 := cross_adj b d hb hd
  have hn5 := cross_adj b e hb he
  have hn6 := cross_adj b f hb hf
  have hn7 := cross_adj c d hc hd
  have hn8 := cross_adj c e hc he
  have hn9 := cross_adj c f hc hf
  have hacne : (a : V) ≠ c := fun h => hane (Subtype.ext h)
  have hdfne : (d : V) ≠ f := fun h => hdne (Subtype.ext h)
  let p : Fin 7 → V := ![c, b, a, s, d, e, f]
  have pinj : Function.Injective p := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [p] at hij ⊢ <;>
      grind [Adj.ne, a.property, b.property, c.property, d.property, e.property, f.property]
  have padj : ∀ i j, G.Adj (p i) (p j) ↔ (pathGraph 7).Adj i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [p, pathGraph_adj] <;>
      grind only [G.adj_comm, G.irrefl]
  exact hp ⟨{ toFun := p, inj' := pinj, map_rel_iff' := fun {i j} => padj i j }⟩

/-- The vertex-set operation in one leaf-deletion step. -/
def chenXuErase (S : Set V) (v : V) : Set V := {w | w ∈ S ∧ w ≠ v}

/-- Literal leaf stripping, retaining each degree-one deletion as a proof witness. -/
inductive ChenXuLeafStrips (G : SimpleGraph V) : Set V → Set V → Prop
  | refl (S) : ChenXuLeafStrips G S S
  | step (S Q : Set V) (v : S) [Fintype S] [DecidableRel (G.induce S).Adj]
      (hleaf : (G.induce S).degree v = 1)
      (tail : ChenXuLeafStrips G (chenXuErase S v) Q) : ChenXuLeafStrips G S Q

noncomputable def chenXuEraseIso (S : Set V) (v : S) :
    ((G.induce S).induce ({v}ᶜ : Set S)) ≃g G.induce (chenXuErase S v) where
  toFun w := ⟨w.val.val, w.val.property, fun h => w.property (Subtype.ext h)⟩
  invFun w := ⟨⟨w.val, w.property.1⟩, fun h => w.property.2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

lemma chenXu_edgeCount_iso {W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] [DecidableRel G.Adj]
    {H : SimpleGraph W} [DecidableRel H.Adj] (e : G ≃g H) :
    edgeCount G = edgeCount H := by
  classical
  exact e.card_edgeFinset_eq

lemma chenXu_erase_card [Fintype V] (S : Set V) (v : S) :
    Nat.card (chenXuErase S v) + 1 = Nat.card S := by
  classical
  let e : chenXuErase S v ≃ ↥({v}ᶜ : Set S) :=
    (chenXuEraseIso (G := (⊥ : SimpleGraph V)) S v).toEquiv.symm
  rw [Nat.card_congr e]
  simp only [Nat.card_eq_fintype_card]
  have hp : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨v⟩
  change Fintype.card {w : S // ¬ w = v} + 1 = Fintype.card S
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]
  omega

lemma ChenXuLeafStrips.subset {S Q : Set V} (h : ChenXuLeafStrips G S Q) : Q ⊆ S := by
  induction h with
  | refl => exact Set.Subset.rfl
  | step S Q v hleaf tail ih => exact fun w hw => (ih hw).1

lemma ChenXuLeafStrips.outside_neighbors {S Q : Set V}
    (h : ChenXuLeafStrips G S Q) :
    ∀ v ∈ S, v ∉ Q → (Q ∩ G.neighborSet v).Subsingleton := by
  induction h with
  | refl => exact fun v hv hv' => (hv' hv).elim
  | step S Q v hleaf tail ih =>
    intro w hw hwQ
    by_cases hwv : w = v.val
    · subst w
      intro a ha b hb
      have haS := tail.subset ha.1
      have hbS := tail.subset hb.1
      have hsingle : ((G.induce S).neighborSet v).Subsingleton := by
        rw [← Set.ncard_le_one_iff_subsingleton, SimpleGraph.ncard_neighborSet]
        exact hleaf.le
      exact congrArg Subtype.val (hsingle (show (G.induce S).Adj v ⟨a, haS.1⟩ from ha.2)
        (show (G.induce S).Adj v ⟨b, hbS.1⟩ from hb.2))
    · exact ih w ⟨hw, hwv⟩ hwQ

open Classical in
lemma chenXu_strip_to_terminal [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (S : Set V) (hc : (G.induce S).Connected) :
    ∃ Q : Set V, ChenXuLeafStrips G S Q ∧ (G.induce Q).Connected ∧
      (∀ v : Q, (G.induce Q).degree v ≠ 1) ∧
      edgeCount (G.induce S) = edgeCount (G.induce Q) + (Nat.card S - Nat.card Q) := by
  classical
  have main : ∀ n, ∀ S : Set V, Nat.card S = n → (G.induce S).Connected →
      ∃ Q : Set V, ChenXuLeafStrips G S Q ∧ (G.induce Q).Connected ∧
        (∀ v : Q, (G.induce Q).degree v ≠ 1) ∧
        edgeCount (G.induce S) = edgeCount (G.induce Q) + (Nat.card S - Nat.card Q) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hn hc
      by_cases hleaf : ∃ v : S, (G.induce S).degree v = 1
      · obtain ⟨v, hv⟩ := hleaf
        let T := chenXuErase S v
        let e := chenXuEraseIso (G := G) S v
        have hcT : (G.induce T).Connected :=
          e.connected_iff.mp (hc.induce_compl_singleton_of_degree_eq_one hv)
        have hcard : Nat.card T + 1 = Nat.card S := chenXu_erase_card S v
        obtain ⟨Q, ht, hqc, hqn, hqe⟩ := ih (Nat.card T) (by omega) T rfl hcT
        have hQT : Nat.card Q ≤ Nat.card T := Nat.card_le_card_of_injective
          (Set.inclusion ht.subset) (Set.inclusion_injective ht.subset)
        have hedge := edgeCount_induce_compl_add (G := G.induce S) v
        rw [hv, chenXu_edgeCount_iso e] at hedge
        exact ⟨Q, .step S Q v hv ht, hqc, hqn, by dsimp [T] at *; omega⟩
      · exact ⟨S, .refl S, hc, by simpa only [not_exists] using hleaf, by simp⟩
  exact main (Nat.card S) S rfl hc

/-- A complete connected triangle-free graph has one or two vertices. -/
lemma chenXu_complete_small [Fintype V] [DecidableEq V]
    (hconn : G.Connected) (htri : G.CliqueFree 3) (hcomplete : G = ⊤) :
    Nonempty (G ≃g completeGraph (Fin 1)) ∨ Nonempty (G ≃g k2Graph) := by
  classical
  haveI := hconn.nonempty
  have hle : Fintype.card V ≤ 2 := by
    by_contra hn
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp (by omega : 2 < Fintype.card V)
    exact htri {a, b, c} (is3Clique_triple_iff.mpr (by simpa [hcomplete] using And.intro hab (And.intro hac hbc)))
  have hpos := Fintype.card_pos (α := V)
  have make (k : ℕ) (hk : Fintype.card V = k) : Nonempty (G ≃g completeGraph (Fin k)) := by
    subst G
    exact ⟨SimpleGraph.Iso.completeGraph (Fintype.equivFinOfCardEq hk)⟩
  by_cases h1 : Fintype.card V = 1
  · exact Or.inl (make 1 h1)
  · exact Or.inr (make 2 (by omega))

open Classical in
/-- Terminal stripping cores have no clique cutset and belong to the Chen–Xu list. -/
lemma chenXu_terminal_classification [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (htri : G.CliqueFree 3) (hC : StrongC4Free G)
    (hp : IsPkFree G 7) (hn : ∀ v, G.degree v ≠ 1) :
    ¬ HasCliqueCutset G ∧
      (Nonempty (G ≃g completeGraph (Fin 1)) ∨ Nonempty (G ≃g k2Graph) ∨
        InChenXuFamily G) := by
  classical
  have hcut : ∀ v, ¬ IsCutVertex G v := by
    by_cases ht : Nontrivial V
    · letI := ht
      have hdeg : ∀ v, 2 ≤ G.degree v := by
        intro v
        obtain ⟨u, hu⟩ := hconn.preconnected.exists_adj_of_nontrivial v
        have hpv : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨u, hu⟩
        have hv := hn v
        omega
      exact chenXu_noCutVertex_of_min_degree hconn htri hC hp hdeg
    · haveI : Subsingleton V := not_nontrivial_iff_subsingleton.mp ht
      intro v hv
      exact hv (fun x y => by have he : x = y := Subsingleton.elim _ _; subst y; exact Reachable.rfl)
  have hcl := chenXu_noCliqueCutset_of_noCutVertex hconn htri hC hp hcut
  refine ⟨hcl, ?_⟩
  by_cases hc : G = ⊤
  · rcases chenXu_complete_small hconn htri hc with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (chen_xu_core G hconn hp
      (strongC4Free_no_induced_C4 hC) htri hcl hc))

open Classical in
/-- Exact Lemma 5.4, retaining the literal sequence of leaf deletions. -/
theorem chenXu_tree_core_stripping [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (htri : G.CliqueFree 3) (hC : StrongC4Free G)
    (hp : IsPkFree G 7) :
    ∃ (Q : Set V) (_ : DecidablePred (· ∈ Q)),
      ChenXuLeafStrips G Set.univ Q ∧
      (G.induce Q).Connected ∧ (G.induce Q).CliqueFree 3 ∧ StrongC4Free (G.induce Q) ∧
        IsPkFree (G.induce Q) 7 ∧ ¬ HasCliqueCutset (G.induce Q) ∧
        (Nonempty ((G.induce Q) ≃g (completeGraph (Fin 1))) ∨
          Nonempty ((G.induce Q) ≃g k2Graph) ∨ InChenXuFamily (G.induce Q)) ∧
        edgeCount G = edgeCount (G.induce Q) + (Fintype.card V - Nat.card Q) ∧
        3 * Fintype.card V - 2 * edgeCount G =
          (3 * Nat.card Q - 2 * edgeCount (G.induce Q)) +
            (Fintype.card V - Nat.card Q) := by
  classical
  obtain ⟨Q, hs, hqc, hqn, he⟩ := chenXu_strip_to_terminal Set.univ
    ((induceUnivIso G).connected_iff.mpr hconn)
  have hqt : (G.induce Q).CliqueFree 3 := (cliqueFree_induce_iff G Q 3).mpr htri.cliqueFreeOn
  have hqC : StrongC4Free (G.induce Q) := strongC4Free_induce hC
  have hqp : IsPkFree (G.induce Q) 7 := fun h =>
    hp (h.trans (Embedding.induce Q).isIndContained)
  obtain ⟨hqcut, hclass⟩ := chenXu_terminal_classification hqc hqt hqC hqp hqn
  have he' : edgeCount G = edgeCount (G.induce Q) + (Fintype.card V - Nat.card Q) := by
    letI : Fintype ↥(Set.univ : Set V) := Subtype.fintype (· ∈ (Set.univ : Set V))
    have hi := chenXu_edgeCount_iso (induceUnivIso G)
    have heNat : Nat.card (Set.univ : Set V) = Fintype.card V := by simp
    rw [heNat] at he
    have heCanon : edgeCount (G.induce Set.univ) =
        edgeCount (G.induce Q) + (Fintype.card V - Nat.card Q) := by
      convert he using 1 <;> simp only [edgeCount, SimpleGraph.edgeFinset, Set.toFinset_card]
      simp only [← Nat.card_eq_fintype_card]
    exact hi.symm.trans heCanon
  have hbound : 2 * edgeCount (G.induce Q) ≤ 3 * Nat.card Q := by
    rcases hclass with h1 | h2 | hf
    · obtain ⟨e⟩ := h1
      have hn := Fintype.card_congr e.toEquiv
      have heq : edgeCount (G.induce Q) = edgeCount (completeGraph (Fin 1)) := e.card_edgeFinset_eq
      have hz : edgeCount (completeGraph (Fin 1)) = 0 := by decide
      simp only [Fintype.card_fin] at hn
      rw [Nat.card_eq_fintype_card]
      omega
    · obtain ⟨e⟩ := h2
      have hn := Fintype.card_congr e.toEquiv
      have heq : edgeCount (G.induce Q) = edgeCount k2Graph := e.card_edgeFinset_eq
      have hz : edgeCount k2Graph = 1 := by decide
      simp only [Fintype.card_fin] at hn
      rw [Nat.card_eq_fintype_card]
      omega
    · simpa only [Nat.card_eq_fintype_card] using chenXu_family_edge_bound hf
  have hcard : Nat.card Q ≤ Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card] using Fintype.card_subtype_le (· ∈ Q)
  exact ⟨Q, inferInstance, hs, hqc, hqt, hqC, hqp, hqcut, hclass, he', by omega⟩

open Classical in
/-- The exact public statement of Lemma 5.4. -/
theorem chenXu_tree_core [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hconn : G.Connected) (htri : G.CliqueFree 3) (hC : StrongC4Free G)
    (hp : IsPkFree G 7) :
    ∃ (Q : Set V) (_ : DecidablePred (· ∈ Q)),
      (G.induce Q).Connected ∧ (G.induce Q).CliqueFree 3 ∧ StrongC4Free (G.induce Q) ∧
        IsPkFree (G.induce Q) 7 ∧ ¬ HasCliqueCutset (G.induce Q) ∧
        (Nonempty ((G.induce Q) ≃g (completeGraph (Fin 1))) ∨
          Nonempty ((G.induce Q) ≃g k2Graph) ∨ InChenXuFamily (G.induce Q)) ∧
        edgeCount G = edgeCount (G.induce Q) + (Fintype.card V - Nat.card Q) ∧
        3 * Fintype.card V - 2 * edgeCount G =
          (3 * Nat.card Q - 2 * edgeCount (G.induce Q)) +
            (Fintype.card V - Nat.card Q) := by
  obtain ⟨Q, hd, -, h⟩ := chenXu_tree_core_stripping hconn htri hC hp
  exact ⟨Q, hd, h⟩

end InducedPaths
