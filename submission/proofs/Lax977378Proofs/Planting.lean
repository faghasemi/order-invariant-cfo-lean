import Lax977378.Planting
import Lax977378.Separation
import Lax977378Proofs.Catalogue
import Lax977378Proofs.Window

namespace Lax977378Proofs.Planting
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests Lax977378.CountParameters
open Lax977378.Planting Lax977378Proofs.Catalogue Lax977378Proofs.Window

theorem reverseWithin {c} {G : Graph c} {r : Nat} {x y : Fin G.size}
    (h : within G r x y) : within G r y x := by
  induction r generalizing y with
  | zero => exact Eq.symm h
  | succ r ih =>
    rcases h with h | ⟨z,hz,he⟩
    · exact Or.inl (ih h)
    · have step : within G 1 y z := Or.inr ⟨y,rfl,G.symm _ _ he⟩
      simpa [Nat.add_comm] using join step (ih hz)

private theorem finish {c d q} (G : Graph c) (hd : G.Bounded d) (p : Nat)
    (palette : (d+1)^p ≤ q) (P : Finset (Fin G.size)) (colour : Fin G.size → Fin q)
    (proper : ProperOn G p P colour) :
    ∃ k, (∀ u ∈ P, k u = colour u) ∧ ProperOn G p Finset.univ k := by
  classical
  let nb (x : Fin G.size) := (ball G p x).erase x
  have mem (x y) : y ∈ nb x ↔ y ≠ x ∧ within G p x y := by simp [nb]
  have bound x : (nb x).card < q :=
    (Finset.card_erase_lt_of_mem ((mem_ball ..).mpr (centerWithin G p x))).trans_le
      ((ballCard G d hd p x).trans palette)
  obtain ⟨k,hk,hp⟩ := Lax977378.Separation.extendColouring nb
    (fun x y h => (mem ..).mpr ⟨(mem ..).mp h |>.1.symm,reverseWithin ((mem ..).mp h).2⟩)
    (fun x h => ((mem ..).mp h).1 rfl) q bound P colour
    (fun x hx y hy h => proper _ hx _ hy ((mem ..).mp h).1.symm ((mem ..).mp h).2)
  exact ⟨k,hk,fun x _ y _ hxy h => hp x y ((mem ..).mpr ⟨hxy.symm,h⟩)⟩

/--
---
conclusion: Lax977378.Planting.plant
assumptions:
  - Lax977378.Separation.extendColouring
---
Choose one occurrence outside the union of the forbidden balls, prescribe its
colours and include its whole ball in the next excluded set. The uniform
bound budgets for this increase on every request. Extend the resulting
partial colouring on the graph power after the final request.
-/
theorem plant {c d q : Nat} (G : Graph c) (hd : G.Bounded d) (r p : Nat)
    (palette : (d+1)^p ≤ q) (P : Finset (Fin G.size)) (colour : Fin G.size → Fin q)
    (proper : ProperOn G p P colour) (requests : List (Request c q))
    (enough : ∀ s ∈ requests, (P.card + requests.length * (d+1)^r) * (d+1)^(2*r+p) <
      (locations s.type r G).card) :
    ∃ k : Fin G.size → Fin q, ∃ centres : List (Fin G.size),
      (∀ u ∈ P, k u = colour u) ∧ ProperOn G p Finset.univ k ∧
      List.Forall₂ (fun x s => Realised s G r k x) centres requests ∧
      (∀ x ∈ centres, ∀ u ∈ P, ¬ within G (2*r+p) u x) ∧
      centres.Pairwise (fun x y => ¬ within G (2*r+p) x y) := by
  classical
  induction requests generalizing P colour with
  | nil =>
    obtain ⟨k,hk,hp⟩ := finish G hd p palette P colour proper
    exact ⟨k,[],hk,hp,.nil,by simp,.nil⟩
  | cons s ss ih =>
    let R := 2*r+p
    let forbidden := P.biUnion (ball G R)
    have banned : forbidden.card ≤ P.card * (d+1)^R := by
      calc
        _ ≤ ∑ u ∈ P, (ball G R u).card := Finset.card_biUnion_le
        _ ≤ ∑ _u ∈ P, (d+1)^R := by gcongr with u; exact ballCard G d hd R u
        _ = _ := by simp
    obtain ⟨x,hx,hout⟩ : ∃ x ∈ locations s.type r G, x ∉ forbidden := by
      by_contra! sub
      have hc := (Finset.card_le_card sub).trans banned
      have he := enough s List.mem_cons_self
      exact (Nat.not_lt_of_ge (hc.trans (Nat.mul_le_mul_right _ (Nat.le_add_right ..)))) he
    have far (u) (hu : u ∈ P) : ¬ within G R u x :=
      fun h => hout (Finset.mem_biUnion.mpr ⟨u,hu,(mem_ball ..).mpr h⟩)
    obtain ⟨y,⟨dia,window⟩,root⟩ : Occurs s.type r G x := (Finset.mem_filter.mp hx).2
    have domain (v) : (∃ j, y j = v) ↔ within G r x v := by simpa [root] using window v
    have here (i) : within G r x (y i) := (domain _).mp ⟨i,rfl⟩
    have away (u) (hu : u ∈ P) (v) (hv : within G r x v) : ¬ within G p u v := by
      intro h
      exact far u hu (grow (join h (reverseWithin hv)) (by dsimp [R]; omega))
    let newColour (u : Fin G.size) := if h : ∃ j, y j = u then s.paint h.choose else colour u
    have paint (j) : newColour (y j) = s.paint j := by
      have e : ∃ i, y i = y j := ⟨j,rfl⟩
      simp only [newColour,dif_pos e,dia.1 e.choose_spec]
    have old (u) (hu : u ∈ P) : newColour u = colour u := by
      have no : ¬ ∃ i, y i = u := fun e => away u hu u ((domain _).mp e) (centerWithin ..)
      simp [newColour,no]
    let P' := P ∪ ball G r x
    have compatible : ProperOn G p P' newColour := by
      intro u hu v hv huv adj
      rcases Finset.mem_union.mp hu with oldU | ballU <;> rcases Finset.mem_union.mp hv with oldV | ballV
      · rw [old u oldU,old v oldV]; exact proper u oldU v oldV huv adj
      · exact False.elim (away u oldU v ((mem_ball ..).mp ballV) adj)
      · exact False.elim (away v oldV u ((mem_ball ..).mp ballU) (reverseWithin adj))
      · obtain ⟨i,rfl⟩ := (domain u).mpr ((mem_ball ..).mp ballU)
        obtain ⟨j,rfl⟩ := (domain v).mpr ((mem_ball ..).mp ballV)
        rw [paint,paint]; exact fun h => huv (congrArg y (s.inj h))
    have next (s' : Request c q) (hs' : s' ∈ ss) :
        (P'.card + ss.length * (d+1)^r) * (d+1)^R < (locations s'.type r G).card := by
      have he := enough s' (List.mem_cons_of_mem _ hs')
      have hc := (Finset.card_union_le P (ball G r x)).trans
        (Nat.add_le_add_left (ballCard G d hd r x) _)
      apply lt_of_le_of_lt (Nat.mul_le_mul_right _ ?_) he
      simp only [List.length_cons,Nat.succ_mul]
      change (P ∪ ball G r x).card + _ ≤ _
      omega
    obtain ⟨k,cs,hk,hp,align,avoid,sep⟩ := ih P' newColour compatible next
    have kept (i) : k (y i) = s.paint i :=
      (hk _ (Finset.mem_union_right _ ((mem_ball ..).mpr (here i)))).trans (paint i)
    refine ⟨k,x :: cs,fun u hu => (hk u (Finset.mem_union_left _ hu)).trans (old u hu),hp,
      .cons ⟨y,⟨dia,window⟩,root,kept⟩ align,?_,List.pairwise_cons.mpr ⟨?_,sep⟩⟩
    · intro z hz u hu
      rcases List.mem_cons.mp hz with rfl | hz
      · exact far u hu
      · exact avoid z hz u (Finset.mem_union_left _ hu)
    · intro z hz
      exact avoid z hz x (Finset.mem_union_right _ ((mem_ball ..).mpr (centerWithin ..)))

end Lax977378Proofs.Planting
