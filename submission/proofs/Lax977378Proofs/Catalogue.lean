import Lax977378.Catalogue
import Mathlib.Tactic

namespace Lax977378Proofs.Catalogue
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests

noncomputable def ball {c : Nat} (G : Graph c) (r : Nat) (x : Fin G.size) : Finset (Fin G.size) := by
  classical
  exact Finset.univ.filter (within G r x)

@[simp] theorem mem_ball {c : Nat} (G : Graph c) (r : Nat) (x y : Fin G.size) :
    y ∈ ball G r x ↔ within G r x y := by classical simp [ball]

theorem centerWithin {c : Nat} (G : Graph c) (r : Nat) (x : Fin G.size) : within G r x x := by
  induction r with
  | zero => rfl
  | succ r ih => exact Or.inl ih

theorem ballCard {c : Nat} (G : Graph c) (d : Nat) (hd : G.Bounded d)
    (r : Nat) (x : Fin G.size) : (ball G r x).card ≤ (d+1)^r := by
  classical
  choose nb hnod hsize hedge using hd
  induction r with
  | zero =>
    have he : ball G 0 x = {x} := by ext y; simp [within,eq_comm]
    simp [he]
  | succ r ih =>
    let S := ball G r x
    have sub : ball G (r+1) x ⊆ S ∪ S.biUnion (fun v => (nb v).toFinset) := by
      intro y hy
      rcases (mem_ball ..).mp hy with hy | ⟨v,hv,he⟩
      · exact Finset.mem_union_left _ ((mem_ball ..).mpr hy)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v,(mem_ball ..).mpr hv,
          List.mem_toFinset.mpr ((hedge _ _).mpr he)⟩)
    have hnb (v) : (nb v).toFinset.card ≤ d := (List.toFinset_card_le _).trans (hsize v)
    calc
      _ ≤ (S ∪ S.biUnion (fun v => (nb v).toFinset)).card := Finset.card_le_card sub
      _ ≤ S.card + (S.biUnion (fun v => (nb v).toFinset)).card := Finset.card_union_le ..
      _ ≤ S.card + ∑ v ∈ S, (nb v).toFinset.card := by gcongr; exact Finset.card_biUnion_le
      _ ≤ S.card + ∑ _v ∈ S, d := by gcongr with v; exact hnb v
      _ = S.card * (d+1) := by simp [Nat.mul_add,Nat.add_comm]
      _ ≤ _ := by rw [pow_succ]; exact Nat.mul_le_mul_right _ ih

private abbrev Code (c n : Nat) :=
  (Fin n → Fin n → Bool) × (Fin c → Fin n → Bool) × Fin n

private def decode {c n : Nat} (code : Code c n) : Pointed c where
  pattern := {
    size := n
    edge := fun i j => i ≠ j ∧ code.1 i j = true ∧ code.1 j i = true
    symm := fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩
    loopless := fun _ h => h.1 rfl
    pred := fun p i => code.2.1 p i = true }
  center := code.2.2

private noncomputable def patterns (c N : Nat) : List (Pointed c) := by
  classical
  exact (List.range (N+1)).flatMap (fun n =>
    (Finset.univ : Finset (Code c n)).toList.map decode)

/--
---
conclusion: Lax977378.Catalogue.catalogue
---
The cardinality of a ball increases by a factor of at most $d+1$ per step.
Number the actual vertices of the ball, transport their edges and unary
predicates, and use that numbering as the witness for its catalogue entry.
-/
theorem catalogue (c d r : Nat) : ∃ ts : List (Pointed c),
    ∀ G : Graph c, G.Bounded d → ∀ x, ∃ t ∈ ts, Occurs t r G x := by
  classical
  refine ⟨patterns c ((d+1)^r),?_⟩
  intro G hd x
  let S := ball G r x
  let e := S.equivFin
  let y (i : Fin S.card) := (e.symm i).val
  let rootId := e ⟨x,(mem_ball ..).mpr (centerWithin G r x)⟩
  have hroot : y rootId = x := by simp [y,rootId]
  let code : Code c S.card :=
    (fun i j => decide (G.edge (y i) (y j)),fun p i => decide (G.pred p (y i)),rootId)
  have hy : Function.Injective y := fun i j h => e.symm.injective (Subtype.ext h)
  have dia : Diagram (decode code).pattern G y := by
    refine ⟨hy,?_,?_⟩
    · intro i j
      change (i ≠ j ∧ decide _ = true ∧ decide _ = true) ↔ _
      simp only [decide_eq_true_eq]
      exact ⟨fun h => h.2.1,fun he => ⟨fun h => G.loopless _ (h ▸ he),he,G.symm _ _ he⟩⟩
    · intro p i; exact decide_eq_true_iff
  refine ⟨decode code,?_,y,⟨dia,?_⟩,hroot⟩
  · apply List.mem_flatMap.mpr
    exact ⟨S.card,List.mem_range.mpr (Nat.lt_succ_of_le (ballCard G d hd r x)),
      List.mem_map.mpr ⟨code,by simp,rfl⟩⟩
  · intro z
    change (∃ i, y i = z) ↔ ∃ i ∈ ({rootId} : Finset (Fin S.card)), within G r (y i) z
    simp only [Finset.mem_singleton,exists_eq_left,hroot]
    constructor
    · rintro ⟨i,rfl⟩; exact (mem_ball ..).mp (e.symm i).property
    · intro hz; exact ⟨e ⟨z,(mem_ball ..).mpr hz⟩, by simp [y]⟩

end Lax977378Proofs.Catalogue
