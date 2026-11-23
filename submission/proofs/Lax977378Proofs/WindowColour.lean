import Lax977378.WindowColour
import Lax977378Proofs.Catalogue
import Lax977378Proofs.Window

namespace Lax977378Proofs.WindowColour
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests Lax977378.Planting
open Lax977378Proofs.Catalogue Lax977378Proofs.Window

/--
---
conclusion: Lax977378.WindowColour.precolour
assumptions:
  - Lax977378.Window.exactBall
---
Pull back a target path of length at most p from its first named vertex into
the window. Mapping that path into the source shows that the transported
colours must differ.
-/
theorem precolour {c d q r p} (W A B : Graph c) (hd : B.Bounded d) (mark : Finset (Fin W.size))
    (y : Fin W.size → Fin A.size) (z : Fin W.size → Fin B.size)
    (wy : Window W A (r+p) mark y) (wz : Window W B (r+p) mark z)
    (κ : Fin A.size → Fin q) (proper : ProperOn A p Finset.univ κ) (nonempty : 0 < q) :
    ∃ (P : Finset (Fin B.size)) (paint : Fin B.size → Fin q),
      P.card ≤ mark.card*(d+1)^r ∧ ProperOn B p P paint ∧
      (∀ j, (∃ m ∈ mark, within W r m j) → z j ∈ P ∧ paint (z j) = κ (y j)) := by
  classical
  let inner := mark.biUnion (ball W r)
  let P := inner.image z
  let paint (x : Fin B.size) : Fin q := if h : ∃ j, z j = x then κ (y h.choose) else ⟨0,nonempty⟩
  have col (j) : paint (z j) = κ (y j) := by
    have h : ∃ k, z k = z j := ⟨j,rfl⟩
    simp only [paint,dif_pos h,wz.1.1 h.choose_spec]
  have near (j) : j ∈ inner ↔ ∃ m ∈ mark, within W r m j := by simp [inner]
  have cover : P ⊆ mark.biUnion (fun m => ball B r (z m)) := by
    intro x hx
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨m,hm,dist⟩ := (near _).mp hj
    exact Finset.mem_biUnion.mpr ⟨m,hm,(mem_ball ..).mpr (mapWithin wz.1 dist)⟩
  refine ⟨P,paint,?_,?_,fun j hj => ⟨Finset.mem_image_of_mem _ ((near _).mpr hj),col j⟩⟩
  · calc
      P.card ≤ _ := Finset.card_le_card cover
      _ ≤ ∑ m ∈ mark, (ball B r (z m)).card := Finset.card_biUnion_le
      _ ≤ ∑ _m ∈ mark, (d+1)^r := by gcongr with m; exact ballCard B d hd r _
      _ = _ := by simp
  · intro x hx u hu ne path
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v,dist,eq⟩ := (Lax977378.Window.exactBall wz ((near _).mp hj) p le_rfl _).mp path
    cases wz.1.1 eq
    rw [col,col]
    exact proper _ (by simp) _ (by simp) (fun e => ne (congrArg z (wy.1.1 e))) (mapWithin wy.1 dist)

end Lax977378Proofs.WindowColour
