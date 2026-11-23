import Lax977378.WindowMap
import Mathlib.Tactic

namespace Lax977378Proofs.WindowMap
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests

private theorem identify {c s p r} (W A : Graph c) (mark : Finset (Fin W.size))
    (y : Fin W.size → Fin A.size) (wy : Window W A (s+p) mark y)
    (u : Fin W.size) (hu : ∃ m ∈ mark, within W s m u) (hr : r ≤ p) :
    ∃ e : Ball W r u ≃ Ball A r (y u), ∀ j, (e j).val = y j.val := by
  classical
  have cover := Lax977378.Window.exactBall wy hu r hr
  let f (j : Ball W r u) : Ball A r (y u) := ⟨y j.val,(cover _).mpr ⟨j.val,j.property,rfl⟩⟩
  have inj : Function.Injective f := fun _ _ h => Subtype.ext (wy.1.1 (congrArg Subtype.val h))
  have onto : Function.Surjective f := by
    intro v
    obtain ⟨j,hj,he⟩ := (cover _).mp v.property
    exact ⟨⟨j,hj⟩,Subtype.ext he⟩
  exact ⟨Equiv.ofBijective f ⟨inj,onto⟩,fun _ => rfl⟩

/--
---
conclusion: Lax977378.WindowMap.matchBall
assumptions:
  - Lax977378.Window.exactBall
---
Both ambient balls are enumerated by the same inner ball of the window.
Compose the two enumerations and use the induced diagrams for edges.
-/
theorem matchBall {c s p r} (W A B : Graph c) (mark : Finset (Fin W.size))
    (y : Fin W.size → Fin A.size) (z : Fin W.size → Fin B.size)
    (wy : Window W A (s+p) mark y) (wz : Window W B (s+p) mark z)
    (u : Fin W.size) (hu : ∃ m ∈ mark, within W s m u) (hr : r ≤ p) :
    ∃ h : Ball A r (y u) ≃ Ball B r (z u),
      (∀ v j, v.val = y j ↔ (h v).val = z j) ∧
      (∀ v, ∃ j, within W r u j ∧ v.val = y j ∧ (h v).val = z j) ∧
      (∀ v w, A.edge v.val w.val ↔ B.edge (h v).val (h w).val) := by
  obtain ⟨e,he⟩ := identify W A mark y wy u hu hr
  obtain ⟨f,hf⟩ := identify W B mark z wz u hu hr
  let h := e.symm.trans f
  have left (v : Ball A r (y u)) : v.val = y (e.symm v).val := by simpa using he (e.symm v)
  have right (v : Ball A r (y u)) : (h v).val = z (e.symm v).val := hf _
  refine ⟨h,?_,fun v => ⟨_,(e.symm v).property,left v,right v⟩,?_⟩
  · intro v j
    rw [left v,right v,wy.1.1.eq_iff,wz.1.1.eq_iff]
  · intro v w
    rw [left v,left w,right v,right w,←wy.1.2.1,←wz.1.2.1]

end Lax977378Proofs.WindowMap
