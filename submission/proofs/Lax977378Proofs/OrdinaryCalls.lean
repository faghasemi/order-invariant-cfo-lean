import Lax977378.OrdinaryCalls
import Lax977378Proofs.Catalogue

namespace Lax977378Proofs.OrdinaryCalls
open Lax977378.Logic Lax977378.OuterContexts Lax977378.LocalCalls Lax977378.TagSafety Lax977378.OrdinaryCalls

/--
---
conclusion: Lax977378.OrdinaryCalls.untagged
assumptions:
  - Lax977378.TagSafety.ordinaryCalls
---
The two ball vertices are both interior at this stage and both ordinary at
the previous stage. Induct on the remaining rank at that pair of vertices.
-/
theorem untagged {c K} (A B : Graph c) (X E : Nat → Finset (Fin A.size))
    (Y F : Nat → Finset (Fin B.size)) (coverA : Covers A K X E) (coverB : Covers B K Y F)
    (colour root ends : Nat → Fin A.size → Fin B.size → Prop)
    (ordinary : ∀ j ≤ K, ∀ x ∉ X j, ∀ y ∉ Y j, colour j x y → root j x y)
    (interior : ∀ j < K, ∀ x ∉ E (j+1), ∀ y ∉ F (j+1), ends (j+1) x y) :
    ∀ j ≤ K, ∀ x ∉ X j, ∀ y ∉ Y j, Calls A B colour (fun _ _ _ => True) j x y →
      Calls A B root ends j x y := by
  intro j
  induction j with
  | zero => exact fun h x hx y hy hc => ordinary _ h x hx y hy hc
  | succ j ih =>
    intro hj x hx y hy hc
    obtain ⟨hr,h,center,edges,children⟩ := hc
    refine ⟨ordinary _ hj _ hx _ hy hr,h,center,edges,?_⟩
    intro v
    have left := Lax977378.TagSafety.ordinaryCalls (X j) (E (j+1)) (X (j+1))
      (coverA j (by omega)) hx v.property
    have right := Lax977378.TagSafety.ordinaryCalls (Y j) (F (j+1)) (Y (j+1))
      (coverB j (by omega)) hy (h v).property
    exact ⟨interior j (by omega) _ left.1 _ right.1,
      ih (by omega) _ (left.2 _ (Catalogue.centerWithin ..)) _
        (right.2 _ (Catalogue.centerWithin ..)) (children v).2⟩

end Lax977378Proofs.OrdinaryCalls
