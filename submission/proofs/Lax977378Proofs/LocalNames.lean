import Lax977378.LocalNames
import Lax977378Proofs.Catalogue

namespace Lax977378Proofs.LocalNames
open Lax977378.Logic Lax977378.Blocks Lax977378.OuterContexts Lax977378.CallAgreement

/--
---
conclusion: Lax977378.LocalNames.names
assumptions:
  - Lax977378.Refinement.levelStep
---
The lower calls determine all parent rows on the ball, including the root
row. Endpoint roles and the common preceding table then determine the new
context. Apply the rule defining the child groups.
-/
theorem names {c K} (A : Graph c) (a : LinearOrder (Fin A.size)) (n : Nat → Nat)
    (P : (j : Nat) → @Partition (Fin A.size) (Fin (n j)) a inferInstance)
    (ra ea : Nat → Fin A.size → Nat)
    (base : ∀ x y, ra 0 x = ra 0 y → (P 0).block x = (P 0).block y)
    (child : ∀ j < K, ∀ x y, ra (j+1) x = ra (j+1) y →
      (P j).block x = (P j).block y → same A A a a (j+1) x y →
      (P (j+1)).block x = (P (j+1)).block y)
    (hom : ∀ j < K, ∀ x y, (P j).block x = (P j).block y → same A A a a j x y)
    (separated : ∀ j < K, ∀ x, Function.Injective (fun v : Ball A (j+1) x => (P j).block v.val))
    (roles : ∀ j < K, ∀ x y, ea (j+1) x = ea (j+1) y →
      (x = (P j).first ((P j).block x) ↔ y = (P j).first ((P j).block y)) ∧
      (x = (P j).last ((P j).block x) ↔ y = (P j).last ((P j).block y))) :
    ∀ j ≤ K, ∀ x y, agrees A A ra ea ra ea j x y → (P j).block x = (P j).block y := by
  intro j
  induction j with
  | zero => exact fun _ x y h => base x y h
  | succ j ih =>
    intro hj x y data
    obtain ⟨r,h,root,edge,calls⟩ := data
    have rows (v) := ih (by omega) _ _ (calls v).2
    let u : Ball A (j+1) x := ⟨x,Catalogue.centerWithin ..⟩
    have hy := (root u).mp (show u.val = x from rfl)
    apply child j (by omega) x y r (by simpa only [hy,u] using rows u)
    exact Lax977378.Refinement.levelStep A A a a (P j) (P j) (hom j (by omega)) x y h
      root edge (separated j (by omega) x) rows
      (fun v => (roles j (by omega) _ _ (calls v).1).1)
      (fun v => (roles j (by omega) _ _ (calls v).1).2)

end Lax977378Proofs.LocalNames
