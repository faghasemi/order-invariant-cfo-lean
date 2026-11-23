import Lax977378.Window

/-!
---
title: Corresponding recursive balls inside a common named window
type: lemma
---
Two realisations of the same window identify the full balls around
corresponding interior vertices. The identification respects every vertex
name in the window, including on the boundary of the inspected ball.
-/
namespace Lax977378.WindowMap
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests

axiom matchBall {c s p r} (W A B : Graph c) (mark : Finset (Fin W.size))
    (y : Fin W.size → Fin A.size) (z : Fin W.size → Fin B.size)
    (wy : Window W A (s+p) mark y) (wz : Window W B (s+p) mark z)
    (u : Fin W.size) (hu : ∃ m ∈ mark, within W s m u) (hr : r ≤ p) :
    ∃ h : Ball A r (y u) ≃ Ball B r (z u),
      (∀ v j, v.val = y j ↔ (h v).val = z j) ∧
      (∀ v, ∃ j, within W r u j ∧ v.val = y j ∧ (h v).val = z j) ∧
      (∀ v w, A.edge v.val w.val ↔ B.edge (h v).val (h w).val)

end Lax977378.WindowMap
