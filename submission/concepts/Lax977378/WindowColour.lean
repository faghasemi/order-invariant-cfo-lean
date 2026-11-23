import Lax977378.TargetWindow
import Lax977378.Window

/-!
---
title: Transporting the exceptional precolouring to a passing graph
type: lemma
---
Only the inner neighbourhood of the marked set is prescribed. Its colours
are proper in the target graph power because each relevant path stays in
the larger window. The number of prescribed vertices is bounded using the
degree bound, independently of the ambient graph size.
-/
namespace Lax977378.WindowColour
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests Lax977378.Planting

axiom precolour {c d q r p} (W A B : Graph c) (hd : B.Bounded d) (mark : Finset (Fin W.size))
    (y : Fin W.size → Fin A.size) (z : Fin W.size → Fin B.size)
    (wy : Window W A (r+p) mark y) (wz : Window W B (r+p) mark z)
    (κ : Fin A.size → Fin q) (proper : ProperOn A p Finset.univ κ) (nonempty : 0 < q) :
    ∃ (P : Finset (Fin B.size)) (paint : Fin B.size → Fin q),
      P.card ≤ mark.card*(d+1)^r ∧ ProperOn B p P paint ∧
      (∀ j, (∃ m ∈ mark, within W r m j) → z j ∈ P ∧ paint (z j) = κ (y j))

end Lax977378.WindowColour
