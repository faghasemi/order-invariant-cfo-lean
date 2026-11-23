import Lax977378.WindowMap
import Lax977378.TagSafety

/-!
---
title: Agreement of all recursive calls in a common coloured and tagged ball
type: lemma
---
At level zero the calculation reads the root data. At a positive level it
compares root data, reads endpoint roles on the inspected ball, and invokes
the preceding calculation at each ball vertex. A common named window with
matching data supplies the whole recursive comparison, with consistent names.
-/
namespace Lax977378.LocalCalls
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests Lax977378.TagSafety

def Calls {c} (A B : Graph c)
    (root ends : Nat → Fin A.size → Fin B.size → Prop) :
    Nat → Fin A.size → Fin B.size → Prop
  | 0,x,y => root 0 x y
  | i+1,x,y => root (i+1) x y ∧ ∃ h : Ball A (i+1) x ≃ Ball B (i+1) y,
    (∀ v, v.val = x ↔ (h v).val = y) ∧
    (∀ v w, A.edge v.val w.val ↔ B.edge (h v).val (h w).val) ∧
    ∀ v, ends (i+1) v.val (h v).val ∧ Calls A B root ends i v.val (h v).val

axiom commonCalls {c} (W A B : Graph c) (mark : Finset (Fin W.size))
    (y : Fin W.size → Fin A.size) (z : Fin W.size → Fin B.size)
    (root ends : Nat → Fin A.size → Fin B.size → Prop) (i s : Nat)
    (wy : Window W A (s+radius i) mark y) (wz : Window W B (s+radius i) mark z)
    (data : ∀ j ≤ i, ∀ u, root j (y u) (z u) ∧ ends j (y u) (z u))
    (u : Fin W.size) (near : ∃ m ∈ mark, within W s m u) :
    Calls A B root ends i (y u) (z u)

axiom innerCalls {c} (W A B : Graph c) (mark : Finset (Fin W.size))
    (y : Fin W.size → Fin A.size) (z : Fin W.size → Fin B.size)
    (root ends : Nat → Fin A.size → Fin B.size → Prop) (i s slack : Nat)
    (wy : Window W A (s+radius i+slack) mark y) (wz : Window W B (s+radius i+slack) mark z)
    (data : ∀ j ≤ i, ∀ u, (∃ m ∈ mark, within W (s+radius i) m u) →
      root j (y u) (z u) ∧ ends j (y u) (z u))
    (u : Fin W.size) (near : ∃ m ∈ mark, within W s m u) :
    Calls A B root ends i (y u) (z u)

end Lax977378.LocalCalls
