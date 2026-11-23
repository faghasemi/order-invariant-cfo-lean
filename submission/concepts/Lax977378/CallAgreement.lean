import Lax977378.LocalCalls

/-!
---
title: Comparison of different representatives of a recursive call
type: lemma
---
Data read at each vertex can be represented by labels. Two source vertices
matching the same target call can be compared by composing their local
correspondences. A match at the full rank gives matches at every lower rank
at the same centre.
-/
namespace Lax977378.CallAgreement
open Lax977378.Logic Lax977378.LocalCalls

def agrees {c} (A B : Graph c)
    (ra ea : Nat → Fin A.size → Nat) (rb eb : Nat → Fin B.size → Nat) :=
  Calls A B (fun j x y => ra j x = rb j y) (fun j x y => ea j x = eb j y)

axiom compareReps {c} (A B : Graph c) (ra ea : Nat → Fin A.size → Nat)
    (rb eb : Nat → Fin B.size → Nat) (i : Nat) (x u : Fin A.size) (y : Fin B.size)
    (hx : agrees A B ra ea rb eb i x y) (hu : agrees A B ra ea rb eb i u y) :
    agrees A A ra ea ra ea i x u

axiom lowerRanks {c} (A B : Graph c) (ra ea : Nat → Fin A.size → Nat)
    (rb eb : Nat → Fin B.size → Nat) (i j : Nat) (hj : j ≤ i) (x y)
    (h : agrees A B ra ea rb eb i x y) : agrees A B ra ea rb eb j x y

end Lax977378.CallAgreement
