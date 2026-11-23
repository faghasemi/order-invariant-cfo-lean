import Lax977378.CallAgreement

/-!
---
title: The recursive calculation without tags at ordinary vertices
type: lemma
---
Agreement of the untagged coloured inputs gives agreement of the tagged
calculations outside the exceptional regions. Only the endpoint roles read
at the current stage and the exceptional vertices read by lower calls matter.
-/
namespace Lax977378.OrdinaryCalls
open Lax977378.Logic Lax977378.OuterContexts Lax977378.LocalCalls Lax977378.TagSafety

def Covers {c} (G : Graph c) (K : Nat) (X E : Nat → Finset (Fin G.size)) : Prop :=
  ∀ j < K, ∀ u ∈ X j ∪ E (j+1), ∀ x, within G (radius (j+1)) u x → x ∈ X (j+1)

axiom untagged {c K} (A B : Graph c) (X E : Nat → Finset (Fin A.size))
    (Y F : Nat → Finset (Fin B.size)) (coverA : Covers A K X E) (coverB : Covers B K Y F)
    (colour root ends : Nat → Fin A.size → Fin B.size → Prop)
    (ordinary : ∀ j ≤ K, ∀ x ∉ X j, ∀ y ∉ Y j, colour j x y → root j x y)
    (interior : ∀ j < K, ∀ x ∉ E (j+1), ∀ y ∉ F (j+1), ends (j+1) x y) :
    ∀ j ≤ K, ∀ x ∉ X j, ∀ y ∉ Y j, Calls A B colour (fun _ _ _ => True) j x y →
      Calls A B root ends j x y

end Lax977378.OrdinaryCalls
