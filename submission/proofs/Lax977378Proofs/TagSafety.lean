import Lax977378.TagSafety
import Lax977378Proofs.Planting

namespace Lax977378Proofs.TagSafety
open Lax977378.Logic Lax977378.OuterContexts Lax977378.TagSafety
open Lax977378Proofs.Planting Lax977378Proofs.Window

/--
---
conclusion: Lax977378.TagSafety.ordinaryCalls
---
A path from a lower call to a previously exceptional vertex, followed in
reverse back to the root, would put the root in the current exceptional set.
-/
theorem ordinaryCalls {c i} {G : Graph c} (previous endpoints current : Finset (Fin G.size))
    (covered : ∀ u ∈ previous ∪ endpoints, ∀ x, within G (radius (i+1)) u x → x ∈ current)
    {x} (ordinary : x ∉ current) {v} (hv : within G (i+1) x v) :
    v ∉ endpoints ∧ ∀ w, within G (radius i) v w → w ∉ previous := by
  constructor
  · intro he
    exact ordinary (covered v (Finset.mem_union_right _ he) x
      (grow (reverseWithin hv) (by simp [radius])))
  · intro w hw hp
    exact ordinary (covered w (Finset.mem_union_left _ hp) x
      (join (reverseWithin hw) (reverseWithin hv)))

end Lax977378Proofs.TagSafety
