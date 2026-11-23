import Lax977378.OuterContexts

/-!
---
title: Locality of the calculation without tags
type: lemma
---
At stage i+1 the exceptional region contains the radius-ρ(i+1) balls
around the previous exceptional region and the newly chosen endpoints.
An ordinary root therefore sees no current endpoint on its inspected ball,
and each recursive call at a ball vertex sees no previous exceptional tag.
-/
namespace Lax977378.TagSafety
open Lax977378.Logic Lax977378.OuterContexts

def radius : Nat → Nat
  | 0 => 0
  | i+1 => radius i + (i+1)

axiom ordinaryCalls {c i} {G : Graph c} (previous endpoints current : Finset (Fin G.size))
    (covered : ∀ u ∈ previous ∪ endpoints, ∀ x, within G (radius (i+1)) u x → x ∈ current)
    {x} (ordinary : x ∉ current) {v} (hv : within G (i+1) x v) :
    v ∉ endpoints ∧ ∀ w, within G (radius i) v w → w ∉ previous

end Lax977378.TagSafety
