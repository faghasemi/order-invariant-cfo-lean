import Lax977378.RecordTests

/-!
---
title: Finite catalogue of bounded-degree neighbourhoods
type: lemma
---
For a fixed vocabulary, degree and radius there is a finite list of pointed
graphs covering all rooted neighbourhoods. Occurrence means an isomorphism
onto the entire induced ball, including its boundary. Numberings of a ball
can give repeated entries; the catalogue makes no uniqueness claim.
-/
namespace Lax977378.Catalogue
open Lax977378.Logic Lax977378.RecordTests

axiom catalogue (c d r : Nat) : ∃ ts : List (Pointed c),
  ∀ G : Graph c, G.Bounded d → ∀ x, ∃ t ∈ ts, Occurs t r G x

end Lax977378.Catalogue
