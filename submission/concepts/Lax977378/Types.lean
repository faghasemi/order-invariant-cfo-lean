import Lax977378.Catalogue

/-!
---
title: A list of neighbourhood types without duplicate isomorphism classes
type: lemma
---
For fixed degree and radius the catalogue can be chosen so that each vertex
realises exactly one entry. This permits summing occurrence counts over rare
types without counting any vertex twice.
-/
namespace Lax977378.Types
open Lax977378.Logic Lax977378.RecordTests

axiom uniqueTypes (c d r : Nat) :
    ∃ n : Nat, ∃ t : Fin n → Pointed c,
      ∀ G : Graph c, G.Bounded d → ∀ x, ∃! j, Occurs (t j) r G x

end Lax977378.Types
