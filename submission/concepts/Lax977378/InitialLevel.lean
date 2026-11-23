import Lax977378.Collapse

/-!
---
title: The initial case of the order construction
type: lemma
---
For outer contexts at level zero, the possible labels are just the truth
tables of the unary predicates at a vertex. One unordered sentence describes
the set of realised labels exactly, and any order can be used.
-/
namespace Lax977378.InitialLevel

open Lax977378.Logic Lax977378.Collapse

axiom initialRecords (c d : Nat) : ∃ tests : List (Record (c := c) d 0),
  ∀ G, G.Bounded d → ∃ e ∈ tests, Unordered G e.test

end Lax977378.InitialLevel
