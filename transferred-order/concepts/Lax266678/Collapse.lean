import Lax266678.Definability

/-!
---
title: Order-invariant cluster first-order logic is included in first-order logic on bounded-degree graphs
type: theorem
---
Fix a finite vocabulary consisting of adjacency and $c$ unary predicates.
A closed cluster first-order sentence $f$ over this vocabulary with an
additional linear order is order-invariant if, for every finite simple graph
$G$ over the vocabulary and every two linear orders on its vertices, $f$ has
the same truth value in the two ordered graphs. For every such $f$, every
natural number $d$, and every class $C$ of finite graphs of maximum degree
at most $d$, there exists a closed first-order sentence over adjacency and
the unary predicates that agrees with $f$ on every graph in $C$ under every
linear order on its vertices.
-/
namespace Lax266678.Collapse
open Lax977378.Logic

axiom orderInvariantCFO_in_FO {c d : Nat} (C : Graph c → Prop)
    (bounded : ∀ G, C G → G.Bounded d) (f : Formula c) (legal : Legal [] f)
    (inv : ∀ G : Graph c, ∀ a b, Holds G a f ↔ Holds G b f) :
    ∃ φ : Formula c, Plain [] φ ∧ ∀ G, C G → ∀ a, Holds G a f ↔ Unordered G φ

end Lax266678.Collapse
