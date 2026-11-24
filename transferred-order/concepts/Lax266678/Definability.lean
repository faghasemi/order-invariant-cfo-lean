import Lax266678.Transfer

/-!
---
title: First-order definability from agreement at bounded rank
type: lemma
---
Fix a finite graph vocabulary with $c$ unary predicates, a class $C$ of finite
graphs, a property $P$ of finite graphs and a natural number $q$. Suppose
that whenever two members of $C$ agree on all order-free first-order
sentences of quantifier rank at most $q$, either both have $P$ or neither
does. Then a single order-free first-order sentence defines $P$ on $C$.
-/
namespace Lax266678.Definability
open Lax977378.Logic Lax266678.Transfer

axiom definable {c : Nat} (C P : Graph c → Prop) (q : Nat)
    (stable : ∀ A B, C A → C B → equivalentAt q A B → (P A ↔ P B)) :
    ∃ f : Formula c, Plain [] f ∧ ∀ A, C A → (P A ↔ Unordered A f)

end Lax266678.Definability
