import Lax977378.OuterContexts

/-!
---
title: Transferring a refinement order between first-order equivalent graphs
type: theorem
---
Fix $c$ unary predicates, a maximum degree $d$ and a context depth $k$.
There is a rank $q$ such that every finite simple graph $A$ of degree at most
$d$ admits a linear order $a$ with the following property. For every finite
simple graph $B$ in the same vocabulary of degree at most $d$ which agrees
with $A$ on every order-free first-order sentence of quantifier rank at most
$q$, there is a linear order $b$ on $B$ such that $(A,a)$ and $(B,b)$ realise
the same outer $k$-contexts. The source order is chosen before $B$.
-/
namespace Lax266678.Transfer
open Lax977378.Logic Lax977378.OuterContexts

def equivalentAt {c : Nat} (q : Nat) (A B : Graph c) : Prop :=
  ∀ f : Formula c, Plain [] f → rank f ≤ q → (Unordered A f ↔ Unordered B f)

axiom transferOrder (c d k : Nat) : ∃ q : Nat, ∀ A : Graph c, A.Bounded d →
  ∃ a : LinearOrder (Fin A.size), ∀ B : Graph c, B.Bounded d → equivalentAt q A B →
    ∃ b : LinearOrder (Fin B.size), spectrumAgrees A B a b k

end Lax266678.Transfer
