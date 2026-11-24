import Lax977378.RecordTests

/-!
---
title: Quantifier rank of a sentence describing counts and a marked neighbourhood
type: lemma
---
Fix a finite graph vocabulary, a radius $r$ for pointed types, a window
radius $R$, a finite graph $W$ with two distinguished subsets of vertices,
a count cap $t$, a list of pointed types with prescribed counts up to $t$,
and a list of frequent types. Suppose all listed pointed patterns have at
most $b$ vertices, the prescribed counts are at most $t$, and $|W|\le U$.
There is an order-free first-order sentence of rank at most
$\max(b+r+t+4,U+\max(R,b+r)+5)$ with the following meaning.
Each specified count below $t$ is exact, and a count equal to $t$ is a
lower bound. There is an induced copy of $W$ whose vertex set is the full
radius-$R$ neighbourhood of the first distinguished subset. The image of
the second distinguished subset consists exactly of the vertices whose
radius-$r$ type is absent from the list of frequent types.
-/
namespace Lax266678.WindowRank
open Lax977378.Logic Lax977378.RecordTests

def bound (b r cap U R : Nat) : Nat := max (b+r+cap+4) (U+max R (b+r)+5)

axiom windowSentence {c : Nat} (D : TestData c) (b U : Nat)
    (counts : ∀ e ∈ D.counts, e.1.pattern.size ≤ b ∧ e.2 ≤ D.cap)
    (freq : ∀ e ∈ D.frequent, e.pattern.size ≤ b) (size : D.windowGraph.size ≤ U) :
    ∃ f : Formula c, Plain [] f ∧ rank f ≤ bound b D.radius D.cap U D.windowRadius ∧
      ∀ G, Unordered G f ↔ Passes D G

end Lax266678.WindowRank
