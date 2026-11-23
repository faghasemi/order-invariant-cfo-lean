import Lax977378.OuterContexts

/-!
---
title: Finitely many outer-context labels at each level
type: lemma
---
At each fixed rank and degree bound, every vertex of every ordered graph can
be assigned one of finitely many labels. Equality of labels is equivalent to
agreement of the outer contexts, also when the graph sizes or orders differ.
This supplies the uniform bound on the number of labels used to refine a block.
-/

namespace Lax977378.ContextLabels
open Lax977378.Logic Lax977378.OuterContexts

axiom finiteLabels (c d i : Nat) :
    ∃ N : Nat, ∃ label : (G : Graph c) → G.Bounded d →
        LinearOrder (Fin G.size) → Fin G.size → Fin N,
      ∀ A B ha hb a b x y, label A ha a x = label B hb b y ↔ same A B a b i x y

end Lax977378.ContextLabels
