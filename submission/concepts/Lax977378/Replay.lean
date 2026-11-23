import Lax977378.Collapse
import Lax977378.RecordTests

/-!
---
title: Assembling checked record tests after replay
type: lemma
---
A finite list pairs the unordered data with the set of labels in the final
table. Replay on each individual passing graph supplies a compatible order.
The resulting orders satisfy the pairwise form of the record theorem.
-/
namespace Lax977378.Replay
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Collapse Lax977378.RecordTests

axiom assemble {c d K N} (lab : (G : Graph c) → G.Bounded d →
    LinearOrder (Fin G.size) → Fin G.size → Fin N)
    (sound : ∀ A B ha hb a b x y, lab A ha a x = lab B hb b y → same A B a b K x y)
    (entries : List (TestData c × Finset (Fin N)))
    (cover : ∀ G : Graph c, G.Bounded d → ∃ e ∈ entries, Passes e.1 G)
    (replay : ∀ e ∈ entries, ∀ (G : Graph c) (hd : G.Bounded d), Passes e.1 G →
      ∃ a, Finset.univ.image (lab G hd a) = e.2) :
    ∃ tests : List (Record (c := c) d K), ∀ G, G.Bounded d → ∃ e ∈ tests, Unordered G e.test

end Lax977378.Replay
