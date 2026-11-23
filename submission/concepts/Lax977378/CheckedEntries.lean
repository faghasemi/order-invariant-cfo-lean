import Lax977378.Replay
import Lax977378.FiniteTests

/-!
---
title: Finite selection of tests with a replayable final table
type: lemma
---
Once the unordered data and the final labels range over finite sets, one can
retain exactly the pairs for which every passing graph admits a suitable order.
It suffices to exhibit one such pair for each individual bounded-degree graph.
Intermediate tables may be used to prove replay without encoding them in FO.
-/
namespace Lax977378.CheckedEntries
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests Lax977378.Collapse

axiom selectEntries {c d K n N} (types : Fin n → Pointed c) (r R cap U : Nat)
    (lab : (G : Graph c) → G.Bounded d → LinearOrder (Fin G.size) → Fin G.size → Fin N)
    (sound : ∀ A B ha hb a b x y, lab A ha a x = lab B hb b y → same A B a b K x y)
    (witness : ∀ A : Graph c, A.Bounded d →
      ∃ (D : TestData c) (S : Finset (Fin N)) (v : Fin n → Fin (cap+1)) (t : Nat),
        D.radius = r ∧ D.windowRadius = R ∧ D.cap = cap ∧ D.windowGraph.size ≤ U ∧
        D.counts = List.ofFn (fun j => (types j,(v j).val)) ∧
        D.frequent = ((List.finRange n).filter (fun j => t ≤ (v j).val)).map types ∧
        Passes D A ∧ ∀ (B : Graph c) (hb : B.Bounded d), Passes D B →
          ∃ b, Finset.univ.image (lab B hb b) = S) :
    ∃ tests : List (Record (c := c) d K), ∀ G, G.Bounded d → ∃ e ∈ tests, Unordered G e.test

end Lax977378.CheckedEntries
