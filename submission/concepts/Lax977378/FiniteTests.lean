import Lax977378.Extraction

/-!
---
title: A uniform finite list of count and window tests
type: lemma
---
Fix the vocabulary, both radii, count cap, catalogue and window size bound.
The whole unordered part of the record ranges over a single finite list.
The same sentence assigned to an entry tests it on every graph.
-/
namespace Lax977378.FiniteTests
open Lax977378.Logic Lax977378.RecordTests

axiom finiteTests {c n} (types : Fin n → Pointed c) (r R cap U : Nat) :
    ∃ tests : List (TestData c × Formula c),
      (∀ e ∈ tests, Plain [] e.2 ∧ ∀ G, Unordered G e.2 ↔ Passes e.1 G) ∧
      ∀ D : TestData c, D.radius = r → D.windowRadius = R → D.cap = cap →
        D.windowGraph.size ≤ U → ∀ (v : Fin n → Fin (cap+1)) (t : Nat),
        D.counts = List.ofFn (fun j => (types j,(v j).val)) →
        D.frequent = ((List.finRange n).filter (fun j => t ≤ (v j).val)).map types →
        ∃ f, (D,f) ∈ tests

end Lax977378.FiniteTests
