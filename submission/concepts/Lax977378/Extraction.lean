import Lax977378.CountParameters

/-!
---
title: Extracting the unordered test from an exceptional set
type: lemma
---
Take the actual truncated counts and an exceptional set containing the rare
vertices. The graph supplies a bounded induced window, with the exceptional
and rare vertices named, and satisfies the resulting unordered record test.
-/
namespace Lax977378.Extraction
open Lax977378.Logic Lax977378.RecordTests Lax977378.CountParameters

axiom extract {c d n} (G : Graph c) (hd : G.Bounded d) (r R cap t : Nat)
    (types : Fin n → Pointed c) (M : Finset (Fin G.size))
    (v : Fin n → Nat) (counts : ∀ j, v j = min cap (locations (types j) r G).card)
    (contains : rareSet types r G v t ⊆ M) :
    ∃ D : TestData c, D.radius = r ∧ D.windowRadius = R ∧ D.cap = cap ∧
      D.counts = List.ofFn (fun j => (types j,v j)) ∧
      D.frequent = ((List.finRange n).filter (fun j => t ≤ v j)).map types ∧
      D.windowGraph.size ≤ M.card * (d+1)^R ∧
      (∃ y, Window D.windowGraph G R D.marked y ∧ D.marked.image y = M ∧
        D.rare.image y = rareSet types r G v t) ∧ Passes D G ∧
      ∃ f, Plain [] f ∧ Unordered G f ∧ ∀ B, Unordered B f ↔ Passes D B

end Lax977378.Extraction
