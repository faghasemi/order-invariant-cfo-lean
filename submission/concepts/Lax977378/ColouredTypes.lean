import Lax977378.Reservoir

/-!
---
title: The list of coloured frequent neighbourhood types
type: lemma
---
Enumerate every injective palette assignment to a frequent uncoloured pattern.
In a proper colouring of the graph power this list covers every nonrare
vertex. Its length is bounded before the frequency vector is chosen.
-/
namespace Lax977378.ColouredTypes
open Lax977378.Logic Lax977378.Planting Lax977378.RecordTests Lax977378.CountParameters

axiom colouredTypes {c n} (types : Fin n → Pointed c) (q : Nat) : ∃ H : Nat,
    ∀ (v : Fin n → Nat) (t : Nat), ∃ seeds : List (Request c q), seeds.length ≤ H ∧
      (∀ s ∈ seeds, ∃ j, t ≤ v j ∧ s.type = types j) ∧
      ∀ (G : Graph c) (r : Nat) (κ : Fin G.size → Fin q),
        ProperOn G (r+r) Finset.univ κ → ∀ x, x ∉ rareSet types r G v t →
          ∃ s ∈ seeds, Realised s G r κ x

end Lax977378.ColouredTypes
