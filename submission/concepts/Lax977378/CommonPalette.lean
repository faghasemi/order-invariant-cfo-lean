import Lax977378.ColouredTypes

/-!
---
title: A common palette of frequent coloured types determined by the count vector
type: lemma
---
Fix a nondecreasing allowance for exceptions as a function of the number of
rare vertices. Thresholds and the catalogue of coloured requests then depend
only on the capped vector. Each graph with this vector admits a proper
colouring extending any permitted precolouring. Every request still occurs
outside any subsequently chosen set within the allowance.
-/
namespace Lax977378.CommonPalette
open Lax977378.Logic Lax977378.Planting Lax977378.RecordTests Lax977378.CountParameters

axiom uniform (c d r q : Nat) (palette : (d+1)^(r+r) ≤ q)
    (g : Nat → Nat) (mono : Monotone g) :
    ∃ n : Nat, ∃ types : Fin n → Pointed c, ∃ cap : Nat,
    ∃ threshold : (Fin n → Nat) → Nat, ∃ seeds : (Fin n → Nat) → List (Request c q),
    ∀ (G : Graph c), G.Bounded d →
      let v := fun j => min cap (locations (types j) r G).card
      let t := threshold v
      let Z := rareSet types r G v t
      0 < t ∧ t ≤ cap ∧ Z.card ≤ n*(cap-1) ∧
      (∀ κ, ProperOn G (r+r) Finset.univ κ → ∀ x ∉ Z,
        ∃ s ∈ seeds v, Realised s G r κ x) ∧
      ∀ (P : Finset (Fin G.size)) (colour : Fin G.size → Fin q),
        P.card ≤ g Z.card → ProperOn G (r+r) P colour →
        ∃ k, (∀ u ∈ P, k u = colour u) ∧ ProperOn G (r+r) Finset.univ k ∧
          ∀ s ∈ seeds v, ∀ M : Finset (Fin G.size), M.card ≤ g Z.card →
            ∃ x ∉ M, Realised s G r k x

end Lax977378.CommonPalette
