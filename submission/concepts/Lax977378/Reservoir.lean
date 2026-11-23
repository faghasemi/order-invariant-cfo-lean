import Lax977378.Planting

/-!
---
title: A coloured realisation survives each bounded exceptional set
type: lemma
---
Prescribe m copies of every requested coloured type in one colouring. After
the colouring has been chosen, every set of fewer than m vertices misses
at least one realisation of each request.
-/
namespace Lax977378.Reservoir
open Lax977378.Logic Lax977378.OuterContexts Lax977378.CountParameters Lax977378.Planting

axiom reserve {c d q} (G : Graph c) (hd : G.Bounded d) (r p m : Nat)
    (palette : (d+1)^p ≤ q) (P : Finset (Fin G.size)) (colour : Fin G.size → Fin q)
    (proper : ProperOn G p P colour) (seeds : List (Request c q))
    (enough : ∀ s ∈ seeds, (P.card + (seeds.length*m) * (d+1)^r) * (d+1)^(2*r+p) <
      (locations s.type r G).card) :
    ∃ k : Fin G.size → Fin q, (∀ u ∈ P, k u = colour u) ∧ ProperOn G p Finset.univ k ∧
      ∀ s ∈ seeds, ∀ M : Finset (Fin G.size), M.card < m →
        ∃ x ∉ M, Realised s G r k x ∧ ∀ u ∈ P, ¬ within G (2*r+p) u x

end Lax977378.Reservoir
