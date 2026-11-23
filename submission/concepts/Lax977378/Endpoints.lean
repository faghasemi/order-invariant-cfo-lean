import Mathlib.Data.Finset.Sort
import Lax977378.Blocks
import Mathlib.Data.Finset.Card

/-!
---
title: Choosing and realising endpoints in the ordinary blocks
type: lemma
---
Outside the exceptional set, all planted centres with the same coloured type
belong to the same block whenever the calculation without tags gives its name.
Two of these centres survive if the multiplicity exceeds the exceptional bound
by two. Every simultaneous choice of legal endpoint pairs is realised by an
order on the individual graph.
-/
namespace Lax977378.Endpoints
open Lax977378.Blocks

axiom twoCentres {V I : Type} [DecidableEq V] (block : V → I) (i : I)
    (Γ S : Finset V) (enough : Γ.card + 2 ≤ S.card)
    (ordinary : ∀ x ∈ S, x ∉ Γ → block x = i) :
    ∃ u ∈ S, ∃ v ∈ S, u ∉ Γ ∧ v ∉ Γ ∧ u ≠ v ∧ block u = i ∧ block v = i

axiom admissible {n m : Nat} (block : Fin n → Fin m) (first last : Fin m → Fin n)
    (hf : ∀ i, block (first i) = i) (hl : ∀ i, block (last i) = i)
    (singleton : ∀ i, first i = last i → ∀ x, block x = i → x = first i) :
    ∃ a : LinearOrder (Fin n), ∃ P : @Partition (Fin n) (Fin m) a inferInstance,
      P.block = block ∧ P.first = first ∧ P.last = last

end Lax977378.Endpoints
