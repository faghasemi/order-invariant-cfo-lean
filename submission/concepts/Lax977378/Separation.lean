import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
---
title: Simultaneous separated choices and extension of a partial colouring
type: lemma
---
The separation statement allows repeated requests for the same neighbourhood
type. The forbidden set initially includes the excluded region and after each
choice includes the entire forbidden ball around the chosen centre.

A symmetric list of neighbours describes the graph power. A partial proper
colouring extends with a palette larger than every list of neighbours.
-/
namespace Lax977378.Separation

axiom separated {V : Type} [DecidableEq V] (halo : V → Finset V)
    (H : Nat) (bound : ∀ x, (halo x).card ≤ H)
    (requests : List (Finset V)) (excluded : Finset V)
    (enough : ∀ s ∈ requests, excluded.card + requests.length * H < s.card) :
    ∃ centres : List V, List.Forall₂ (fun x s => x ∈ s) centres requests ∧
      (∀ x ∈ centres, x ∉ excluded) ∧ centres.Pairwise (fun x y => y ∉ halo x)

axiom extendColouring {V : Type} [Fintype V] [DecidableEq V] (nb : V → Finset V)
    (symm : ∀ x y, x ∈ nb y → y ∈ nb x) (loopless : ∀ x, x ∉ nb x)
    (q : Nat) (bound : ∀ x, (nb x).card < q) (P : Finset V) (colour : V → Fin q)
    (proper : ∀ x ∈ P, ∀ y ∈ P, y ∈ nb x → colour x ≠ colour y) :
    ∃ κ : V → Fin q, (∀ x ∈ P, κ x = colour x) ∧ ∀ x y, y ∈ nb x → κ x ≠ κ y

end Lax977378.Separation
