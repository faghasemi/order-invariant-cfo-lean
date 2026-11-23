import Lax977378.SourceRun
import Lax977378.Planting

/-!
---
title: Bounded source run from a coloured graph and its rare vertices
type: lemma
---
Every rare vertex starts in a singleton. Other vertices start together
exactly when their unary predicates and auxiliary colour agree. A proper
colouring of the graph power makes the initial rows distinct on each
inspected ball. The whole history can then be constructed up to rank K.
-/
namespace Lax977378.ColouredRun
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Planting Lax977378.SourceRun Lax977378.Stage

axiom colouredRun (c d K : Nat) : ∃ N : Nat → Nat, ∀ (G : Graph c), G.Bounded d →
    ∀ (q : Nat) (κ : Fin G.size → Fin q), ProperOn G (K+K) Finset.univ κ →
    ∀ Z : Finset (Fin G.size), ∃ I L : Layer G,
      I.exceptions = Z ∧
      (∀ x y, I.row x = I.row y ↔ x = y ∨
        x ∉ Z ∧ y ∉ Z ∧ κ x = κ y ∧ ∀ p, G.pred p x ↔ G.pred p y) ∧
      History G I K L ∧ Stable G K L.row ∧ Function.Surjective L.row ∧
      L.n ≤ limit d N (Z.card + 2^c*q) K ∧ L.exceptions.card ≤ limit d N (Z.card + 2^c*q) K

end Lax977378.ColouredRun
