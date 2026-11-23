import Lax977378.Endpoints
import Lax977378.ContextLabels
import Lax977378.Refinement

/-!
---
title: Constructing a refinement and proving invariance under internal orders
type: lemma
---
For one graph, take legal endpoints in every current block. Split each parent
into the first singleton, the other exceptional singletons, ordinary groups
by outer context, and the last singleton. Every order compatible with the
result has the prescribed endpoints in its parent blocks. Vertices in the
same new block agree at the next rank in any two such orders.
-/
namespace Lax977378.Stage
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Blocks

def Compatible {v n} (a : LinearOrder (Fin v)) (block : Fin v → Fin n) : Prop :=
  ∀ x y, a.le x y → block x ≤ block y

def Stable {c n} (G : Graph c) (i : Nat) (block : Fin G.size → Fin n) : Prop :=
  ∀ a b, Compatible a block → Compatible b block →
    ∀ x y, block x = block y → same G G a b i x y

axiom refineBlocks (c d i : Nat) : ∃ N : Nat, ∀ {n : Nat} (G : Graph c), G.Bounded d →
    ∀ (block : Fin G.size → Fin n) (first last : Fin n → Fin G.size),
    (∀ j, block (first j) = j) → (∀ j, block (last j) = j) →
    (∀ j, first j = last j → ∀ x, block x = j → x = first j) →
    ∀ (Γ : Finset (Fin G.size)), (∀ j, first j ∈ Γ ∧ last j ∈ Γ) →
    Stable G i block →
    (∀ x, Function.Injective (fun u : Ball G (i+1) x => block u.val)) →
    ∃ m : Nat, ∃ next : Fin G.size → Fin m, Function.Surjective next ∧
      m ≤ Γ.card + n * N ∧
      Stable G (i+1) next ∧
      (∀ (a : LinearOrder (Fin G.size)), Compatible a next →
        ∃ P : @Partition (Fin G.size) (Fin n) a inferInstance,
          P.block = block ∧ P.first = first ∧ P.last = last) ∧
      (∀ (a : LinearOrder (Fin G.size)), Compatible a next → ∀ x y,
        next x = next y ↔ block x = block y ∧
          (x = y ∨ x ∉ Γ ∧ y ∉ Γ ∧ same G G a a (i+1) x y))

end Lax977378.Stage
