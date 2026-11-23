import Lax977378.Stage
import Lax977378.TagSafety

/-!
---
title: Constructing the bounded history of the source partitions
type: lemma
---
Starting with a stable partition separating every inspected ball, retain each
parent partition, its endpoints, and the rule defining its children. At each
stage the exceptional set is exactly the neighbourhood of the previous
exceptions and the new endpoints. A common bound for the number of rows and
exceptions depends only on the parameters and the initial bound.
-/
namespace Lax977378.SourceRun
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Blocks Lax977378.Stage Lax977378.TagSafety

structure Layer {c : Nat} (G : Graph c) where
  n : Nat
  row : Fin G.size → Fin n
  exceptions : Finset (Fin G.size)

def History {c} (G : Graph c) (initial : Layer G) : Nat → Layer G → Prop
  | 0, L => L = initial
  | j+1, L => ∃ H : Layer G, History G initial j H ∧
    ∃ f l : Fin H.n → Fin G.size,
      (∀ x, x ∈ L.exceptions ↔ ∃ z, (z ∈ H.exceptions ∨ (∃ t, f t = z) ∨ ∃ t, l t = z) ∧
        within G (radius (j+1)) z x) ∧
      (∀ (a : LinearOrder (Fin G.size)), Compatible a L.row →
        ∃ P : @Partition (Fin G.size) (Fin H.n) a inferInstance,
          P.block = H.row ∧ P.first = f ∧ P.last = l) ∧
      (∀ (a : LinearOrder (Fin G.size)), Compatible a L.row → ∀ x y,
        L.row x = L.row y ↔ H.row x = H.row y ∧
          (x = y ∨ x ∉ L.exceptions ∧ y ∉ L.exceptions ∧ same G G a a (j+1) x y))

def limit (d : Nat) (N : Nat → Nat) (b : Nat) : Nat → Nat
  | 0 => b
  | j+1 => (3*(d+1)^(radius (j+1)) + N j) * limit d N b j

axiom construct (c d K : Nat) : ∃ N : Nat → Nat, ∀ (G : Graph c), G.Bounded d →
    ∀ (initial : Layer G) (b : Nat), initial.n ≤ b → initial.exceptions.card ≤ b →
    Function.Surjective initial.row → Stable G 0 initial.row →
    (∀ x, Function.Injective (fun u : Ball G K x => initial.row u.val)) →
    ∃ L : Layer G, History G initial K L ∧ Stable G K L.row ∧
      Function.Surjective L.row ∧ L.n ≤ limit d N b K ∧ L.exceptions.card ≤ limit d N b K

end Lax977378.SourceRun
