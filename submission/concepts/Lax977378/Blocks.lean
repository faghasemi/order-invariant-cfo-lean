import Mathlib.Order.Monotone.Basic

/-!
---
title: Context labels in the intervals of an ordered partition
type: lemma
---
The map from vertices to block indices is monotone. Each nonempty block has
a first and a last vertex. A block label contributes once whenever any vertex
of that block meets the gap. The internal interval and both exterior intervals
are stated pointwise, so identical labels on different blocks are allowed.
-/
namespace Lax977378.Blocks

structure Partition (V I : Type) [LinearOrder V] [LinearOrder I] where
  block : V → I
  monotone : Monotone block
  first : I → V
  last : I → V
  first_mem : ∀ i, block (first i) = i
  last_mem : ∀ i, block (last i) = i
  first_le : ∀ v, first (block v) ≤ v
  le_last : ∀ v, v ≤ last (block v)

axiom interval {V I L : Type} [LinearOrder V] [LinearOrder I] (P : Partition V I)
    (label : I → L) (a b : V) (hab : P.block a < P.block b) (l : L) :
    (∃ x, a < x ∧ x < b ∧ label (P.block x) = l) ↔
    (∃ i, P.block a < i ∧ i < P.block b ∧ label i = l) ∨
    (a ≠ P.last (P.block a) ∧ label (P.block a) = l) ∨
    (b ≠ P.first (P.block b) ∧ label (P.block b) = l)

axiom outerIntervals {V I L : Type} [LinearOrder V] [LinearOrder I] (P : Partition V I)
    (label : I → L) (a : V) (l : L) :
    ((∃ x, x < a ∧ label (P.block x) = l) ↔
      (∃ i, i < P.block a ∧ label i = l) ∨
      (a ≠ P.first (P.block a) ∧ label (P.block a) = l)) ∧
    ((∃ x, a < x ∧ label (P.block x) = l) ↔
      (∃ i, P.block a < i ∧ label i = l) ∨
      (a ≠ P.last (P.block a) ∧ label (P.block a) = l))

end Lax977378.Blocks
