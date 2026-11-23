import Lax977378.Blocks
import Mathlib.Tactic

namespace Lax977378Proofs
open Lax977378.Blocks

private theorem block_lt {V I : Type} [LinearOrder V] [LinearOrder I]
    (P : Partition V I) {x y : V} (h : P.block x < P.block y) : x < y :=
  lt_of_not_ge (fun h' => (not_le_of_gt h) (P.monotone h'))

/--
---
conclusion: Lax977378.Blocks.interval
---
For a witness between the endpoints, monotonicity places its block
between the two endpoint blocks inclusively. Conversely use the first
vertex of an intervening block, or the appropriate endpoint of a boundary block.
-/
theorem interval {V I L : Type} [LinearOrder V] [LinearOrder I] (P : Partition V I)
    (label : I → L) (a b : V) (hab : P.block a < P.block b) (l : L) :
    (∃ x, a < x ∧ x < b ∧ label (P.block x) = l) ↔
    (∃ i, P.block a < i ∧ i < P.block b ∧ label i = l) ∨
    (a ≠ P.last (P.block a) ∧ label (P.block a) = l) ∨
    (b ≠ P.first (P.block b) ∧ label (P.block b) = l) := by
  constructor
  · rintro ⟨x, ha, hb, hl⟩
    rcases (P.monotone ha.le).eq_or_lt with h | h
    · exact Or.inr (Or.inl ⟨(ha.trans_le (h ▸ P.le_last x)).ne, h ▸ hl⟩)
    rcases (P.monotone hb.le).eq_or_lt with h' | h'
    · have le := P.first_le x
      rw [h'] at le
      exact Or.inr (Or.inr ⟨(le.trans_lt hb).ne', h' ▸ hl⟩)
    · exact Or.inl ⟨P.block x, h, h', hl⟩
  · rintro (⟨i, ha, hb, hl⟩ | ⟨hne, hl⟩ | ⟨hne, hl⟩)
    · exact ⟨P.first i, block_lt P (by rwa [P.first_mem]),
        block_lt P (by rwa [P.first_mem]), by rwa [P.first_mem]⟩
    · exact ⟨P.last (P.block a), lt_of_le_of_ne (P.le_last a) hne,
        block_lt P (by rwa [P.last_mem]), by rwa [P.last_mem]⟩
    · exact ⟨P.first (P.block b), block_lt P (by rwa [P.first_mem]),
        lt_of_le_of_ne (P.first_le b) hne.symm, by rwa [P.first_mem]⟩

/--
---
conclusion: Lax977378.Blocks.outerIntervals
---
For a prefix use the first vertex of the boundary block, and for a suffix
use its last vertex. A block strictly on the appropriate side contributes
all its vertices.
-/
theorem outerIntervals {V I L : Type} [LinearOrder V] [LinearOrder I] (P : Partition V I)
    (label : I → L) (a : V) (l : L) :
    ((∃ x, x < a ∧ label (P.block x) = l) ↔
      (∃ i, i < P.block a ∧ label i = l) ∨
      (a ≠ P.first (P.block a) ∧ label (P.block a) = l)) ∧
    ((∃ x, a < x ∧ label (P.block x) = l) ↔
      (∃ i, P.block a < i ∧ label i = l) ∨
      (a ≠ P.last (P.block a) ∧ label (P.block a) = l)) := by
  constructor <;> constructor
  · rintro ⟨x, hx, hl⟩
    rcases (P.monotone hx.le).eq_or_lt with h | h
    · have le := P.first_le x
      rw [h] at le
      exact Or.inr ⟨(le.trans_lt hx).ne', h ▸ hl⟩
    · exact Or.inl ⟨_, h, hl⟩
  · rintro (⟨i, hi, hl⟩ | ⟨hne, hl⟩)
    · exact ⟨P.first i, block_lt P (by rwa [P.first_mem]), by rwa [P.first_mem]⟩
    · exact ⟨_, lt_of_le_of_ne (P.first_le a) hne.symm, by rwa [P.first_mem]⟩
  · rintro ⟨x, hx, hl⟩
    rcases (P.monotone hx.le).eq_or_lt with h | h
    · have le := P.le_last x
      rw [← h] at le
      exact Or.inr ⟨(hx.trans_le le).ne, h ▸ hl⟩
    · exact Or.inl ⟨_, h, hl⟩
  · rintro (⟨i, hi, hl⟩ | ⟨hne, hl⟩)
    · exact ⟨P.first i, block_lt P (by rwa [P.first_mem]), by rwa [P.first_mem]⟩
    · exact ⟨_, lt_of_le_of_ne (P.le_last a) hne, by rwa [P.last_mem]⟩

end Lax977378Proofs
