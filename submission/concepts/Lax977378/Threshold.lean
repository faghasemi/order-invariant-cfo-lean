import Mathlib.Data.List.Basic
import Mathlib.Order.Monotone.Basic

/-!
---
title: Uniform threshold for a finite list of type counts
type: lemma
---
For a fixed number of counts we can choose a uniformly bounded positive
threshold. The threshold dominates a prescribed nondecreasing function of
the total of the counts strictly below it, including when some counts vanish.
-/
namespace Lax977378.Threshold

def rareTotal (t : Nat) (counts : List Nat) : Nat :=
  ((counts.filter (fun n => decide (n < t))).sum)

axiom uniformGap (N : Nat) (h : Nat → Nat) (mono : Monotone h) :
    ∃ U, ∀ counts : List Nat, counts.length ≤ N →
      ∃ t, 0 < t ∧ t ≤ U ∧ h (rareTotal t counts) ≤ t

end Lax977378.Threshold
