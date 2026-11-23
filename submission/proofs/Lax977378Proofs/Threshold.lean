import Lax977378.Threshold
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

namespace Lax977378Proofs
open Lax977378.Threshold

/--
---
conclusion: Lax977378.Threshold.uniformGap
---
Start with the threshold $b=1+h(0)$. If a count is below $b$, remove it
and apply induction to the remaining counts with the allowance $b$ added
to their rare total. This bounds the effect of putting the count back.
-/
theorem uniformGap (N : Nat) (h : Nat → Nat) (mono : Monotone h) :
    ∃ U, ∀ counts : List Nat, counts.length ≤ N →
      ∃ t, 0 < t ∧ t ≤ U ∧ h (rareTotal t counts) ≤ t := by
  induction N generalizing h with
  | zero =>
    refine ⟨h 0 + 1, ?_⟩
    intro counts hc
    have hempty : counts = [] := List.length_eq_zero_iff.mp (by omega)
    subst counts
    exact ⟨h 0 + 1, by omega, le_rfl, by simp [rareTotal]⟩
  | succ N ih =>
    let b := h 0 + 1
    obtain ⟨U, hu⟩ := ih (fun s => h (s + b)) (fun _ _ hij => mono (Nat.add_le_add_right hij b))
    refine ⟨max U b, ?_⟩
    intro counts hc
    by_cases small : ∃ x ∈ counts, x < b
    · obtain ⟨x, hx, hxb⟩ := small
      have hp := List.perm_cons_erase hx
      have hlen := hp.length_eq
      simp only [List.length_cons] at hlen
      obtain ⟨t, ht, htU, good⟩ := hu (counts.erase x) (by omega)
      refine ⟨t, ht, htU.trans (le_max_left ..), le_trans (mono ?_) good⟩
      have heq := (hp.filter (fun n => decide (n < t))).sum_eq
      unfold rareTotal
      rw [heq]
      by_cases hxt : x < t
      · simp [hxt]; omega
      · simp [hxt]
    · have hf : counts.filter (fun n => decide (n < b)) = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro n hn
        obtain ⟨hn, hnb⟩ := List.mem_filter.mp hn
        exact small ⟨n, hn, of_decide_eq_true hnb⟩
      refine ⟨b, Nat.zero_lt_succ _, le_max_right .., ?_⟩
      unfold rareTotal
      rw [hf]
      exact Nat.le_succ _

end Lax977378Proofs
