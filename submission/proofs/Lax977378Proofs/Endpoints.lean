import Lax977378.Endpoints
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

namespace Lax977378Proofs.Endpoints
open Lax977378.Blocks

/--
---
conclusion: Lax977378.Endpoints.twoCentres
---
At most the cardinality of the exceptional set is lost on taking the
difference. Choose two distinct surviving centres in the requested block.
-/
theorem twoCentres {V I : Type} [DecidableEq V] (block : V → I) (i : I)
    (Γ S : Finset V) (enough : Γ.card + 2 ≤ S.card)
    (ordinary : ∀ x ∈ S, x ∉ Γ → block x = i) :
    ∃ u ∈ S, ∃ v ∈ S, u ∉ Γ ∧ v ∉ Γ ∧ u ≠ v ∧ block u = i ∧ block v = i := by
  have h := Finset.le_card_sdiff Γ S
  obtain ⟨u,hu,v,hv,ne⟩ := Finset.one_lt_card.mp (show 1 < (S \ Γ).card by omega)
  obtain ⟨hus,hug⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨hvs,hvg⟩ := Finset.mem_sdiff.mp hv
  exact ⟨u,hus,v,hvs,hug,hvg,ne,ordinary u hus hug,ordinary v hvs hvg⟩

/--
---
conclusion: Lax977378.Endpoints.admissible
---
Order first by block, then by endpoint position, and use the original vertex
number to break ties among the middle vertices. A coincident first and last
can occur precisely in a singleton block under the stated hypothesis.
-/
theorem admissible {n m : Nat} (block : Fin n → Fin m) (first last : Fin m → Fin n)
    (hf : ∀ i, block (first i) = i) (hl : ∀ i, block (last i) = i)
    (singleton : ∀ i, first i = last i → ∀ x, block x = i → x = first i) :
    ∃ a : LinearOrder (Fin n), ∃ P : @Partition (Fin n) (Fin m) a inferInstance,
      P.block = block ∧ P.first = first ∧ P.last = last := by
  classical
  let role (x : Fin n) : Nat := if x = first (block x) then 0 else if x = last (block x) then 2 else 1
  let key (x : Fin n) := toLex (block x, toLex (role x,x))
  have inj : Function.Injective key := fun _ _ h => congrArg (fun t => (ofLex (ofLex t).2).2) h
  let a := LinearOrder.lift' key inj
  have before (x) : a.le (first (block x)) x := by
    change key (first (block x)) ≤ key x
    apply Prod.Lex.toLex_le_toLex.mpr
    refine Or.inr ⟨hf _,?_⟩
    by_cases he : x = first (block x)
    · rw [← he]
    · apply Prod.Lex.toLex_le_toLex.mpr
      left
      simp [role,hf,he]
      split <;> decide
  have after (x) : a.le x (last (block x)) := by
    change key x ≤ key (last (block x))
    apply Prod.Lex.toLex_le_toLex.mpr
    refine Or.inr ⟨(hl _).symm,?_⟩
    by_cases he : x = last (block x)
    · rw [← he]
    · have dist : last (block x) ≠ first (block x) := by
        intro h
        exact he ((singleton _ h.symm x rfl).trans h.symm)
      apply Prod.Lex.toLex_le_toLex.mpr
      left
      simp [role,hl,dist,he]
      split <;> decide
  have mono : ∀ x y, a.le x y → block x ≤ block y := by
    intro x y h
    rcases Prod.Lex.toLex_le_toLex.mp (show key x ≤ key y from h) with h | ⟨h,_⟩
    · exact le_of_lt h
    · exact le_of_eq h
  exact ⟨a,⟨block,fun {x y} => mono x y,first,last,hf,hl,before,after⟩,rfl,rfl,rfl⟩

end Lax977378Proofs.Endpoints
