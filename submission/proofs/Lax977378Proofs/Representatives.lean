import Lax977378.Representatives
import Mathlib.Tactic

namespace Lax977378Proofs.Representatives

/--
---
conclusion: Lax977378.Representatives.representatives
---
Use the fixed window map on the exceptional set. Elsewhere choose any
ordinary source witness of the coloured type. Constancy on an ordinary type
turns coverage of types into coverage of child blocks.
-/
theorem representatives {A B T I : Type} (X : Set A) (Y : Set B)
    (exceptional : Y ≃ X) (shapeA : A → T) (shapeB : B → T) (block : A → I)
    (onto : Function.Surjective block)
    (availableA : ∀ y, y ∉ Y → ∃ x ∉ X, shapeA x = shapeB y)
    (availableB : ∀ x, x ∉ X → ∃ y ∉ Y, shapeB y = shapeA x)
    (constant : ∀ x ∉ X, ∀ u ∉ X, shapeA x = shapeA u → block x = block u) :
    ∃ rep : B → A, (∀ y : Y, rep y = (exceptional y).val) ∧
      (∀ y ∉ Y, rep y ∉ X ∧ shapeA (rep y) = shapeB y) ∧
      (∀ x : X, ∃! y, rep y = x.val) ∧ Function.Surjective (block ∘ rep) := by
  classical
  let rep (y : B) := if hy : y ∈ Y then (exceptional ⟨y,hy⟩).val
    else (availableA y hy).choose
  have fixed (y : Y) : rep y = (exceptional y).val := by simp [rep,y.property]
  have ord (y : B) (hy : y ∉ Y) : rep y ∉ X ∧ shapeA (rep y) = shapeB y := by
    simpa [rep,hy] using (availableA y hy).choose_spec
  refine ⟨rep,fixed,ord,?_,?_⟩
  · intro x
    refine ⟨(exceptional.symm x).val,by simpa using fixed (exceptional.symm x),?_⟩
    intro y he
    by_cases hy : y ∈ Y
    · have eq : exceptional ⟨y,hy⟩ = x := Subtype.ext ((fixed ⟨y,hy⟩).symm.trans he)
      exact congrArg Subtype.val (exceptional.eq_symm_apply.mpr eq)
    · exact False.elim ((ord y hy).1 (he ▸ x.property))
  · intro j
    obtain ⟨x,rfl⟩ := onto j
    by_cases hx : x ∈ X
    · let y := exceptional.symm ⟨x,hx⟩
      exact ⟨y,congrArg block (by simpa [y] using fixed y)⟩
    · obtain ⟨y,hy,h⟩ := availableB x hx
      exact ⟨y,constant _ (ord y hy).1 x hx ((ord y hy).2.trans h)⟩

end Lax977378Proofs.Representatives
