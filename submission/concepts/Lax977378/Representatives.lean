import Lax977378.Transport

/-!
---
title: Representatives of all child blocks on a passing graph
type: lemma
---
The exceptional vertices correspond through the named window. Outside it,
each coloured type occurs on both graphs and determines its source child
block. Choose one source representative per ordinary type. The target then
hits every source child block, including every named singleton, without
requiring a bijection of ordinary vertices.
-/
namespace Lax977378.Representatives

axiom representatives {A B T I : Type} (X : Set A) (Y : Set B)
    (exceptional : Y ≃ X) (shapeA : A → T) (shapeB : B → T) (block : A → I)
    (onto : Function.Surjective block)
    (availableA : ∀ y, y ∉ Y → ∃ x ∉ X, shapeA x = shapeB y)
    (availableB : ∀ x, x ∉ X → ∃ y ∉ Y, shapeB y = shapeA x)
    (constant : ∀ x ∉ X, ∀ u ∉ X, shapeA x = shapeA u → block x = block u) :
    ∃ rep : B → A, (∀ y : Y, rep y = (exceptional y).val) ∧
      (∀ y ∉ Y, rep y ∉ X ∧ shapeA (rep y) = shapeB y) ∧
      (∀ x : X, ∃! y, rep y = x.val) ∧ Function.Surjective (block ∘ rep)

end Lax977378.Representatives
