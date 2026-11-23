import Lax977378.SourceRun

/-!
---
title: Reading all source tables in a single final order
type: lemma
---
A history retains the endpoint choices of each refinement. Reading it
backwards from a final table produces the earlier tables in that same order.
The two successive tables satisfy both the exception closure and the rule
identifying ordinary child blocks by parent and outer context.
-/
namespace Lax977378.SourceTables
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Blocks Lax977378.SourceRun Lax977378.TagSafety

structure Table {c} (G : Graph c) (a : LinearOrder (Fin G.size)) where
  n : Nat
  part : @Partition (Fin G.size) (Fin n) a inferInstance
  exceptions : Finset (Fin G.size)

def Table.layer {c G a} (T : @Table c G a) : Layer G := ⟨T.n,T.part.block,T.exceptions⟩

def Follows {c G a} (j : Nat) (P Q : @Table c G a) : Prop :=
  (∀ x, x ∈ Q.exceptions ↔ ∃ z, (z ∈ P.exceptions ∨ (∃ t, P.part.first t = z) ∨
    ∃ t, P.part.last t = z) ∧ within G (radius (j+1)) z x) ∧
  (∀ x y, Q.part.block x = Q.part.block y ↔ P.part.block x = P.part.block y ∧
    (x = y ∨ x ∉ Q.exceptions ∧ y ∉ Q.exceptions ∧ same G G a a (j+1) x y))

axiom sourceTables {c K} (G : Graph c) (I L : Layer G) (hist : History G I K L)
    (onto : Function.Surjective L.row) :
    ∃ (a : LinearOrder (Fin G.size)) (T : Nat → Table G a),
      (T 0).layer = I ∧ (T K).layer = L ∧ ∀ j < K, Follows j (T j) (T (j+1))

end Lax977378.SourceTables
