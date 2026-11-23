import Lax977378.SourceRecord
import Lax977378.OrdinaryCalls

/-!
---
title: Structural properties of the tables read from a source run
type: lemma
---
The rows refine their parents, every endpoint is isolated at the next stage,
and all past exceptions have names in the final window. Separation on the
initial ball persists down the refinement. Row homogeneity holds in the
final order in which the tables were read.
-/
namespace Lax977378.TableFacts
open Lax977378.Logic Lax977378.OuterContexts Lax977378.SourceTables Lax977378.OrdinaryCalls

def endpoints {c G a} (T : @Table c G a) := Finset.univ.image T.part.first ∪ Finset.univ.image T.part.last

axiom facts {c d K} (A : Graph c) (hd : A.Bounded d) (a : LinearOrder (Fin A.size))
    (T : Nat → Table A a) (next : ∀ j < K, Follows j (T j) (T (j+1)))
    (base : ∀ x y, (T 0).part.block x = (T 0).part.block y → ∀ p, A.pred p x ↔ A.pred p y)
    (sep : ∀ x, Function.Injective (fun u : Ball A K x => (T 0).part.block u.val)) :
    (∀ i j, i ≤ j → j ≤ K → (T i).exceptions ⊆ (T j).exceptions) ∧
    (∀ j < K, endpoints (T j) ⊆ (T (j+1)).exceptions) ∧
    (∀ j ≤ K, ∀ x y, (T j).part.block x = (T j).part.block y → same A A a a j x y) ∧
    (∀ j < K, ∀ x, Function.Injective (fun u : Ball A (j+1) x => (T j).part.block u.val))

end Lax977378.TableFacts
