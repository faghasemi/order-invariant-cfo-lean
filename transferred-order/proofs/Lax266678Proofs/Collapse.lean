import Lax266678.Collapse
import Lax977378.Collapse
import Mathlib.Tactic

namespace Lax266678Proofs
open Lax977378.Logic

private abbrev naturalOrder (n : Nat) : LinearOrder (Fin n) := inferInstance

/--
---
conclusion: Lax266678.Collapse.orderInvariantCFO_in_FO
assumptions:
  - Lax266678.Transfer.transferOrder
  - Lax977378.Collapse.comparison
  - Lax266678.Definability.definable
---
Choose context depth one less than the quantifier rank, using depth zero for
rank zero. Transfer the source order, compare the ordered graphs at that
depth, and use order invariance on each graph to obtain a property constant
on bounded-rank first-order classes.
-/
theorem orderInvariantCFO_in_FO {c d : Nat} (C : Graph c → Prop)
    (bounded : ∀ G, C G → G.Bounded d) (f : Formula c) (legal : Legal [] f)
    (inv : ∀ G : Graph c, ∀ a b, Holds G a f ↔ Holds G b f) :
    ∃ φ : Formula c, Plain [] φ ∧ ∀ G, C G → ∀ a, Holds G a f ↔ Unordered G φ := by
  let k := rank f - 1
  obtain ⟨q, tr⟩ := Lax266678.Transfer.transferOrder c d k
  apply Exists.elim (Lax266678.Definability.definable C (fun G => Unordered G f) q ?_)
  · rintro φ ⟨hp,h⟩
    exact ⟨φ,hp,fun G hG a => (inv G a (naturalOrder G.size)).trans (h G hG)⟩
  · intro A B hA hB eq
    obtain ⟨a, move⟩ := tr A (bounded A hA)
    obtain ⟨b, agree⟩ := move B (bounded B hB) eq
    exact (inv A (naturalOrder A.size) a).trans
      ((Lax977378.Collapse.comparison k A B a b agree f legal (by dsimp [k]; omega)).trans
        (inv B b (naturalOrder B.size)))

end Lax266678Proofs
