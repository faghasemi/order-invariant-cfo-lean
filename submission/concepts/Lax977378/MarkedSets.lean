import Lax977378.OrdinaryCalls
import Lax977378.Window

/-!
---
title: Transporting the exceptional stages through a shared window
type: lemma
---
Transport a source subset using the common names of its vertices. When the
exceptional sets and endpoints lie in the marked set, every target path used
in defining the next exceptional set lifts into the window. Thus the target
inherits the coverage needed for calculations without tags.
-/
namespace Lax977378.MarkedSets
open Lax977378.Logic Lax977378.RecordTests Lax977378.OrdinaryCalls Lax977378.TagSafety

noncomputable def moved {c} {W A B : Graph c} (y : Fin W.size → Fin A.size)
    (z : Fin W.size → Fin B.size) (S : Finset (Fin A.size)) : Finset (Fin B.size) := by
  classical exact (Finset.univ.filter (fun j => y j ∈ S)).image z

axiom moveStages {c K R} (W A B : Graph c) (mark : Finset (Fin W.size))
    (y : Fin W.size → Fin A.size) (z : Fin W.size → Fin B.size)
    (wy : Window W A R mark y) (wz : Window W B R mark z)
    (X E : Nat → Finset (Fin A.size)) (covers : Covers A K X E)
    (named : ∀ j < K, X j ∪ E (j+1) ⊆ mark.image y)
    (size : ∀ j < K, radius (j+1) ≤ R) :
    Covers B K (fun j => moved y z (X j)) (fun j => moved y z (E j))

end Lax977378.MarkedSets
