import Lax977378.RecordTests

/-!
---
title: Exact distances in the record's exceptional window
type: lemma
---
A record names the entire radius-$(\rho+p)$ neighbourhood of its exceptional
set. Starting within distance $\rho$ of that set, every ambient path of length
at most $p$ can be read in the named induced graph. The conclusion includes
both the vertices reached and their distances up to the specified radius.
-/
namespace Lax977378.Window
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests

axiom exactBall {c ρ p : Nat} {W G : Graph c} {mark : Finset (Fin W.size)}
    {y : Fin W.size → Fin G.size} (hw : RecordTests.Window W G (ρ+p) mark y)
    {u : Fin W.size} (near : ∃ m ∈ mark, within W ρ m u)
    (r : Nat) (hr : r ≤ p) (z : Fin G.size) :
    within G r (y u) z ↔ ∃ v, within W r u v ∧ y v = z

end Lax977378.Window
