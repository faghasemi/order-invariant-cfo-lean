import Lax977378.TableFacts
import Lax977378.LocalCover
import Lax977378.CoverReplay
import Lax977378.MarkedSets

/-!
---
title: An independent order on a graph with the same window and coloured types
type: lemma
---
Transport the exception names and endpoint roles through the finite window.
Elsewhere use the untagged coloured types realised on both graphs. These
data determine a target order with exactly the source spectrum.
-/
namespace Lax977378.TargetOrder
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests Lax977378.Planting
open Lax977378.SourceTables Lax977378.TagSafety

axiom targetOrder {c d K q p} (W A B : Graph c) (ha : A.Bounded d) (hb : B.Bounded d)
    (a : LinearOrder (Fin A.size)) (T : Nat → Table A a)
    (next : ∀ j < K, Follows j (T j) (T (j+1)))
    (κ : Fin A.size → Fin q) (kB : Fin B.size → Fin q)
    (base : ∀ x y, (T 0).part.block x = (T 0).part.block y ↔ x = y ∨
      x ∉ (T 0).exceptions ∧ y ∉ (T 0).exceptions ∧ κ x = κ y ∧ ∀ i, A.pred i x ↔ A.pred i y)
    (sep : ∀ x, Function.Injective (fun u : Ball A K x => (T 0).part.block u.val))
    (mark : Finset (Fin W.size)) (y : Fin W.size → Fin A.size) (z : Fin W.size → Fin B.size)
    (wy : Window W A (radius K+p) mark y) (wz : Window W B (radius K+p) mark z)
    (named : mark.image y = (T K).exceptions)
    (col : ∀ j, (∃ m ∈ mark, within W (radius K) m j) → κ (y j) = kB (z j))
    (seeds : List (Request c q))
    (typesA : ∀ x ∉ (T K).exceptions, ∃ s ∈ seeds, Realised s A (radius K) κ x)
    (typesB : ∀ w ∉ mark.image z, ∃ s ∈ seeds, Realised s B (radius K) kB w)
    (copiesA : ∀ s ∈ seeds, ∃ x ∉ (T K).exceptions, Realised s A (radius K) κ x)
    (copiesB : ∀ s ∈ seeds, ∃ w ∉ mark.image z, Realised s B (radius K) kB w) :
    ∃ b, spectrumAgrees A B a b K

end Lax977378.TargetOrder
