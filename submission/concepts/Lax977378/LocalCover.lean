import Lax977378.OrdinaryCalls
import Lax977378.CommonPalette

/-!
---
title: Coverage of full local calls by the named window and the coloured requests
type: lemma
---
Use the common inner window for each final exceptional vertex. Every other
vertex has a frequent coloured request which survives outside the other
graph's final exceptions. The untagged calculation there agrees at all ranks.
This yields coverage in both directions without pairing ordinary vertices
bijectively.
-/
namespace Lax977378.LocalCover
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests Lax977378.Planting
open Lax977378.TagSafety Lax977378.OrdinaryCalls Lax977378.LocalCalls

axiom coverCalls {c q K slack} (W A B : Graph c) (mark : Finset (Fin W.size))
    (y : Fin W.size → Fin A.size) (z : Fin W.size → Fin B.size)
    (wy : Window W A (radius K+slack) mark y) (wz : Window W B (radius K+slack) mark z)
    (X E : Nat → Finset (Fin A.size)) (Y F : Nat → Finset (Fin B.size))
    (covA : Covers A K X E) (covB : Covers B K Y F)
    (markA : mark.image y = X K) (markB : mark.image z = Y K)
    (a : Fin A.size → Fin q) (b : Fin B.size → Fin q)
    (root ends : Nat → Fin A.size → Fin B.size → Prop)
    (inside : ∀ i ≤ K, ∀ u, (∃ m ∈ mark, within W (radius K) m u) →
      root i (y u) (z u) ∧ ends i (y u) (z u))
    (ordinary : ∀ i ≤ K, ∀ x ∉ X i, ∀ w ∉ Y i,
      a x = b w ∧ (∀ p, A.pred p x ↔ B.pred p w) → root i x w)
    (interior : ∀ i < K, ∀ x ∉ E (i+1), ∀ w ∉ F (i+1), ends (i+1) x w)
    (seeds : List (Request c q))
    (typesA : ∀ x ∉ X K, ∃ s ∈ seeds, Realised s A (radius K) a x)
    (typesB : ∀ w ∉ Y K, ∃ s ∈ seeds, Realised s B (radius K) b w)
    (copiesA : ∀ s ∈ seeds, ∃ x ∉ X K, Realised s A (radius K) a x)
    (copiesB : ∀ s ∈ seeds, ∃ w ∉ Y K, Realised s B (radius K) b w) :
    (∀ x, ∃ w, Calls A B root ends K x w) ∧ (∀ w, ∃ x, Calls A B root ends K x w)

end Lax977378.LocalCover
