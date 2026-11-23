import Lax977378.Transport
import Lax977378.CallAgreement

/-!
---
title: Replaying every level from matching recursive local data
type: lemma
---
Source partitions refer to a single final source order. Each target vertex
has a full-rank representative. Lower-rank calls at a target ball vertex need
not use its chosen representative; comparing the two source calls recovers
the same lower block. Thus one representative map works at all levels.
-/
namespace Lax977378.RunReplay
open Lax977378.Logic Lax977378.Blocks Lax977378.OuterContexts Lax977378.Stage
open Lax977378.CallAgreement

axiom runReplay {c d K} (A B : Graph c) (ha : A.Bounded d) (hb : B.Bounded d)
    (a : LinearOrder (Fin A.size)) (n : Nat → Nat)
    (P : (j : Nat) → @Partition (Fin A.size) (Fin (n j)) a inferInstance)
    (ra ea : Nat → Fin A.size → Nat) (rb eb : Nat → Fin B.size → Nat)
    (rep : Fin B.size → Fin A.size)
    (matched : ∀ z, agrees A B ra ea rb eb K (rep z) z)
    (hit : ∀ j ≤ K, Function.Surjective ((P j).block ∘ rep))
    (base : ∀ x z, (P 0).block x = (P 0).block (rep z) → ∀ p, A.pred p x ↔ B.pred p z)
    (names : ∀ j ≤ K, ∀ x y, agrees A A ra ea ra ea j x y → (P j).block x = (P j).block y)
    (hom : ∀ j ≤ K, ∀ x y, (P j).block x = (P j).block y → same A A a a j x y)
    (parent : ∀ j < K, ∀ x y, (P (j+1)).block x = (P (j+1)).block y → (P j).block x = (P j).block y)
    (ends : ∀ j < K, ∀ t, ∀ e ∈ [(P j).first t,(P j).last t],
      (∀ x, (P (j+1)).block x = (P (j+1)).block e → x = e) ∧ ∃! z, rep z = e)
    (separated : ∀ j < K, ∀ x, Function.Injective (fun v : Ball A (j+1) x => (P j).block v.val))
    (roles : ∀ j < K, ∀ x z, ea (j+1) x = eb (j+1) z →
      (x = (P j).first ((P j).block x) ↔ rep z = (P j).first ((P j).block (rep z))) ∧
      (x = (P j).last ((P j).block x) ↔ rep z = (P j).last ((P j).block (rep z)))) :
    ∀ j ≤ K, ∀ (b : LinearOrder (Fin B.size)), Compatible b ((P j).block ∘ rep) →
      (∀ x z, (P j).block x = (P j).block (rep z) → same A B a b j x z) ∧
      spectrumAgrees A B a b j

end Lax977378.RunReplay
