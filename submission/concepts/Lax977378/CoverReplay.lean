import Lax977378.LocalNames

/-!
---
title: Independent order from coverage of full-rank local calls
type: lemma
---
Choose one source representative per target vertex from the full-rank local
comparisons. Reverse coverage makes every source row appear in the target,
even though the representative chosen for a target need not be the source
vertex that witnessed reverse coverage. Named endpoints have unique fibres.
-/
namespace Lax977378.CoverReplay
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Blocks Lax977378.CallAgreement

axiom orderFromCover {c d K} (A B : Graph c) (ha : A.Bounded d) (hb : B.Bounded d)
    (a : LinearOrder (Fin A.size)) (n : Nat → Nat)
    (P : (j : Nat) → @Partition (Fin A.size) (Fin (n j)) a inferInstance)
    (ra ea : Nat → Fin A.size → Nat) (rb eb : Nat → Fin B.size → Nat)
    (fwd : ∀ x, ∃ z, agrees A B ra ea rb eb K x z)
    (back : ∀ z, ∃ x, agrees A B ra ea rb eb K x z)
    (pred : ∀ x z, ra 0 x = rb 0 z → ∀ p, A.pred p x ↔ B.pred p z)
    (base : ∀ x y, ra 0 x = ra 0 y → (P 0).block x = (P 0).block y)
    (child : ∀ j < K, ∀ x y, ra (j+1) x = ra (j+1) y → (P j).block x = (P j).block y →
      same A A a a (j+1) x y → (P (j+1)).block x = (P (j+1)).block y)
    (hom : ∀ j ≤ K, ∀ x y, (P j).block x = (P j).block y → same A A a a j x y)
    (parent : ∀ j < K, ∀ x y, (P (j+1)).block x = (P (j+1)).block y → (P j).block x = (P j).block y)
    (ends : ∀ j < K, ∀ t, ∀ e ∈ [(P j).first t,(P j).last t],
      (∀ x, (P (j+1)).block x = (P (j+1)).block e → x = e) ∧
      (∀ x, ra K x = ra K e → x = e) ∧ ∀ z w, rb K z = ra K e → rb K w = ra K e → z = w)
    (separated : ∀ j < K, ∀ x, Function.Injective (fun v : Ball A (j+1) x => (P j).block v.val))
    (roles : ∀ j < K, ∀ x y, ea (j+1) x = ea (j+1) y →
      (x = (P j).first ((P j).block x) ↔ y = (P j).first ((P j).block y)) ∧
      (x = (P j).last ((P j).block x) ↔ y = (P j).last ((P j).block y))) :
    ∃ b, spectrumAgrees A B a b K

end Lax977378.CoverReplay
