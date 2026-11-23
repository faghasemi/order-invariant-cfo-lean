import Lax977378.RunReplay

/-!
---
title: Local recovery of source block names at all ranks
type: lemma
---
At an ordinary vertex the parent and new outer context determine the
child block. Exceptional vertices have distinct root tags. Endpoint tags
give the two endpoint roles used by the previous table.
-/
namespace Lax977378.LocalNames
open Lax977378.Logic Lax977378.Blocks Lax977378.OuterContexts Lax977378.CallAgreement

axiom names {c K} (A : Graph c) (a : LinearOrder (Fin A.size)) (n : Nat → Nat)
    (P : (j : Nat) → @Partition (Fin A.size) (Fin (n j)) a inferInstance)
    (ra ea : Nat → Fin A.size → Nat)
    (base : ∀ x y, ra 0 x = ra 0 y → (P 0).block x = (P 0).block y)
    (child : ∀ j < K, ∀ x y, ra (j+1) x = ra (j+1) y →
      (P j).block x = (P j).block y → same A A a a (j+1) x y →
      (P (j+1)).block x = (P (j+1)).block y)
    (hom : ∀ j < K, ∀ x y, (P j).block x = (P j).block y → same A A a a j x y)
    (separated : ∀ j < K, ∀ x, Function.Injective (fun v : Ball A (j+1) x => (P j).block v.val))
    (roles : ∀ j < K, ∀ x y, ea (j+1) x = ea (j+1) y →
      (x = (P j).first ((P j).block x) ↔ y = (P j).first ((P j).block y)) ∧
      (x = (P j).last ((P j).block x) ↔ y = (P j).last ((P j).block y))) :
    ∀ j ≤ K, ∀ x y, agrees A A ra ea ra ea j x y → (P j).block x = (P j).block y

end Lax977378.LocalNames
