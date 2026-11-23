import Lax977378.Stage

/-!
---
title: Transport of a refinement to an independently ordered graph
type: lemma
---
A target vertex is assigned a source representative by the local calculation.
Every source child row must be hit. Endpoint children are singletons, and
the correspondence recognises the two chosen target endpoints. Ordering
the target by the representative's child row then enforces the recorded
endpoints, in every compatible order. Ball correspondences allow the previous
table to compute the new outer contexts across the two graphs.
-/
namespace Lax977378.Transport
open Lax977378.Logic Lax977378.Blocks Lax977378.OuterContexts Lax977378.Stage

axiom transport {c d n m i} (A B : Graph c) (ha : A.Bounded d) (hb : B.Bounded d)
    (a : LinearOrder (Fin A.size))
    (P : @Partition (Fin A.size) (Fin n) a inferInstance)
    (C : @Partition (Fin A.size) (Fin m) a inferInstance)
    (hom : ∀ x y, C.block x = C.block y → same A A a a (i+1) x y)
    (parent : ∀ x y, C.block x = C.block y → P.block x = P.block y)
    (singleF : ∀ x j, C.block x = C.block (P.first j) → x = P.first j)
    (singleL : ∀ x j, C.block x = C.block (P.last j) → x = P.last j)
    (rep : Fin B.size → Fin A.size) (hit : Function.Surjective (C.block ∘ rep))
    (f l : Fin n → Fin B.size) (rf : ∀ j, rep (f j) = P.first j)
    (rl : ∀ j, rep (l j) = P.last j)
    (uf : ∀ j z, rep z = P.first j → z = f j)
    (ul : ∀ j z, rep z = P.last j → z = l j)
    (lower : ∀ (b : LinearOrder (Fin B.size)), Compatible b (P.block ∘ rep) →
      ∀ x z, P.block x = P.block (rep z) → same A B a b i x z)
    (balls : ∀ z, ∃ h : Ball A (i+1) (rep z) ≃ Ball B (i+1) z,
      (∀ u, u.val = rep z ↔ (h u).val = z) ∧
      (∀ u v, A.edge u.val v.val ↔ B.edge (h u).val (h v).val) ∧
      Function.Injective (fun u : Ball A (i+1) (rep z) => P.block u.val) ∧
      (∀ u, P.block u.val = P.block (rep (h u).val)) ∧
      (∀ u, u.val = P.first (P.block u.val) ↔ (h u).val = f (P.block (rep (h u).val))) ∧
      (∀ u, u.val = P.last (P.block u.val) ↔ (h u).val = l (P.block (rep (h u).val)))) :
    ∀ (b : LinearOrder (Fin B.size)), Compatible b (C.block ∘ rep) →
      (∃ Q : @Partition (Fin B.size) (Fin n) b inferInstance,
        Q.block = P.block ∘ rep ∧ Q.first = f ∧ Q.last = l) ∧
      (∀ x z, C.block x = C.block (rep z) → same A B a b (i+1) x z) ∧
      spectrumAgrees A B a b (i+1)

end Lax977378.Transport
