import Lax977378.Blocks
import Lax977378.OuterContexts

/-!
---
title: One level of outer-context evaluation using the previous block table
type: lemma
---
Suppose two ordered partitions have the same ordered block names and that
vertices in matching blocks agree at the preceding rank. An isomorphism of
rooted balls preserving edges, block names and the first and last roles then
preserves the next outer context. Distinct ball vertices must occupy distinct
blocks. The graphs and the cardinalities of their blocks may differ.
-/
namespace Lax977378.Refinement
open Lax977378.Logic Lax977378.Blocks Lax977378.OuterContexts

axiom levelStep {c n i : Nat} (A B : Graph c)
    (a : LinearOrder (Fin A.size)) (b : LinearOrder (Fin B.size))
    (P : @Partition (Fin A.size) (Fin n) a inferInstance)
    (Q : @Partition (Fin B.size) (Fin n) b inferInstance)
    (lower : ∀ x y, P.block x = Q.block y → same A B a b i x y)
    (x : Fin A.size) (y : Fin B.size) (h : Ball A (i+1) x ≃ Ball B (i+1) y)
    (center : ∀ u, u.val = x ↔ (h u).val = y)
    (edges : ∀ u v, A.edge u.val v.val ↔ B.edge (h u).val (h v).val)
    (unique : Function.Injective (fun u : Ball A (i+1) x => P.block u.val))
    (blocks : ∀ u, P.block u.val = Q.block (h u).val)
    (first : ∀ u, u.val = P.first (P.block u.val) ↔ (h u).val = Q.first (Q.block (h u).val))
    (last : ∀ u, u.val = P.last (P.block u.val) ↔ (h u).val = Q.last (Q.block (h u).val)) :
    same A B a b (i+1) x y

end Lax977378.Refinement
