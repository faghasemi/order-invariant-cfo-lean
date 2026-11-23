import Lax977378.Logic

/-!
---
title: Agreement of outer contexts in two ordered graphs
type: definition
---
A pointed ball is taken in the graph metric. Agreement at rank $i+1$
requires a rooted ordered ball isomorphism, matching rank-$i$ labels on
ball vertices and matching sets of lower contexts in the internal gaps
and the two outer gaps. Strict comparisons against every ball vertex
specify the gap. Both directions of witness matching are required.
-/
namespace Lax977378.OuterContexts

open Lax977378.Logic

def within {c : Nat} (G : Graph c) : Nat → Fin G.size → Fin G.size → Prop
  | 0, x, y => x = y
  | i+1, x, y => within G i x y ∨ ∃ z, within G i x z ∧ G.edge z y

abbrev Ball {c : Nat} (G : Graph c) (r : Nat) (x : Fin G.size) :=
  {y : Fin G.size // within G r x y}

def same {c : Nat} (A B : Graph c) (a : LinearOrder (Fin A.size))
    (b : LinearOrder (Fin B.size)) : Nat → Fin A.size → Fin B.size → Prop
  | 0, x, y => ∀ p, A.pred p x ↔ B.pred p y
  | i+1, x, y =>
    ∃ h : Ball A (i+1) x ≃ Ball B (i+1) y,
      (∀ u, u.val = x ↔ (h u).val = y) ∧
      (∀ u v, A.edge u.val v.val ↔ B.edge (h u).val (h v).val) ∧
      (∀ u v, a.lt u.val v.val ↔ b.lt (h u).val (h v).val) ∧
      (∀ u, same A B a b i u.val (h u).val) ∧
      let matched := fun (z : Fin A.size) (w : Fin B.size) =>
        same A B a b i z w ∧ ∀ u,
          (a.lt z u.val ↔ b.lt w (h u).val) ∧ (a.lt u.val z ↔ b.lt (h u).val w)
      (∀ z, ∃ w, matched z w) ∧ (∀ w, ∃ z, matched z w)

def spectrumAgrees {c : Nat} (A B : Graph c) (a : LinearOrder (Fin A.size))
    (b : LinearOrder (Fin B.size)) (i : Nat) : Prop :=
  (∀ x, ∃ y, same A B a b i x y) ∧ (∀ y, ∃ x, same A B a b i x y)

end Lax977378.OuterContexts
