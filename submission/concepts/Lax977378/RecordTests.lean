import Lax977378.OuterContexts

/-!
---
title: Unordered neighbourhood and exceptional-window tests
type: lemma
---
A diagram enumerates a finite induced graph with its original unary predicates.
The window condition says exactly which vertices are within a fixed radius
of one of the marked vertices. A pointed type is a one-centre window with
a distinguished root. A finite record can prescribe truncated type counts
and require its distinguished rare vertices to be precisely those outside
its list of frequent types, using the very same witnesses as its window.
-/
namespace Lax977378.RecordTests
open Lax977378.Logic Lax977378.OuterContexts

def Diagram {c : Nat} (W G : Graph c) (y : Fin W.size → Fin G.size) : Prop :=
  Function.Injective y ∧ (∀ i j, W.edge i j ↔ G.edge (y i) (y j)) ∧
    ∀ p i, W.pred p i ↔ G.pred p (y i)

def Window {c : Nat} (W G : Graph c) (r : Nat) (marked : Finset (Fin W.size))
    (y : Fin W.size → Fin G.size) : Prop :=
  Diagram W G y ∧ ∀ x, (∃ i, y i = x) ↔ ∃ i ∈ marked, within G r (y i) x

structure Pointed (c : Nat) where
  pattern : Graph c
  center : Fin pattern.size

def Occurs {c : Nat} (t : Pointed c) (r : Nat) (G : Graph c) (x : Fin G.size) : Prop :=
  ∃ y, Window t.pattern G r {t.center} y ∧ y t.center = x

def AtLeast {c : Nat} (t : Pointed c) (r k : Nat) (G : Graph c) : Prop :=
  ∃ xs : Fin k → Fin G.size, Function.Injective xs ∧ ∀ i, Occurs t r G (xs i)

structure TestData (c : Nat) where
  radius : Nat
  windowRadius : Nat
  windowGraph : Graph c
  marked : Finset (Fin windowGraph.size)
  rare : Finset (Fin windowGraph.size)
  cap : Nat
  counts : List (Pointed c × Nat)
  frequent : List (Pointed c)

def Passes {c : Nat} (D : TestData c) (G : Graph c) : Prop :=
  (∀ tv ∈ D.counts, tv.2 ≤ D.cap ∧ AtLeast tv.1 D.radius tv.2 G ∧
    (tv.2 < D.cap → ¬ AtLeast tv.1 D.radius (tv.2+1) G)) ∧
  ∃ y, Window D.windowGraph G D.windowRadius D.marked y ∧
    ∀ x, (∃ i ∈ D.rare, y i = x) ↔ ¬ ∃ t ∈ D.frequent, Occurs t D.radius G x

axiom recordTest {c : Nat} (D : TestData c) :
  ∃ f : Formula c, Plain [] f ∧ ∀ G, Unordered G f ↔ Passes D G

end Lax977378.RecordTests
