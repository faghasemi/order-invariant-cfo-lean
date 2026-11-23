import Lax977378.OuterContexts

/-!
---
title: Elimination of order from invariant cluster sentences
type: theorem
---
The main statement quantifies over every class of finite coloured graphs
of degree at most $d$. The two intermediate statements are the ordered
comparison lemma and the finite-record order construction in pairwise form.
A record chooses an order using just the record and the individual graph.
The same record must work uniformly over all graphs passing its test.
-/
namespace Lax977378.Collapse

open Lax977378.Logic Lax977378.OuterContexts

axiom comparison {c : Nat} (K : Nat) (A B : Graph c)
    (a : LinearOrder (Fin A.size)) (b : LinearOrder (Fin B.size))
    (agree : spectrumAgrees A B a b K) (f : Formula c) (legal : Legal [] f)
    (bound : rank f ≤ K+1) : Holds A a f ↔ Holds B b f

structure Record {c : Nat} (d K : Nat) where
  test : Formula c
  plain : Plain [] test
  order : (G : Graph c) → LinearOrder (Fin G.size)
  agree : ∀ A B, A.Bounded d → B.Bounded d → Unordered A test → Unordered B test →
    spectrumAgrees A B (order A) (order B) K

axiom records (c d K : Nat) : ∃ tests : List (Record (c := c) d K),
  ∀ G, G.Bounded d → ∃ e ∈ tests, Unordered G e.test

axiom relativeCollapse {c d : Nat} (C : Graph c → Prop) (bounded : ∀ G, C G → G.Bounded d)
    (f : Formula c) (legal : Legal [] f) (inv : InvariantOn C f) :
    ∃ φ : Formula c, Plain [] φ ∧ ∀ G, C G → ∀ o, Holds G o f ↔ Unordered G φ

/-- The thesis convention requires order invariance on every finite coloured graph. -/
axiom collapse {c d : Nat} (C : Graph c → Prop) (bounded : ∀ G, C G → G.Bounded d)
    (f : Formula c) (legal : Legal [] f)
    (inv : ∀ G : Graph c, ∀ a b, Holds G a f ↔ Holds G b f) :
    ∃ φ : Formula c, Plain [] φ ∧ ∀ G, C G → ∀ o, Holds G o f ↔ Unordered G φ

end Lax977378.Collapse
