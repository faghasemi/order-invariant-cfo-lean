import Mathlib.Data.Fintype.Card
import Mathlib.Order.Basic

/-!
---
title: Finite coloured graphs and the cluster fragment
type: definition
---
Vertices are numbered solely to present a finite domain. Formulas have no access
to vertex numbers. Each unary predicate is interpreted independently. The
auxiliary order is an arbitrary linear order on the domain.

A variable is a word of child indices together with a continuation index.
The constructors of Legal express precisely the variable restrictions in the
graph vocabulary of the thesis. Greater-than is expressed by swapping the
arguments of less-than. Disjunction, negation and existential quantification
give the other Boolean connectives and universal quantification.
-/
namespace Lax977378.Logic

structure Graph (c : Nat) where
  size : Nat
  edge : Fin size → Fin size → Prop
  symm : ∀ x y, edge x y → edge y x
  loopless : ∀ x, ¬ edge x x
  pred : Fin c → Fin size → Prop

def Graph.Bounded {c : Nat} (G : Graph c) (d : Nat) : Prop :=
  ∀ x, ∃ neighbours : List (Fin G.size), neighbours.Nodup ∧
    neighbours.length ≤ d ∧ ∀ y, y ∈ neighbours ↔ G.edge x y

abbrev Var := List Nat × Nat

inductive Formula (c : Nat)
  | pred (p : Fin c) (x : Var)
  | edge (x y : Var)
  | eq (x y : Var)
  | lt (x y : Var)
  | neg (f : Formula c)
  | disj (f g : Formula c)
  | ex (x : Var) (f : Formula c)

def conj {c : Nat} (f g : Formula c) : Formula c :=
  .neg (.disj (.neg f) (.neg g))

def root : Var := ([], 0)

def child (w : List Nat) (a : Nat) : Var := (w ++ [a], 0)

def comparable (x y : Var) : Prop :=
  x.1 = y.1 ∨ (∃ a, x = child y.1 a) ∨ (∃ a, y = child x.1 a)

inductive Legal {c : Nat} : List Var → Formula c → Prop
  | pred {S x p} : x ∈ S → Legal S (.pred p x)
  | edge {S x y} : x ∈ S → y ∈ S → x.1 = y.1 → Legal S (.edge x y)
  | eq {S x y} : x ∈ S → y ∈ S → comparable x y → Legal S (.eq x y)
  | lt {S x y} : x ∈ S → y ∈ S → comparable x y → Legal S (.lt x y)
  | neg {S f} : Legal S f → Legal S (.neg f)
  | disj {S f g} : Legal S f → Legal S g → Legal S (.disj f g)
  | rootEx {f} : Legal [root] f → Legal [] (.ex root f)
  | childEx {S w a f} : (w, 0) ∈ S → child w a ∉ S →
      Legal (child w a :: S) f → Legal S (.ex (child w a) f)
  | continuation {S w i j f} : (w, j) ∈ S → j < i → (w, i) ∉ S →
      (∀ l < i, (w, l) ∈ S) → Legal ((w, i) :: S) f →
      Legal S (.ex (w, i) (conj (.edge (w, i) (w, j)) f))

def Plain {c : Nat} (S : List Var) : Formula c → Prop
  | .pred _ x => x ∈ S
  | .edge x y | .eq x y => x ∈ S ∧ y ∈ S
  | .lt _ _ => False
  | .neg f => Plain S f
  | .disj f g => Plain S f ∧ Plain S g
  | .ex x f => Plain (x :: S) f

def rank {c : Nat} : Formula c → Nat
  | .neg f => rank f
  | .disj f g => max (rank f) (rank g)
  | .ex _ f => rank f + 1
  | _ => 0

def eval {c : Nat} (G : Graph c) (ord : LinearOrder (Fin G.size))
    (env : Var → Option (Fin G.size)) : Formula c → Prop
  | .pred p x => ∃ u, env x = some u ∧ G.pred p u
  | .edge x y => ∃ u v, env x = some u ∧ env y = some v ∧ G.edge u v
  | .eq x y => ∃ u, env x = some u ∧ env y = some u
  | .lt x y => ∃ u v, env x = some u ∧ env y = some v ∧ ord.lt u v
  | .neg f => ¬ eval G ord env f
  | .disj f g => eval G ord env f ∨ eval G ord env g
  | .ex x f => ∃ u, eval G ord (fun y => if y = x then some u else env y) f

def Holds {c : Nat} (G : Graph c) (ord : LinearOrder (Fin G.size))
    (f : Formula c) : Prop := eval G ord (fun _ => none) f

def Unordered {c : Nat} (G : Graph c) (f : Formula c) : Prop :=
  Holds G inferInstance f

def InvariantOn {c : Nat} (C : Graph c → Prop) (f : Formula c) : Prop :=
  ∀ G, C G → ∀ o₁ o₂, Holds G o₁ f ↔ Holds G o₂ f

end Lax977378.Logic
