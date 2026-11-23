import Lax977378.CountParameters

/-!
---
title: Prescribing coloured neighbourhoods outside the exceptional set
type: lemma
---
Each entry in the request list prescribes an injective colouring of an
uncoloured rooted neighbourhood. Repetition prescribes multiplicity. Given
enough occurrences, one proper colouring of the graph power realises every
entry at a separated centre and extends the colouring on the excluded set.
-/
namespace Lax977378.Planting
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests Lax977378.CountParameters

structure Request (c q : Nat) where
  type : Pointed c
  paint : Fin type.pattern.size → Fin q
  inj : Function.Injective paint

def Realised {c q} (s : Request c q) (G : Graph c) (r : Nat) (k : Fin G.size → Fin q)
    (x : Fin G.size) : Prop :=
  ∃ y, Window s.type.pattern G r {s.type.center} y ∧ y s.type.center = x ∧
    ∀ i, k (y i) = s.paint i

def ProperOn {c q} (G : Graph c) (p : Nat) (P : Finset (Fin G.size))
    (k : Fin G.size → Fin q) : Prop :=
  ∀ u ∈ P, ∀ v ∈ P, u ≠ v → within G p u v → k u ≠ k v

axiom plant {c d q : Nat} (G : Graph c) (hd : G.Bounded d) (r p : Nat)
    (palette : (d+1)^p ≤ q) (P : Finset (Fin G.size)) (colour : Fin G.size → Fin q)
    (proper : ProperOn G p P colour) (requests : List (Request c q))
    (enough : ∀ s ∈ requests, (P.card + requests.length * (d+1)^r) * (d+1)^(2*r+p) <
      (locations s.type r G).card) :
    ∃ k : Fin G.size → Fin q, ∃ centres : List (Fin G.size),
      (∀ u ∈ P, k u = colour u) ∧ ProperOn G p Finset.univ k ∧
      List.Forall₂ (fun x s => Realised s G r k x) centres requests ∧
      (∀ x ∈ centres, ∀ u ∈ P, ¬ within G (2*r+p) u x) ∧
      centres.Pairwise (fun x y => ¬ within G (2*r+p) x y)

end Lax977378.Planting
