import Lax977378.Types
import Lax977378.Threshold

/-!
---
title: The threshold and rare set determined by a truncated count vector
type: lemma
---
The vector indexed by the non-repeating catalogue determines the least eligible
threshold and the exact number of rare vertices. These are uniform parameters
for every graph with the given vector. Saturated entries suffice for each
frequent type, while the low entries still give exact cardinalities.
-/
namespace Lax977378.CountParameters
open Lax977378.Logic Lax977378.RecordTests

noncomputable def locations {c} (t : Pointed c) (r : Nat) (G : Graph c) : Finset (Fin G.size) := by
  classical exact Finset.univ.filter (Occurs t r G)

noncomputable def rareSet {c n} (types : Fin n → Pointed c) (r : Nat) (G : Graph c)
    (v : Fin n → Nat) (t : Nat) : Finset (Fin G.size) := by
  classical exact Finset.univ.filter (fun x => ¬ ∃ j, t ≤ v j ∧ Occurs (types j) r G x)

def Eligible {n} (h : Nat → Nat) (v : Fin n → Nat) (cap t : Nat) : Prop :=
  0 < t ∧ t ≤ cap ∧ h (Threshold.rareTotal t (List.ofFn v)) ≤ t

axiom countTestValue {c} (a : Pointed c) (r cap k : Nat) (G : Graph c) :
    (k ≤ cap ∧ AtLeast a r k G ∧ (k < cap → ¬ AtLeast a r (k+1) G)) ↔
      k = min cap (locations a r G).card

axiom fixedParameters {c d r n} (types : Fin n → Pointed c)
    (cover : ∀ G : Graph c, G.Bounded d → ∀ x, ∃! j, Occurs (types j) r G x)
    (h : Nat → Nat) (mono : Monotone h) :
    ∃ cap : Nat, ∃ threshold : (Fin n → Nat) → Nat,
∀ (G : Graph c), G.Bounded d →
        let counts := fun j => (locations (types j) r G).card
        let v := fun j => min cap (counts j)
        let t := threshold v
        Eligible h v cap t ∧ (∀ u, Eligible h v cap u → t ≤ u) ∧
        (∀ j, t ≤ v j ↔ t ≤ counts j) ∧
        (rareSet types r G v t).card = Threshold.rareTotal t (List.ofFn v) ∧
        (rareSet types r G v t).card ≤ n * (cap-1)

axiom parameters (c d r : Nat) (h : Nat → Nat) (mono : Monotone h) :
    ∃ n : Nat, ∃ types : Fin n → Pointed c, ∃ cap : Nat,
    ∃ threshold : (Fin n → Nat) → Nat,
      (∀ G : Graph c, G.Bounded d → ∀ x, ∃! j, Occurs (types j) r G x) ∧
      ∀ (G : Graph c), G.Bounded d →
        let counts := fun j => (locations (types j) r G).card
        let v := fun j => min cap (counts j)
        let t := threshold v
        Eligible h v cap t ∧ (∀ u, Eligible h v cap u → t ≤ u) ∧
        (∀ j, t ≤ v j ↔ t ≤ counts j) ∧
        (rareSet types r G v t).card = Threshold.rareTotal t (List.ofFn v) ∧
        (rareSet types r G v t).card ≤ n * (cap-1)

end Lax977378.CountParameters
