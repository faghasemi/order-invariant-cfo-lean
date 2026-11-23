import Lax977378.CountParameters
import Mathlib.Tactic

namespace Lax977378Proofs.CountParameters
open Lax977378.Logic Lax977378.RecordTests Lax977378.CountParameters Lax977378.Threshold

private theorem memLocations {c} {a : Pointed c} {r} {G : Graph c} {x} :
    x ∈ locations a r G ↔ Occurs a r G x := by classical simp [locations]

private theorem atLeastIff {c} (a : Pointed c) (r k : Nat) (G : Graph c) :
    AtLeast a r k G ↔ k ≤ (locations a r G).card := by
  classical
  let S := locations a r G
  constructor
  · rintro ⟨xs,hin,h⟩
    let f (j : Fin k) : S := ⟨xs j,memLocations.mpr (h j)⟩
    have inj : Function.Injective f := fun _ _ he => hin (congrArg Subtype.val he)
    simpa [S] using Fintype.card_le_of_injective f inj
  · intro hk
    let e := (Fin.castLEEmb hk).trans S.equivFin.symm.toEmbedding
    exact ⟨fun i => (e i).val, fun i j h => e.injective (Subtype.ext h),
      fun i => memLocations.mp (e i).property⟩

/--
---
conclusion: Lax977378.CountParameters.countTestValue
---
An injection of the requested number of indices into the set of occurrences
is equivalent to the corresponding cardinality bound.
-/
theorem countTestValue {c} (a : Pointed c) (r cap k : Nat) (G : Graph c) :
    (k ≤ cap ∧ AtLeast a r k G ∧ (k < cap → ¬ AtLeast a r (k+1) G)) ↔
      k = min cap (locations a r G).card := by
  rw [atLeastIff,atLeastIff]; omega

private theorem rareSum {n} (v : Fin n → Nat) (t : Nat) :
    rareTotal t (List.ofFn v) = ∑ j : Fin n, if v j < t then v j else 0 := by
  induction n with
  | zero => simp [rareTotal,List.ofFn_zero]
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    specialize ih (fun j => v j.succ)
    simp only [rareTotal,List.ofFn_succ] at *
    split_ifs with h <;> simp [h,ih]

/--
---
conclusion: Lax977378.CountParameters.fixedParameters
assumptions:
  - Lax977378.Threshold.uniformGap
---
Choose thresholds after fixing the catalogue, so their growth function can
include the number of palette assignments for that very catalogue.
-/
theorem fixedParameters {c d r n} (types : Fin n → Pointed c)
    (cover : ∀ G : Graph c, G.Bounded d → ∀ x, ∃! j, Occurs (types j) r G x)
    (h : Nat → Nat) (mono : Monotone h) :
    ∃ cap : Nat, ∃ threshold : (Fin n → Nat) → Nat,
∀ (G : Graph c), G.Bounded d →
        let counts := fun j => (locations (types j) r G).card
        let v := fun j => min cap (counts j)
        let t := threshold v
        Eligible h v cap t ∧ (∀ u, Eligible h v cap u → t ≤ u) ∧
        (∀ j, t ≤ v j ↔ t ≤ counts j) ∧
        (rareSet types r G v t).card = rareTotal t (List.ofFn v) ∧
        (rareSet types r G v t).card ≤ n * (cap-1) := by
  classical
  obtain ⟨cap,hu⟩ := Lax977378.Threshold.uniformGap n h mono
  have ex (v : Fin n → Nat) : ∃ t, Eligible h v cap t := hu _ (by simp)
  refine ⟨cap,fun v => Nat.find (ex v),?_⟩
  intro G hd counts v t
  have he : Eligible h v cap t := Nat.find_spec (ex v)
  have ht := he.2.1
  refine ⟨he,fun k hk => Nat.find_min' _ hk,fun j => by dsimp [v]; omega,?_⟩
  let name (x : Fin G.size) := (cover G hd x).exists.choose
  have occurs (x j) : Occurs (types j) r G x ↔ name x = j := by
    have hx := (cover G hd x).exists.choose_spec
    exact ⟨fun hj => (cover G hd x).unique hx hj,fun e => e ▸ hx⟩
  let low := Finset.univ.filter (fun j => v j < t)
  have loweq : rareSet types r G v t = Finset.univ.filter (fun x => name x ∈ low) := by
    ext x
    simp [rareSet,low,occurs]
  have fibre (j) : (Finset.univ.filter (fun x => name x = j)).card = counts j := by
    congr 1
    ext x
    simp [locations,occurs]
  have hr : (rareSet types r G v t).card = rareTotal t (List.ofFn v) := by
    rw [loweq, ← Finset.sum_card_fiberwise_eq_card_filter,rareSum]
    simp only [fibre]
    rw [show low = Finset.univ.filter (fun j => v j < t) from rfl,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with small
    · dsimp [v] at small ⊢; omega
    · rfl
  refine ⟨hr,?_⟩
  rw [hr, rareSum]
  calc
    _ ≤ ∑ _j : Fin n, (cap-1) := by
      gcongr with j
      split_ifs <;> omega
    _ = _ := by simp

/--
---
conclusion: Lax977378.CountParameters.parameters
assumptions:
  - Lax977378.Types.uniqueTypes
  - Lax977378.CountParameters.fixedParameters
---
Take the least eligible threshold for each vector. Unique type membership
partitions the rare vertices into disjoint fibres, whose cardinalities are
exactly the unsaturated low entries of the vector.
-/
theorem parameters (c d r : Nat) (h : Nat → Nat) (mono : Monotone h) :
    ∃ n : Nat, ∃ types : Fin n → Pointed c, ∃ cap : Nat,
    ∃ threshold : (Fin n → Nat) → Nat,
      (∀ G : Graph c, G.Bounded d → ∀ x, ∃! j, Occurs (types j) r G x) ∧
      ∀ (G : Graph c), G.Bounded d →
        let counts := fun j => (locations (types j) r G).card
        let v := fun j => min cap (counts j)
        let t := threshold v
        Eligible h v cap t ∧ (∀ u, Eligible h v cap u → t ≤ u) ∧
        (∀ j, t ≤ v j ↔ t ≤ counts j) ∧
        (rareSet types r G v t).card = rareTotal t (List.ofFn v) ∧
        (rareSet types r G v t).card ≤ n * (cap-1) := by
  classical
  obtain ⟨n,types,cover⟩ := Lax977378.Types.uniqueTypes c d r
  obtain ⟨cap,threshold,good⟩ := Lax977378.CountParameters.fixedParameters types cover h mono
  exact ⟨n,types,cap,threshold,cover,good⟩

end Lax977378Proofs.CountParameters
