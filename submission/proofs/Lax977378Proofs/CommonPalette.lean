import Lax977378.CommonPalette
import Mathlib.Tactic

namespace Lax977378Proofs.CommonPalette
open Lax977378.Logic Lax977378.Planting Lax977378.RecordTests Lax977378.CountParameters

/--
---
conclusion: Lax977378.CommonPalette.uniform
assumptions:
  - Lax977378.Types.uniqueTypes
  - Lax977378.ColouredTypes.colouredTypes
  - Lax977378.CountParameters.fixedParameters
  - Lax977378.Reservoir.reserve
---
First fix the catalogue and its number of coloured requests. Choose the
frequency gap with room for the entire excluded set and one more realisation
of every request than there can be exceptions.
-/
theorem uniform (c d r q : Nat) (palette : (d+1)^(r+r) ≤ q)
    (g : Nat → Nat) (mono : Monotone g) :
    ∃ n : Nat, ∃ types : Fin n → Pointed c, ∃ cap : Nat,
    ∃ threshold : (Fin n → Nat) → Nat, ∃ seeds : (Fin n → Nat) → List (Request c q),
    ∀ (G : Graph c), G.Bounded d →
      let v := fun j => min cap (locations (types j) r G).card
      let t := threshold v
      let Z := rareSet types r G v t
      0 < t ∧ t ≤ cap ∧ Z.card ≤ n*(cap-1) ∧
      (∀ κ, ProperOn G (r+r) Finset.univ κ → ∀ x ∉ Z,
        ∃ s ∈ seeds v, Realised s G r κ x) ∧
      ∀ (P : Finset (Fin G.size)) (colour : Fin G.size → Fin q),
        P.card ≤ g Z.card → ProperOn G (r+r) P colour →
        ∃ k, (∀ u ∈ P, k u = colour u) ∧ ProperOn G (r+r) Finset.univ k ∧
          ∀ s ∈ seeds v, ∀ M : Finset (Fin G.size), M.card ≤ g Z.card →
            ∃ x ∉ M, Realised s G r k x := by
  classical
  obtain ⟨n,types,cover⟩ := Lax977378.Types.uniqueTypes c d r
  obtain ⟨H,lists⟩ := Lax977378.ColouredTypes.colouredTypes types q
  choose all spec using lists
  let h (s : Nat) := (g s + (H*(g s+1))*(d+1)^r) * (d+1)^(2*r+(r+r)) + 1
  have mh : Monotone h := by
    intro a b hab
    have le := mono hab
    dsimp [h]; gcongr
  obtain ⟨cap,threshold,params⟩ := Lax977378.CountParameters.fixedParameters types cover h mh
  refine ⟨n,types,cap,threshold,fun v => all v (threshold v),?_⟩
  intro G hd v t Z
  obtain ⟨eligible,_,_,rare,small⟩ := params G hd
  change Eligible h v cap t at eligible
  change Z.card = _ at rare
  obtain ⟨len,freq,real⟩ := spec v t
  refine ⟨eligible.1,eligible.2.1,small,real G r,?_⟩
  intro P colour hP proper
  have room (s) (hs : s ∈ all v t) :
      (P.card + ((all v t).length * (g Z.card+1)) * (d+1)^r) * (d+1)^(2*r+(r+r)) <
        (locations s.type r G).card := by
    obtain ⟨j,hj,eq⟩ := freq s hs
    rw [eq]
    have allowance : h Z.card ≤ t := by rw [rare]; exact eligible.2.2
    apply lt_of_lt_of_le _ (hj.trans (min_le_right _ _))
    apply lt_of_lt_of_le _ allowance
    apply Nat.lt_succ_of_le
    gcongr
  obtain ⟨k,keep,ok,more⟩ := Lax977378.Reservoir.reserve G hd r (r+r) (g Z.card+1)
    palette P colour proper (all v t) room
  refine ⟨k,keep,ok,?_⟩
  intro s hs M hM
  obtain ⟨x,out,hx,_⟩ := more s hs M (by omega)
  exact ⟨x,out,hx⟩

end Lax977378Proofs.CommonPalette
