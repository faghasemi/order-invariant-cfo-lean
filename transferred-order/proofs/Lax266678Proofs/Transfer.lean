import Lax266678.Transfer
import Lax977378.SourceRecord
import Lax977378.TargetWindow
import Lax977378.TargetOrder
import Lax977378.CommonPalette
import Lax977378.WindowColour
import Lax266678.WindowRank
import Mathlib.Tactic

namespace Lax266678Proofs.Transfer
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Stage
open Lax977378.SourceRun Lax977378.SourceTables Lax977378.TagSafety Lax977378.CountParameters
open Lax977378.Planting Lax977378.RecordTests Lax977378

private theorem grow {c : Nat} {G : Graph c} {r s : Nat} {x y : Fin G.size}
    (h : within G r x y) (hrs : r ≤ s) : within G s x y := by
  induction s, hrs using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact Or.inl ih

private theorem join {c : Nat} {G : Graph c} {r s : Nat} {x y z : Fin G.size}
    (h : within G r x y) (k : within G s y z) : within G (r+s) x z := by
  induction s generalizing z with
  | zero => exact (show y = z from k) ▸ h
  | succ s ih =>
    rcases k with k | ⟨v,hv,he⟩
    · exact Or.inl (ih k)
    · exact Or.inr ⟨v,ih hv,he⟩

private theorem centerWithin {c : Nat} (G : Graph c) (r : Nat) (x : Fin G.size) : within G r x x := by
  induction r with
  | zero => rfl
  | succ r ih => exact Or.inl ih

private theorem reverseWithin {c} {G : Graph c} {r : Nat} {x y : Fin G.size}
    (h : within G r x y) : within G r y x := by
  induction r generalizing y with
  | zero => exact Eq.symm h
  | succ r ih =>
    rcases h with h | ⟨z,hz,he⟩
    · exact Or.inl (ih h)
    · have step : within G 1 y z := Or.inr ⟨y,rfl,G.symm _ _ he⟩
      simpa [Nat.add_comm] using join step (ih hz)

private theorem limitMono (d : Nat) (N : Nat → Nat) (j : Nat) :
    Monotone (fun s => limit d N s j) := by
  induction j with
  | zero => exact monotone_id
  | succ i ih => intro x y h; exact Nat.mul_le_mul_left _ (ih h)

set_option maxHeartbeats 1500000

/--
---
conclusion: Lax266678.Transfer.transferOrder
assumptions:
  - Lax977378.SourceRecord.sourceRecord
  - Lax977378.CommonPalette.uniform
  - Lax266678.WindowRank.windowSentence
  - Lax977378.TargetWindow.targetWindow
  - Lax977378.WindowColour.precolour
  - Lax977378.TargetOrder.targetOrder
---
Bound the number of rare vertices and the size of the exceptional neighbourhood
before choosing either graph. The bound on the number of window vertices and the maximum size of a
pointed neighbourhood pattern give an explicit rank budget for the count and
induced-neighbourhood sentence. Choose the source colouring, the refinement order and its endpoints.
Rank equivalence transfers the actual source neighbourhood sentence to the target.
Copy the inner colouring, realise the frequent coloured types away from the
exceptional vertices, and transfer the source order along the resulting window.
-/
theorem transferOrder (c d K : Nat) : ∃ q : Nat, ∀ A : Graph c, A.Bounded d →
    ∃ a : LinearOrder (Fin A.size), ∀ B : Graph c, B.Bounded d →
      Lax266678.Transfer.equivalentAt q A B →
      ∃ b : LinearOrder (Fin B.size), spectrumAgrees A B a b K := by
  classical
  obtain ⟨N,source⟩ := Lax977378.SourceRecord.sourceRecord c d K
  let r := radius K
  let p := r+r
  let R := r+p
  let q := (d+1)^p
  let bound s := limit d N (s+2^c*q) K
  let g s := bound s * (d+1)^r
  have bg s : bound s ≤ g s := Nat.le_mul_of_pos_right _ (by positivity)
  have mono : Monotone bound := fun _ _ h => limitMono d N K (Nat.add_le_add_right h _)
  have gm : Monotone g := fun _ _ h => Nat.mul_le_mul_right _ (mono h)
  obtain ⟨n,types,cap,threshold,seeds,uniform⟩ := Lax977378.CommonPalette.uniform c d r q le_rfl g gm
  let vec (G : Graph c) (j : Fin n) := min cap (locations (types j) r G).card
  have kr : K ≤ r := by cases K with
                         | zero => exact Nat.zero_le _
                         | succ j => exact Nat.le_add_left _ _
  let patternSize (j : Fin n) := (types j).pattern.size
  let ballBound := Finset.univ.sup patternSize
  have smallPattern (j : Fin n) : (types j).pattern.size ≤ ballBound :=
    Finset.le_sup (f := patternSize) (Finset.mem_univ j)
  let windowBound := bound (n*(cap-1)) * (d+1)^R
  let qFO := Lax266678.WindowRank.bound ballBound r cap windowBound R
  refine ⟨qFO,?_⟩
  intro A ha
  let v := vec A
  let t := threshold v
  let Z := rareSet types r A v t
  obtain ⟨_,tcap,rareBound,typesA,paintA⟩ := uniform A ha
  have qpos : 0 < q := by dsimp [q]; positivity
  obtain ⟨κ,_,proper,copiesA⟩ := paintA ∅ (fun _ => ⟨0,qpos⟩) (by simp) (by simp [ProperOn])
  have smaller : ProperOn A (K+K) Finset.univ κ := fun x hx u hu ne path =>
    proper x hx u hu ne (grow path (Nat.add_le_add kr kr))
  obtain ⟨a,T,D,zero,base,next,numExc,hr,hR,hcap,cnts,freq,wbound,⟨y,wy,named,rareA⟩,passA⟩ :=
    source A ha q κ smaller types r R cap t v (fun _ => rfl)
  have sourceRare : Z ⊆ (T K).exceptions := by
    have inc j (hj : j ≤ K) : Z ⊆ (T j).exceptions := by
      induction j with
      | zero => exact zero ▸ Finset.Subset.rfl
      | succ j ih =>
        intro x hx
        exact ((next j (by omega)).1 x).mpr ⟨x,Or.inl (ih (by omega) hx),centerWithin ..⟩
    exact inc K le_rfl
  obtain ⟨ω,plainω,rankω,description⟩ :=
    Lax266678.WindowRank.windowSentence D ballBound windowBound (by
      intro e he
      rw [cnts] at he
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
      exact ⟨smallPattern j,hcap ▸ min_le_left ..⟩) (by
      intro e he
      rw [freq] at he
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
      exact smallPattern j) (wbound.trans (Nat.mul_le_mul_right _ (mono rareBound)))
  rw [hr,hR,hcap] at rankω
  refine ⟨a,?_⟩
  intro B hb eq
  have passB := (description B).mp ((eq ω plainω rankω).mp ((description A).mpr passA))
  obtain ⟨cb,_,z,wz,rareB,_⟩ := Lax977378.TargetWindow.targetWindow A B D types v t
    (hcap.symm ▸ tcap) cnts freq y (hR.symm ▸ wy) passB
  rw [hr,hcap] at cb
  rw [hr] at rareB
  rw [hR] at wz
  have sameV : vec B = v := funext (fun j => (cb j).symm)
  let Zb := rareSet types r B v t
  have cardZ : Zb.card = Z.card := by
    change (rareSet types r B v t).card = (rareSet types r A v t).card
    rw [← rareB,←rareA,Finset.card_image_of_injective _ wz.1.1,Finset.card_image_of_injective _ wy.1.1]
  have cardM : D.marked.card = (T K).exceptions.card := by
    rw [←named,Finset.card_image_of_injective _ wy.1.1]
  have rareMarks : D.rare ⊆ D.marked := by
    intro j hj
    have h : y j ∈ Z := by change y j ∈ rareSet types r A v t; rw [←rareA]; exact Finset.mem_image_of_mem _ hj
    obtain ⟨u,hu,eq⟩ := Finset.mem_image.mp (named.symm ▸ sourceRare h)
    exact wy.1.1 eq ▸ hu
  have targetRare : Zb ⊆ D.marked.image z := by
    change rareSet types r B v t ⊆ _
    rw [←rareB]; exact Finset.image_subset_image rareMarks
  obtain ⟨P,paint,psz,hprop,localCol⟩ := Lax977378.WindowColour.precolour D.windowGraph A B hb D.marked
    y z wy wz κ proper qpos
  have allowance : P.card ≤ g Zb.card := by
    rw [cardZ]; apply psz.trans
    rw [cardM]; exact Nat.mul_le_mul_right _ numExc
  have ub := uniform B hb
  change 0 < threshold (vec B) ∧ threshold (vec B) ≤ cap ∧
    (rareSet types r B (vec B) (threshold (vec B))).card ≤ n*(cap-1) ∧ _ at ub
  have hv : (fun j => min cap (locations (types j) r B).card) = v := sameV
  unfold vec at ub
  rw [hv] at ub
  obtain ⟨_,_,_,typesB,paintB⟩ := ub
  obtain ⟨k,keep,properB,copiesB⟩ := paintB P paint allowance hprop
  have sep x : Function.Injective (fun u : Ball A K x => (T 0).part.block u.val) := by
    intro u w eq
    apply Subtype.ext
    rcases (base _ _).mp eq with h | ⟨_,_,col,_⟩
    · exact h
    · by_contra ne
      exact smaller _ (by simp) _ (by simp) ne (join (reverseWithin u.property) w.property) col
  have bbase := base
  rw [←zero] at bbase
  obtain ⟨b,agree⟩ := Lax977378.TargetOrder.targetOrder D.windowGraph A B ha hb a T next κ k bbase sep
    D.marked y z wy wz named (fun j h => ((keep _ (localCol j h).1).trans (localCol j h).2).symm)
    (seeds v) (fun x hx => typesA κ proper x (fun h => hx (sourceRare h)))
    (fun x hx => typesB k properB x (fun h => hx (targetRare h)))
    (fun s hs => copiesA s hs _ (numExc.trans (bg _)))
    (fun s hs => copiesB s hs _ (by rw [Finset.card_image_of_injective _ wz.1.1,cardM,cardZ]; exact numExc.trans (bg _)))
  exact ⟨b,agree⟩

end Lax266678Proofs.Transfer
