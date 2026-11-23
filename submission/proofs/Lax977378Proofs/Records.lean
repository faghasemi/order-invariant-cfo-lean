import Lax977378.CheckedEntries
import Lax977378.TargetOrder
import Lax977378.CommonPalette
import Lax977378.WindowColour
import Lax977378Proofs.Planting
import Mathlib.Tactic

namespace Lax977378Proofs.Records
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Collapse Lax977378.Stage
open Lax977378.SourceRun Lax977378.SourceTables Lax977378.TagSafety Lax977378.CountParameters
open Lax977378.Planting Lax977378.RecordTests

private theorem limitMono (d : Nat) (N : Nat → Nat) (j : Nat) :
    Monotone (fun s => limit d N s j) := by
  induction j with
  | zero => exact monotone_id
  | succ i ih => intro x y h; exact Nat.mul_le_mul_left _ (ih h)

set_option maxHeartbeats 1500000

/--
---
conclusion: Lax977378.Collapse.records
assumptions:
  - Lax977378.ContextLabels.finiteLabels
  - Lax977378.SourceRecord.sourceRecord
  - Lax977378.CommonPalette.uniform
  - Lax977378.CheckedEntries.selectEntries
  - Lax977378.TargetWindow.targetWindow
  - Lax977378.WindowColour.precolour
  - Lax977378.TargetOrder.targetOrder
---
Choose the growth allowance before taking the frequency gap. Extract the
source record from a colouring with reserves. On every passing target copy
the inner window colouring, plant the same frequent requests, and realise
the recorded spectrum using the independent target order.
-/
theorem records (c d K : Nat) : ∃ tests : List (Record (c := c) d K),
    ∀ G, G.Bounded d → ∃ e ∈ tests, Unordered G e.test := by
  classical
  obtain ⟨N,source⟩ := Lax977378.SourceRecord.sourceRecord c d K
  obtain ⟨num,lab,labels⟩ := Lax977378.ContextLabels.finiteLabels c d K
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
  refine Lax977378.CheckedEntries.selectEntries types r R cap
    (bound (n*(cap-1))*(d+1)^R) lab (fun _ _ _ _ _ _ _ _ => (labels ..).mp) ?_
  intro A ha
  let v := vec A
  let t := threshold v
  let Z := rareSet types r A v t
  obtain ⟨_,tcap,rareBound,typesA,paintA⟩ := uniform A ha
  have qpos : 0 < q := by dsimp [q]; positivity
  obtain ⟨κ,_,proper,copiesA⟩ := paintA ∅ (fun _ => ⟨0,qpos⟩) (by simp) (by simp [ProperOn])
  have smaller : ProperOn A (K+K) Finset.univ κ := fun x hx u hu ne path =>
    proper x hx u hu ne (Window.grow path (Nat.add_le_add kr kr))
  obtain ⟨a,T,D,zero,base,next,numExc,hr,hR,hcap,cnts,freq,wbound,⟨y,wy,named,rareA⟩,passA⟩ :=
    source A ha q κ smaller types r R cap t v (fun _ => rfl)
  have sourceRare : Z ⊆ (T K).exceptions := by
    have inc j (hj : j ≤ K) : Z ⊆ (T j).exceptions := by
      induction j with
      | zero => exact zero ▸ Finset.Subset.rfl
      | succ j ih =>
        intro x hx
        exact ((next j (by omega)).1 x).mpr ⟨x,Or.inl (ih (by omega) hx),Catalogue.centerWithin ..⟩
    exact inc K le_rfl
  let values j : Fin (cap+1) := ⟨v j,Nat.lt_succ_of_le (min_le_left ..)⟩
  refine ⟨D,Finset.univ.image (lab A ha a),values,t,hr,hR,hcap,
    wbound.trans (Nat.mul_le_mul_right _ (mono rareBound)),cnts,freq,passA,?_⟩
  intro B hb passB
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
      exact smaller _ (by simp) _ (by simp) ne (Window.join (Planting.reverseWithin u.property) w.property) col
  have bbase := base
  rw [←zero] at bbase
  obtain ⟨b,agree⟩ := Lax977378.TargetOrder.targetOrder D.windowGraph A B ha hb a T next κ k bbase sep
    D.marked y z wy wz named (fun j h => ((keep _ (localCol j h).1).trans (localCol j h).2).symm)
    (seeds v) (fun x hx => typesA κ proper x (fun h => hx (sourceRare h)))
    (fun x hx => typesB k properB x (fun h => hx (targetRare h)))
    (fun s hs => copiesA s hs _ (numExc.trans (bg _)))
    (fun s hs => copiesB s hs _ (by rw [Finset.card_image_of_injective _ wz.1.1,cardM,cardZ]; exact numExc.trans (bg _)))
  refine ⟨b,Finset.Subset.antisymm ?_ ?_⟩
  · intro v hv
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨x,h⟩ := agree.2 z
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,(labels ..).mpr h⟩
  · intro v hv
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨z,h⟩ := agree.1 x
    exact Finset.mem_image.mpr ⟨z,Finset.mem_univ _,((labels ..).mpr h).symm⟩

end Lax977378Proofs.Records
