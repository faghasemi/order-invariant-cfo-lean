import Lax977378.CoverReplay
import Lax977378Proofs.SourceRun

namespace Lax977378Proofs.CoverReplay
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Blocks Lax977378.CallAgreement

private theorem readRoot {c} {A B : Graph c} {ra ea rb eb i x z}
    (h : agrees A B ra ea rb eb i x z) : ra i x = rb i z := by
  cases i with
  | zero => exact h
  | succ i => exact h.1

/--
---
conclusion: Lax977378.CoverReplay.orderFromCover
assumptions:
  - Lax977378.LocalNames.names
  - Lax977378.CallAgreement.lowerRanks
  - Lax977378.CallAgreement.compareReps
  - Lax977378.RunReplay.runReplay
---
Reverse coverage gives a witness at every source vertex. Compare that witness
to the chosen representative at the same target. They agree on the source
row at every lower level. The full root tag isolates each named endpoint.
-/
theorem orderFromCover {c d K} (A B : Graph c) (ha : A.Bounded d) (hb : B.Bounded d)
    (a : LinearOrder (Fin A.size)) (n : Nat → Nat)
    (P : (j : Nat) → @Partition (Fin A.size) (Fin (n j)) a inferInstance)
    (ra ea : Nat → Fin A.size → Nat) (rb eb : Nat → Fin B.size → Nat)
    (fwd : ∀ x, ∃ z, agrees A B ra ea rb eb K x z)
    (back : ∀ z, ∃ x, agrees A B ra ea rb eb K x z)
    (pred : ∀ x z, ra 0 x = rb 0 z → ∀ p, A.pred p x ↔ B.pred p z)
    (base : ∀ x y, ra 0 x = ra 0 y → (P 0).block x = (P 0).block y)
    (child : ∀ j < K, ∀ x y, ra (j+1) x = ra (j+1) y → (P j).block x = (P j).block y →
      same A A a a (j+1) x y → (P (j+1)).block x = (P (j+1)).block y)
    (hom : ∀ j ≤ K, ∀ x y, (P j).block x = (P j).block y → same A A a a j x y)
    (parent : ∀ j < K, ∀ x y, (P (j+1)).block x = (P (j+1)).block y → (P j).block x = (P j).block y)
    (ends : ∀ j < K, ∀ t, ∀ e ∈ [(P j).first t,(P j).last t],
      (∀ x, (P (j+1)).block x = (P (j+1)).block e → x = e) ∧
      (∀ x, ra K x = ra K e → x = e) ∧ ∀ z w, rb K z = ra K e → rb K w = ra K e → z = w)
    (separated : ∀ j < K, ∀ x, Function.Injective (fun v : Ball A (j+1) x => (P j).block v.val))
    (roles : ∀ j < K, ∀ x y, ea (j+1) x = ea (j+1) y →
      (x = (P j).first ((P j).block x) ↔ y = (P j).first ((P j).block y)) ∧
      (x = (P j).last ((P j).block x) ↔ y = (P j).last ((P j).block y))) :
    ∃ b, spectrumAgrees A B a b K := by
  classical
  choose rep matched using back
  have lower (i) (hi : i ≤ K) {x z} (h : agrees A B ra ea rb eb K x z) :=
    Lax977378.CallAgreement.lowerRanks A B ra ea rb eb K i hi x z h
  have names := Lax977378.LocalNames.names A a n P ra ea base child
    (fun j hj => hom j (Nat.le_of_lt hj)) separated roles
  have hits j (hj : j ≤ K) : Function.Surjective ((P j).block ∘ rep) := by
    intro t
    let x := (P j).first t
    obtain ⟨z,hz⟩ := fwd x
    have eq := names j hj _ _ (Lax977378.CallAgreement.compareReps A B ra ea rb eb j _ _ _
      (lower j hj (matched z)) (lower j hj hz))
    exact ⟨z,eq.trans ((P j).first_mem t)⟩
  have basal x z (eq : (P 0).block x = (P 0).block (rep z)) (p) :=
    (hom 0 (Nat.zero_le _) x _ eq p).trans (pred _ z (readRoot (lower 0 (Nat.zero_le _) (matched z))) p)
  have endpoint j (hj : j < K) t e (he : e ∈ [(P j).first t,(P j).last t]) :
      (∀ x, (P (j+1)).block x = (P (j+1)).block e → x = e) ∧ ∃! z, rep z = e := by
    obtain ⟨singleton,src,tgt⟩ := ends j hj t e he
    obtain ⟨z,hz⟩ := fwd e
    have tag := (readRoot hz).symm
    refine ⟨singleton,z,src _ ((readRoot (matched z)).trans tag),?_⟩
    intro w hw
    exact tgt w z ((readRoot (matched w)).symm.trans (congrArg (ra K) hw)) tag
  have role j (hj : j < K) x z (eq : ea (j+1) x = eb (j+1) z) :
      (x = (P j).first ((P j).block x) ↔ rep z = (P j).first ((P j).block (rep z))) ∧
      (x = (P j).last ((P j).block x) ↔ rep z = (P j).last ((P j).block (rep z))) := by
    obtain ⟨_,h,ctr,_,nodes⟩ := lower (j+1) hj (matched z)
    let u : Ball A (j+1) (rep z) := ⟨rep z,Catalogue.centerWithin ..⟩
    have target := (ctr u).mp (show u.val = rep z from rfl)
    have endsEq : ea (j+1) (rep z) = eb (j+1) z := by simpa only [target,u] using (nodes u).1
    exact roles j hj x (rep z) (eq.trans endsEq.symm)
  obtain ⟨b,hb'⟩ := SourceRun.compatibleOrder ((P K).block ∘ rep)
  exact ⟨b,(Lax977378.RunReplay.runReplay A B ha hb a n P ra ea rb eb rep matched
    hits basal names hom parent endpoint separated role K le_rfl b hb').2⟩

end Lax977378Proofs.CoverReplay
