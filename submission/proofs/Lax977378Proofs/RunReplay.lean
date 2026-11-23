import Lax977378.RunReplay
import Mathlib.Tactic

namespace Lax977378Proofs.RunReplay
open Lax977378.Logic Lax977378.Blocks Lax977378.OuterContexts Lax977378.Stage
open Lax977378.CallAgreement

/--
---
conclusion: Lax977378.RunReplay.runReplay
assumptions:
  - Lax977378.CallAgreement.lowerRanks
  - Lax977378.CallAgreement.compareReps
  - Lax977378.Transport.transport
---
Induct on the rank, for every compatible target order. At a ball vertex the
recursive comparison and the fixed representative meet the same target call.
The source name is therefore the same. Endpoint fibres are singletons, so
the target endpoints read from their preimages have precisely the given roles.
-/
theorem runReplay {c d K} (A B : Graph c) (ha : A.Bounded d) (hb : B.Bounded d)
    (a : LinearOrder (Fin A.size)) (n : Nat → Nat)
    (P : (j : Nat) → @Partition (Fin A.size) (Fin (n j)) a inferInstance)
    (ra ea : Nat → Fin A.size → Nat) (rb eb : Nat → Fin B.size → Nat)
    (rep : Fin B.size → Fin A.size)
    (matched : ∀ z, agrees A B ra ea rb eb K (rep z) z)
    (hit : ∀ j ≤ K, Function.Surjective ((P j).block ∘ rep))
    (base : ∀ x z, (P 0).block x = (P 0).block (rep z) → ∀ p, A.pred p x ↔ B.pred p z)
    (names : ∀ j ≤ K, ∀ x y, agrees A A ra ea ra ea j x y → (P j).block x = (P j).block y)
    (hom : ∀ j ≤ K, ∀ x y, (P j).block x = (P j).block y → same A A a a j x y)
    (parent : ∀ j < K, ∀ x y, (P (j+1)).block x = (P (j+1)).block y → (P j).block x = (P j).block y)
    (ends : ∀ j < K, ∀ t, ∀ e ∈ [(P j).first t,(P j).last t],
      (∀ x, (P (j+1)).block x = (P (j+1)).block e → x = e) ∧ ∃! z, rep z = e)
    (separated : ∀ j < K, ∀ x, Function.Injective (fun v : Ball A (j+1) x => (P j).block v.val))
    (roles : ∀ j < K, ∀ x z, ea (j+1) x = eb (j+1) z →
      (x = (P j).first ((P j).block x) ↔ rep z = (P j).first ((P j).block (rep z))) ∧
      (x = (P j).last ((P j).block x) ↔ rep z = (P j).last ((P j).block (rep z)))) :
    ∀ j ≤ K, ∀ (b : LinearOrder (Fin B.size)), Compatible b ((P j).block ∘ rep) →
      (∀ x z, (P j).block x = (P j).block (rep z) → same A B a b j x z) ∧
      spectrumAgrees A B a b j := by
  classical
  have atRank (j) (hj : j ≤ K) (z) :=
    Lax977378.CallAgreement.lowerRanks A B ra ea rb eb K j hj _ _ (matched z)
  intro j
  induction j with
  | zero =>
    intro hj b _
    refine ⟨base,?_,fun z => ⟨rep z,base _ _ rfl⟩⟩
    intro x
    obtain ⟨z,hz⟩ := hit 0 hj ((P 0).block x)
    exact ⟨z,base _ _ hz.symm⟩
  | succ j ih =>
    intro hj b hc
    have hj' : j < K := by omega
    have first t := ends j hj' t ((P j).first t) (by simp)
    have last t := ends j hj' t ((P j).last t) (by simp)
    let f t := (first t).2.exists.choose
    let l t := (last t).2.exists.choose
    have rf t : rep (f t) = (P j).first t := (first t).2.exists.choose_spec
    have rl t : rep (l t) = (P j).last t := (last t).2.exists.choose_spec
    have uf t z (h : rep z = (P j).first t) : z = f t := (first t).2.unique h (rf t)
    have ul t z (h : rep z = (P j).last t) : z = l t := (last t).2.unique h (rl t)
    apply And.right (a := ∃ Q : @Partition (Fin B.size) (Fin (n j)) b inferInstance,
      Q.block = (P j).block ∘ rep ∧ Q.first = f ∧ Q.last = l)
    apply Lax977378.Transport.transport A B ha hb a (P j) (P (j+1)) (hom _ hj)
      (parent _ hj') (fun x t => (first t).1 x) (fun x t => (last t).1 x) rep (hit _ hj)
      f l rf rl uf ul (fun o ho => (ih (by omega) o ho).1) _ b hc
    intro z
    obtain ⟨_,h,root,edge,call⟩ := atRank _ hj z
    refine ⟨h,root,edge,separated _ hj' _,?_,?_,?_⟩
    · intro u
      exact names j (by omega) _ _ (Lax977378.CallAgreement.compareReps A B ra ea rb eb j _ _ _
        (call u).2 (atRank j (by omega) (h u).val))
    · intro u
      exact ((roles j hj' _ _ (call u).1).1).trans
        ⟨uf _ _,fun e => (congrArg rep e).trans (rf _)⟩
    · intro u
      exact ((roles j hj' _ _ (call u).1).2).trans
        ⟨ul _ _,fun e => (congrArg rep e).trans (rl _)⟩

end Lax977378Proofs.RunReplay
