import Lax977378.Transport
import Mathlib.Tactic

namespace Lax977378Proofs.Transport
open Lax977378.Logic Lax977378.Blocks Lax977378.OuterContexts Lax977378.Stage

/--
---
conclusion: Lax977378.Transport.transport
assumptions:
  - Lax977378.ContextLabels.finiteLabels
  - Lax977378.Refinement.levelStep
---
Distinct child rows compare as in the source order. The first and last child
rows of each parent isolate their target endpoints. Apply the block evaluation
lemma at a representative, then use homogeneity of its source child row.
-/
theorem transport {c d n m i} (A B : Graph c) (ha : A.Bounded d) (hb : B.Bounded d)
    (a : LinearOrder (Fin A.size))
    (P : @Partition (Fin A.size) (Fin n) a inferInstance)
    (C : @Partition (Fin A.size) (Fin m) a inferInstance)
    (hom : ∀ x y, C.block x = C.block y → same A A a a (i+1) x y)
    (parent : ∀ x y, C.block x = C.block y → P.block x = P.block y)
    (singleF : ∀ x j, C.block x = C.block (P.first j) → x = P.first j)
    (singleL : ∀ x j, C.block x = C.block (P.last j) → x = P.last j)
    (rep : Fin B.size → Fin A.size) (hit : Function.Surjective (C.block ∘ rep))
    (f l : Fin n → Fin B.size) (rf : ∀ j, rep (f j) = P.first j)
    (rl : ∀ j, rep (l j) = P.last j)
    (uf : ∀ j z, rep z = P.first j → z = f j)
    (ul : ∀ j z, rep z = P.last j → z = l j)
    (lower : ∀ (b : LinearOrder (Fin B.size)), Compatible b (P.block ∘ rep) →
      ∀ x z, P.block x = P.block (rep z) → same A B a b i x z)
    (balls : ∀ z, ∃ h : Ball A (i+1) (rep z) ≃ Ball B (i+1) z,
      (∀ u, u.val = rep z ↔ (h u).val = z) ∧
      (∀ u v, A.edge u.val v.val ↔ B.edge (h u).val (h v).val) ∧
      Function.Injective (fun u : Ball A (i+1) (rep z) => P.block u.val) ∧
      (∀ u, P.block u.val = P.block (rep (h u).val)) ∧
      (∀ u, u.val = P.first (P.block u.val) ↔ (h u).val = f (P.block (rep (h u).val))) ∧
      (∀ u, u.val = P.last (P.block u.val) ↔ (h u).val = l (P.block (rep (h u).val)))) :
    ∀ (b : LinearOrder (Fin B.size)), Compatible b (C.block ∘ rep) →
      (∃ Q : @Partition (Fin B.size) (Fin n) b inferInstance,
        Q.block = P.block ∘ rep ∧ Q.first = f ∧ Q.last = l) ∧
      (∀ x z, C.block x = C.block (rep z) → same A B a b (i+1) x z) ∧
      spectrumAgrees A B a b (i+1) := by
  intro b hc
  have liftLE {x y : Fin A.size} (h : C.block x ≤ C.block y) : P.block x ≤ P.block y := by
    rcases lt_or_eq_of_le h with lt | eq
    · rcases @le_total _ a x y with le | le
      · exact P.monotone le
      · exact False.elim (lt.not_ge (C.monotone le))
    · exact le_of_eq (parent _ _ eq)
  have compat : Compatible b (P.block ∘ rep) :=
    fun x y h => liftLE (hc x y h)
  have strict {x y : Fin B.size} (h : C.block (rep x) < C.block (rep y)) : b.le x y := by
    rcases @le_total _ b x y with le | le
    · exact le
    · exact False.elim (h.not_ge (hc _ _ le))
  let Q : @Partition (Fin B.size) (Fin n) b inferInstance :=
    { block := P.block ∘ rep, monotone := fun {x y} => compat x y,
      first := f, last := l, first_mem := fun j => by simp [rf,P.first_mem],
      last_mem := fun j => by simp [rl,P.last_mem],
      first_le := by
        intro z
        let j := P.block (rep z)
        by_cases eq : z = f j
        · exact eq ▸ @le_refl _ b.toPreorder z
        · apply strict
          rw [rf]
          exact lt_of_le_of_ne (C.monotone (P.first_le _))
            (fun e => eq (uf _ _ (singleF _ _ e.symm)))
      le_last := by
        intro z
        let j := P.block (rep z)
        by_cases eq : z = l j
        · exact eq ▸ @le_refl _ b.toPreorder z
        · apply strict
          rw [rl]
          exact lt_of_le_of_ne (C.monotone (P.le_last _))
            (fun e => eq (ul _ _ (singleL _ _ e))) }
  have agree (x z) (e : C.block x = C.block (rep z)) : same A B a b (i+1) x z := by
    obtain ⟨h,root,edge,inj,blocks,first,last⟩ := balls z
    have hz := Lax977378.Refinement.levelStep A B a b P Q (lower b compat) (rep z) z
      h root edge inj blocks first last
    obtain ⟨_,label,labels⟩ := Lax977378.ContextLabels.finiteLabels c d (i+1)
    exact (labels A B ha hb a b x z).mp
      (((labels A A ha ha a a x (rep z)).mpr (hom x _ e)).trans ((labels ..).mpr hz))
  refine ⟨⟨Q,rfl,rfl,rfl⟩,agree,?_,fun z => ⟨rep z,agree _ _ rfl⟩⟩
  intro x
  obtain ⟨z,hz⟩ := hit (C.block x)
  exact ⟨z,agree _ _ hz.symm⟩

end Lax977378Proofs.Transport
