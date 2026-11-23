import Lax977378.LocalCover
import Mathlib.Tactic

namespace Lax977378Proofs.LocalCover
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests Lax977378.Planting
open Lax977378.TagSafety Lax977378.OrdinaryCalls Lax977378.LocalCalls

/--
---
conclusion: Lax977378.LocalCover.coverCalls
assumptions:
  - Lax977378.LocalCalls.innerCalls
  - Lax977378.LocalCalls.commonCalls
  - Lax977378.OrdinaryCalls.untagged
---
Two copies of a coloured request give an untagged comparison by their
common numbering. Named exceptional vertices instead use the inner window
with the recorded data. The argument works from either graph.
-/
theorem coverCalls {c q K slack} (W A B : Graph c) (mark : Finset (Fin W.size))
    (y : Fin W.size → Fin A.size) (z : Fin W.size → Fin B.size)
    (wy : Window W A (radius K+slack) mark y) (wz : Window W B (radius K+slack) mark z)
    (X E : Nat → Finset (Fin A.size)) (Y F : Nat → Finset (Fin B.size))
    (covA : Covers A K X E) (covB : Covers B K Y F)
    (markA : mark.image y = X K) (markB : mark.image z = Y K)
    (a : Fin A.size → Fin q) (b : Fin B.size → Fin q)
    (root ends : Nat → Fin A.size → Fin B.size → Prop)
    (inside : ∀ i ≤ K, ∀ u, (∃ m ∈ mark, within W (radius K) m u) →
      root i (y u) (z u) ∧ ends i (y u) (z u))
    (ordinary : ∀ i ≤ K, ∀ x ∉ X i, ∀ w ∉ Y i,
      a x = b w ∧ (∀ p, A.pred p x ↔ B.pred p w) → root i x w)
    (interior : ∀ i < K, ∀ x ∉ E (i+1), ∀ w ∉ F (i+1), ends (i+1) x w)
    (seeds : List (Request c q))
    (typesA : ∀ x ∉ X K, ∃ s ∈ seeds, Realised s A (radius K) a x)
    (typesB : ∀ w ∉ Y K, ∃ s ∈ seeds, Realised s B (radius K) b w)
    (copiesA : ∀ s ∈ seeds, ∃ x ∉ X K, Realised s A (radius K) a x)
    (copiesB : ∀ s ∈ seeds, ∃ w ∉ Y K, Realised s B (radius K) b w) :
    (∀ x, ∃ w, Calls A B root ends K x w) ∧ (∀ w, ∃ x, Calls A B root ends K x w) := by
  classical
  have named m (hm : m ∈ mark) : Calls A B root ends K (y m) (z m) :=
    Lax977378.LocalCalls.innerCalls W A B mark y z root ends K 0 slack
      (by simpa using wy) (by simpa using wz) (by simpa using inside) m ⟨m,hm,rfl⟩
  let colour := fun (_ : Nat) (x : Fin A.size) (w : Fin B.size) =>
    a x = b w ∧ ∀ p, A.pred p x ↔ B.pred p w
  have pair (s : Request c q) (x w) (hx : x ∉ X K) (hw : w ∉ Y K)
      (ha : Realised s A (radius K) a x) (hb : Realised s B (radius K) b w) :
      Calls A B root ends K x w := by
    obtain ⟨ya,wa,rfl,ca⟩ := ha
    obtain ⟨zb,wb,rfl,cb⟩ := hb
    apply Lax977378.OrdinaryCalls.untagged A B X E Y F covA covB colour root ends ordinary interior
      K le_rfl _ hx _ hw
    apply Lax977378.LocalCalls.commonCalls s.type.pattern A B {s.type.center} ya zb colour
      (fun _ _ _ => True) K 0 (by simpa using wa) (by simpa using wb) _ _ ⟨_,by simp,rfl⟩
    intro j _ u
    exact ⟨⟨(ca u).trans (cb u).symm,fun p => ((wa.1.2.2 p u).symm.trans (wb.1.2.2 p u))⟩,trivial⟩
  constructor
  · intro x
    by_cases hx : x ∈ X K
    · rw [←markA] at hx
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hx
      exact ⟨_,named m hm⟩
    · obtain ⟨s,hs,ha⟩ := typesA x hx
      obtain ⟨w,hw,hb⟩ := copiesB s hs
      exact ⟨w,pair s x w hx hw ha hb⟩
  · intro w
    by_cases hw : w ∈ Y K
    · rw [←markB] at hw
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hw
      exact ⟨_,named m hm⟩
    · obtain ⟨s,hs,hb⟩ := typesB w hw
      obtain ⟨x,hx,ha⟩ := copiesA s hs
      exact ⟨x,pair s x w hx hw ha hb⟩

end Lax977378Proofs.LocalCover
