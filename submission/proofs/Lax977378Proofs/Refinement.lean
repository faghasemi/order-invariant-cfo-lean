import Lax977378.Refinement
import Mathlib.Tactic
namespace Lax977378Proofs.Refinement
open Lax977378.Logic Lax977378.Blocks Lax977378.OuterContexts

section Tables
variable {V W I U : Type} [LinearOrder V] [LinearOrder W] [LinearOrder I]
    (P : Partition V I) (Q : Partition W I) (left : U → V) (right : U → W)
    (unique : Function.Injective (P.block ∘ left))
    (blocks : ∀ u, P.block (left u) = Q.block (right u))

private theorem byBlock {x y : V} (h : P.block x < P.block y) : x < y :=
  lt_of_not_ge (fun hy => (not_le_of_gt h) (P.monotone hy))

include blocks in
private theorem orderByRow {z : V} {t : W} (hz : P.block z = Q.block t) (u : U)
    (diff : P.block z ≠ P.block (left u)) :
    (z < left u ↔ t < right u) ∧ (left u < z ↔ right u < t) := by
  rcases lt_or_gt_of_ne diff with h | h
  · have l := byBlock P h
    have r := byBlock Q (hz ▸ blocks u ▸ h)
    simp [l,r,not_lt_of_gt l,not_lt_of_gt r]
  · have l := byBlock P h
    have r := byBlock Q (hz ▸ blocks u ▸ h)
    simp [l,r,not_lt_of_gt l,not_lt_of_gt r]

include unique blocks in
private theorem corresponding (first : ∀ u, left u = P.first (P.block (left u)) ↔
      right u = Q.first (Q.block (right u)))
    (last : ∀ u, left u = P.last (P.block (left u)) ↔
      right u = Q.last (Q.block (right u))) (z : V) :
    ∃ t, P.block z = Q.block t ∧ ∀ u,
      (z < left u ↔ t < right u) ∧ (left u < z ↔ right u < t) := by
  classical
  by_cases existsRow : ∃ k, P.block z = P.block (left k)
  · obtain ⟨k,hk⟩ := existsRow
    have finish (t : W) (ht : Q.block t = P.block z)
        (hp : (z < left k ↔ t < right k) ∧ (left k < z ↔ right k < t)) :
        ∀ u, (z < left u ↔ t < right u) ∧ (left u < z ↔ right u < t) := by
      intro u
      by_cases h : k = u
      · exact h ▸ hp
      · apply orderByRow P Q left right blocks ht.symm u
        exact fun he => h (unique (hk.symm.trans he))
    rcases lt_trichotomy z (left k) with h | h | h
    · let t := Q.first (Q.block (right k))
      have ht : Q.block t = P.block z := (Q.first_mem _).trans ((blocks k).symm.trans hk.symm)
      have hn : left k ≠ P.first (P.block (left k)) := by
        have le := P.first_le z; rw [hk] at le; exact (le.trans_lt h).ne'
      have hr : t < right k := lt_of_le_of_ne (Q.first_le _) (fun e => hn ((first k).mpr e.symm))
      exact ⟨t,ht.symm,finish t ht (by simp [h,hr,not_lt_of_gt h,not_lt_of_gt hr])⟩
    · exact ⟨right k, hk.trans (blocks k), finish _ (hk.trans (blocks k)).symm (by simp [h])⟩
    · let t := Q.last (Q.block (right k))
      have ht : Q.block t = P.block z := (Q.last_mem _).trans ((blocks k).symm.trans hk.symm)
      have hn : left k ≠ P.last (P.block (left k)) := by
        have le := P.le_last z; rw [hk] at le; exact (h.trans_le le).ne
      have hr : right k < t := lt_of_le_of_ne (Q.le_last _) (fun e => hn ((last k).mpr e))
      exact ⟨t,ht.symm,finish t ht (by simp [h,hr,not_lt_of_gt h,not_lt_of_gt hr])⟩
  · let t := Q.first (P.block z)
    have ht : P.block z = Q.block t := (Q.first_mem _).symm
    exact ⟨t,ht,fun k => orderByRow P Q left right blocks ht k (fun h => existsRow ⟨k,h⟩)⟩

end Tables

/--
---
conclusion: Lax977378.Refinement.levelStep
---
Transfer each interval witness in its own block. If that block also contains
a ball vertex, choose the corresponding vertex, first vertex or last vertex,
according to the side on which the witness must lie. Every other comparison
is fixed by the common order of the block indices.
-/
theorem levelStep {c n i : Nat} (A B : Graph c)
    (a : LinearOrder (Fin A.size)) (b : LinearOrder (Fin B.size))
    (P : @Partition (Fin A.size) (Fin n) a inferInstance)
    (Q : @Partition (Fin B.size) (Fin n) b inferInstance)
    (lower : ∀ x y, P.block x = Q.block y → same A B a b i x y)
    (x : Fin A.size) (y : Fin B.size) (h : Ball A (i+1) x ≃ Ball B (i+1) y)
    (center : ∀ u, u.val = x ↔ (h u).val = y)
    (edges : ∀ u v, A.edge u.val v.val ↔ B.edge (h u).val (h v).val)
    (unique : Function.Injective (fun u : Ball A (i+1) x => P.block u.val))
    (blocks : ∀ u, P.block u.val = Q.block (h u).val)
    (first : ∀ u, u.val = P.first (P.block u.val) ↔ (h u).val = Q.first (Q.block (h u).val))
    (last : ∀ u, u.val = P.last (P.block u.val) ↔ (h u).val = Q.last (Q.block (h u).val)) :
    same A B a b (i+1) x y := by
  let := a
  let := b
  let l (u : Ball A (i+1) x) := u.val
  let r (u : Ball A (i+1) x) := (h u).val
  have ub : Function.Injective (Q.block ∘ r) := by
    intro u v he; exact unique ((blocks u).trans (he.trans (blocks v).symm))
  refine ⟨h,center,edges,?_,fun u => lower _ _ (blocks u),?_,?_⟩
  · intro u v
    by_cases he : u = v
    · subst v; exact iff_of_false (@lt_irrefl _ a.toPreorder _) (@lt_irrefl _ b.toPreorder _)
    · exact (orderByRow P Q l r blocks (blocks u) v (fun e => he (unique e))).1
  · intro z
    obtain ⟨t,ht,pr⟩ := corresponding P Q l r unique blocks first last z
    exact ⟨t,lower _ _ ht,pr⟩
  · intro t
    obtain ⟨z,hz,pr⟩ := corresponding Q P r l ub (fun u => (blocks u).symm)
      (fun u => (first u).symm) (fun u => (last u).symm) t
    exact ⟨z,lower _ _ hz.symm,fun u => ⟨(pr u).1.symm,(pr u).2.symm⟩⟩

end Lax977378Proofs.Refinement
