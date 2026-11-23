import Lax977378.Types
import Mathlib.Tactic

namespace Lax977378Proofs.Types
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests

private def Equivalent {c} (r : Nat) (s t : Pointed c) : Prop :=
  ∀ (G : Graph c) x, Occurs s r G x ↔ Occurs t r G x

private theorem commonRoot {c r} {s t : Pointed c} {A : Graph c} {x}
    (hs : Occurs s r A x) (ht : Occurs t r A x) : Equivalent r s t := by
  classical
  obtain ⟨u,⟨du,wu⟩,hu⟩ := hs
  obtain ⟨v,⟨dv,wv⟩,hv⟩ := ht
  have ran : Set.range u = Set.range v := by
    ext z
    change (∃ a, u a = z) ↔ ∃ b, v b = z
    rw [wu,wv]
    simp [hu,hv]
  let e := ((Equiv.ofInjective u du.1).trans (Equiv.setCongr ran)).trans (Equiv.ofInjective v dv.1).symm
  have comm (i) : v (e i) = u i := by
    exact congrArg Subtype.val ((Equiv.ofInjective v dv.1).apply_symm_apply _)
  have root : e s.center = t.center := dv.1 ((comm _).trans (hu.trans hv.symm))
  have transfer {s' t' : Pointed c} (e' : Fin s'.pattern.size ≃ Fin t'.pattern.size)
      (rt : e' s'.center = t'.center) (ed : ∀ a b, s'.pattern.edge a b ↔ t'.pattern.edge (e' a) (e' b))
      (pr : ∀ p a, s'.pattern.pred p a ↔ t'.pattern.pred p (e' a))
      {G : Graph c} {z} (h : Occurs t' r G z) : Occurs s' r G z := by
    obtain ⟨w,⟨dw,ww⟩,hw⟩ := h
    refine ⟨w ∘ e',⟨⟨dw.1.comp e'.injective,
      fun i j => (ed i j).trans (dw.2.1 _ _), fun p i => (pr p i).trans (dw.2.2 _ _)⟩,?_⟩,?_⟩
    · intro z'
      change (∃ i, w (e' i) = z') ↔ _
      calc
        _ ↔ ∃ j, w j = z' := ⟨fun ⟨i,h⟩ => ⟨_,h⟩, fun ⟨j,h⟩ => ⟨e'.symm j, by simpa using h⟩⟩
        _ ↔ _ := by simpa [Function.comp_def,rt] using ww z'
    · simpa [Function.comp_def,rt] using hw
  have ed a b : s.pattern.edge a b ↔ t.pattern.edge (e a) (e b) := by
    rw [du.2.1, dv.2.1,comm,comm]
  have pr p a : s.pattern.pred p a ↔ t.pattern.pred p (e a) := by
    rw [du.2.2, dv.2.2,comm]
  intro G z
  exact ⟨transfer e.symm (by simp [← root])
    (fun a b => by simpa using (ed (e.symm a) (e.symm b)).symm)
    (fun p a => by simpa using (pr p (e.symm a)).symm),transfer e root ed pr⟩

-- Collapse the finite list by semantic equivalence. The common-root lemma
-- makes the cells of unequal representatives disjoint on every graph.
private theorem representatives {c} (r : Nat) (ts : List (Pointed c)) :
    ∃ n : Nat, ∃ t : Fin n → Pointed c,
      (∀ u ∈ ts, ∃ j, Equivalent r u (t j)) ∧
      (∀ i j, Equivalent r (t i) (t j) → i = j) := by
  classical
  induction ts with
  | nil => exact ⟨0,Fin.elim0,by simp,fun i => i.elim0⟩
  | cons u us ih =>
    obtain ⟨n,t,cover,unique⟩ := ih
    by_cases found : ∃ j, Equivalent r u (t j)
    · exact ⟨n,t,fun v hv => (List.mem_cons.mp hv).elim (fun h => h ▸ found) (cover v),unique⟩
    · refine ⟨n+1,Fin.cases u t,?_,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨0, fun _ _ => Iff.rfl⟩
        · obtain ⟨j,hj⟩ := cover v hv
          exact ⟨j.succ,hj⟩
      · intro i j
        refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
        · exact fun _ => rfl
        · exact fun h => False.elim (found ⟨_,h⟩)
        · exact fun h => False.elim (found ⟨_,fun G x => (h G x).symm⟩)
        · exact fun h => congrArg Fin.succ (unique a b h)

/--
---
conclusion: Lax977378.Types.uniqueTypes
assumptions:
  - Lax977378.Catalogue.catalogue
---
Two patterns occurring at the same vertex have numberings onto the same
ambient ball. Their root-preserving change of numbering transports an
occurrence on any graph. Retaining one representative of each such class
therefore partitions the vertices of every bounded-degree graph.
-/
theorem uniqueTypes (c d r : Nat) :
    ∃ n : Nat, ∃ t : Fin n → Pointed c,
      ∀ G : Graph c, G.Bounded d → ∀ x, ∃! j, Occurs (t j) r G x := by
  obtain ⟨ts,all⟩ := Lax977378.Catalogue.catalogue c d r
  obtain ⟨n,t,cover,unique⟩ := representatives r ts
  refine ⟨n,t,?_⟩
  intro G hd x
  obtain ⟨s,hs,hx⟩ := all G hd x
  obtain ⟨j,hj⟩ := cover s hs
  have h := (hj G x).mp hx
  exact ⟨j,h,fun k hk => unique k j (commonRoot hk h)⟩

end Lax977378Proofs.Types
