import Lax977378.CallAgreement
import Lax977378Proofs.Catalogue

namespace Lax977378Proofs.CallAgreement
open Lax977378.Logic Lax977378.OuterContexts Lax977378.LocalCalls Lax977378.CallAgreement

/--
---
conclusion: Lax977378.CallAgreement.compareReps
---
Compose the first ball map with the inverse of the second. Lower calls at
corresponding ball vertices compare through their common target vertex.
-/
theorem compareReps {c} (A B : Graph c) (ra ea : Nat → Fin A.size → Nat)
    (rb eb : Nat → Fin B.size → Nat) (i : Nat) (x u : Fin A.size) (y : Fin B.size)
    (hx : agrees A B ra ea rb eb i x y) (hu : agrees A B ra ea rb eb i u y) :
    agrees A A ra ea ra ea i x u := by
  induction i generalizing x u y with
  | zero => exact Eq.trans hx (Eq.symm hu)
  | succ i ih =>
    obtain ⟨r,e,er,ed,ec⟩ := hx
    obtain ⟨s,f,fr,fd,fc⟩ := hu
    let g := e.trans f.symm
    have comm v : f (g v) = e v := f.apply_symm_apply _
    refine ⟨r.trans s.symm,g,?_,?_,?_⟩
    · intro v; exact (er v).trans (by simpa only [comm] using (fr (g v)).symm)
    · intro v w; exact (ed v w).trans (by simpa only [comm] using (fd (g v) (g w)).symm)
    · intro v
      have hh := fc (g v)
      rw [comm] at hh
      exact ⟨(ec v).1.trans hh.1.symm,ih _ _ _ (ec v).2 hh.2⟩

/--
---
conclusion: Lax977378.CallAgreement.lowerRanks
---
The radius ball contains its centre and the rooted map sends it to the
other centre. Its child call reduces the rank while keeping both roots.
-/
theorem lowerRanks {c} (A B : Graph c) (ra ea : Nat → Fin A.size → Nat)
    (rb eb : Nat → Fin B.size → Nat) (i j : Nat) (hj : j ≤ i) (x y)
    (h : agrees A B ra ea rb eb i x y) : agrees A B ra ea rb eb j x y := by
  induction i with
  | zero => cases Nat.le_zero.mp hj; exact h
  | succ i ih =>
    rcases Nat.eq_or_lt_of_le hj with rfl | lt
    · exact h
    · obtain ⟨_,e,root,_,calls⟩ := h
      let v : Ball A (i+1) x := ⟨x,Catalogue.centerWithin ..⟩
      have eq := (root v).mp (show v.val = x from rfl)
      exact ih (by omega) (by simpa only [eq,agrees,v] using (calls v).2)

end Lax977378Proofs.CallAgreement
