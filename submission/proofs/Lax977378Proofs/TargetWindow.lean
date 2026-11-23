import Lax977378.TargetWindow
import Mathlib.Tactic

namespace Lax977378Proofs.TargetWindow
open Lax977378.Logic Lax977378.RecordTests Lax977378.CountParameters

private noncomputable def number {n m} (M : Finset (Fin n)) (y : Fin n → Fin m) (inj : Function.Injective y) :
    M ≃ (M.image y) :=
  Equiv.ofBijective (fun i => ⟨y i.val,Finset.mem_image_of_mem _ i.property⟩)
    ⟨fun _ _ eq => Subtype.ext (inj (congrArg Subtype.val eq)),by
      intro u
      obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp u.property
      exact ⟨⟨i,hi⟩,Subtype.ext eq⟩⟩

/--
---
conclusion: Lax977378.TargetWindow.targetWindow
assumptions:
  - Lax977378.CountParameters.countTestValue
---
Read each capped count from its conjunct. Both marked sets have an injective
enumeration by the same window names.
-/
theorem targetWindow {c n} (A B : Graph c) (D : TestData c) (types : Fin n → Pointed c)
    (v : Fin n → Nat) (t : Nat) (tcap : t ≤ D.cap)
    (counts : D.counts = List.ofFn (fun j => (types j,v j)))
    (freq : D.frequent = ((List.finRange n).filter (fun j => t ≤ v j)).map types)
    (y : Fin D.windowGraph.size → Fin A.size) (wy : Window D.windowGraph A D.windowRadius D.marked y)
    (pass : Passes D B) :
    (∀ j, v j = min D.cap (locations (types j) D.radius B).card) ∧
    (∀ j, t ≤ v j ↔ t ≤ (locations (types j) D.radius B).card) ∧
    ∃ z, Window D.windowGraph B D.windowRadius D.marked z ∧
      D.rare.image z = rareSet types D.radius B v t ∧
      ∃ e : (D.marked.image z) ≃ (D.marked.image y),
        ∀ j (hj : j ∈ D.marked), (e ⟨z j, Finset.mem_image_of_mem _ hj⟩).val = y j
 := by
  classical
  obtain ⟨hc,z,wz,hz⟩ := pass
  have eq (j) : v j = min D.cap (locations (types j) D.radius B).card := by
    apply (Lax977378.CountParameters.countTestValue ..).mp
    apply hc (types j,v j)
    rw [counts]; exact List.mem_ofFn.mpr ⟨j,rfl⟩
  refine ⟨eq,fun j => by rw [eq]; omega,z,wz,?_,?_⟩
  · ext x
    rw [Finset.mem_image,hz]
    simp [rareSet,freq]
  · let e := (number D.marked z wz.1.1).symm.trans (number D.marked y wy.1.1)
    refine ⟨e,?_⟩
    intro j hj
    let u : D.marked := ⟨j,hj⟩
    change ((number D.marked y wy.1.1) ((number D.marked z wz.1.1).symm
      ((number D.marked z wz.1.1) u))).val = _
    rw [Equiv.symm_apply_apply]
    rfl

end Lax977378Proofs.TargetWindow
