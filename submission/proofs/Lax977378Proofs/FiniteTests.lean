import Lax977378.FiniteTests
import Mathlib.Tactic

namespace Lax977378Proofs.FiniteTests
open Lax977378.Logic Lax977378.RecordTests

private abbrev WindowCode (c U : Nat) := (k : Fin (U+1)) ×
  (Fin k.val → Fin k.val → Prop) × (Fin c → Fin k.val → Prop) ×
  Finset (Fin k.val) × Finset (Fin k.val)

private def windowGraph {c U} (w : WindowCode c U) : Graph c where
  size := w.1.val
  edge := fun x y => x ≠ y ∧ w.2.1 x y ∧ w.2.1 y x
  symm := fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩
  loopless := fun _ h => h.1 rfl
  pred := w.2.2.1

/--
---
conclusion: Lax977378.FiniteTests.finiteTests
assumptions:
  - Lax977378.RecordTests.recordTest
---
Enumerate the two relation tables and both marked subsets on each possible
window size, the capped vector and the subset of frequent indices.
-/
theorem finiteTests {c n} (types : Fin n → Pointed c) (r R cap U : Nat) :
    ∃ tests : List (TestData c × Formula c),
      (∀ e ∈ tests, Plain [] e.2 ∧ ∀ G, Unordered G e.2 ↔ Passes e.1 G) ∧
      ∀ D : TestData c, D.radius = r → D.windowRadius = R → D.cap = cap →
        D.windowGraph.size ≤ U → ∀ (v : Fin n → Fin (cap+1)) (t : Nat),
        D.counts = List.ofFn (fun j => (types j,(v j).val)) →
        D.frequent = ((List.finRange n).filter (fun j => t ≤ (v j).val)).map types →
        ∃ f, (D,f) ∈ tests := by
  classical
  let Code := WindowCode c U × (Fin n → Fin (cap+1)) × Finset (Fin n)
  let decode (z : Code) : TestData c :=
    ⟨r,R,windowGraph z.1,z.1.2.2.2.1,z.1.2.2.2.2,cap,
      List.ofFn (fun j => (types j,(z.2.1 j).val)),
      ((List.finRange n).filter (fun j => j ∈ z.2.2)).map types⟩
  choose sentence good using (fun D : TestData c => Lax977378.RecordTests.recordTest D)
  let entry (z : Code) := (decode z,sentence (decode z))
  refine ⟨(Finset.univ : Finset Code).toList.map entry,?_,?_⟩
  · intro e he
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp he
    exact good _
  · rintro ⟨_,_,⟨k,ed,symm,loop,pred⟩,M,Z,_,_,_⟩ hr hR hc hk v t hcnt hfreq
    dsimp at hr hR hc hk hcnt hfreq
    subst_vars
    let w : WindowCode c U := ⟨⟨k,Nat.lt_succ_of_le hk⟩,ed,pred,M,Z⟩
    let z : Code := (w,v,Finset.univ.filter (fun j => t ≤ (v j).val))
    refine ⟨sentence (decode z),List.mem_map.mpr ⟨z,by simp,?_⟩⟩
    have edge : (fun x y => x ≠ y ∧ ed x y ∧ ed y x) = ed := by
      funext x y; apply propext
      exact ⟨fun h => h.2.1,fun h => ⟨fun eq => loop _ (eq ▸ h),h,symm _ _ h⟩⟩
    simp [entry,decode,z,w,windowGraph,edge]

end Lax977378Proofs.FiniteTests
