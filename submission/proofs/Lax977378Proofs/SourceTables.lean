import Lax977378.SourceTables
import Mathlib.Tactic

namespace Lax977378Proofs.SourceTables
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Blocks Lax977378.SourceRun Lax977378.SourceTables

private theorem readHistory {c} (G : Graph c) (I : Layer G) (a : LinearOrder (Fin G.size))
    (K : Nat) (top : Table G a) (hist : History G I K top.layer) :
    ∃ T : Nat → Table G a, (T 0).layer = I ∧ T K = top ∧ ∀ j < K, Follows j (T j) (T (j+1)) := by
  induction K generalizing top with
  | zero => exact ⟨fun _ => top,hist,rfl,by simp⟩
  | succ j ih =>
    obtain ⟨H,hist,f,l,closure,parent,child⟩ := hist
    have compat : Lax977378.Stage.Compatible a top.layer.row :=
      fun _ _ h => top.part.monotone h
    obtain ⟨P,hr,hf,hl⟩ := parent a compat
    let previous : Table G a := ⟨H.n,P,H.exceptions⟩
    have sameLayer : previous.layer = H := by cases H; simp_all [previous,Table.layer]
    obtain ⟨T,h0,hj,steps⟩ := ih previous (sameLayer.symm ▸ hist)
    let tables := Function.update T (j+1) top
    refine ⟨tables,by simpa [tables] using h0,by simp [tables],?_⟩
    intro k hk
    by_cases eq : k = j
    · subst k
      have next : Follows j previous top := by
        constructor
        · simpa [previous,hf,hl,Table.layer] using closure
        · simpa [previous,hr,Table.layer] using child a compat
      simpa [tables,Function.update_of_ne (show j ≠ j+1 by omega),hj] using next
    · have old := steps k (by omega)
      simpa [tables,Function.update_of_ne (show k ≠ j+1 by omega),
        Function.update_of_ne (show k+1 ≠ j+1 by omega)] using old

/--
---
conclusion: Lax977378.SourceTables.sourceTables
assumptions:
  - Lax977378.Endpoints.admissible
---
Choose endpoints of the final rows and a compatible order. At each previous
level the history supplies a parent partition in this very order, including
its recorded extrema. Induction assembles the complete sequence.
-/
theorem sourceTables {c K} (G : Graph c) (I L : Layer G) (hist : History G I K L)
    (onto : Function.Surjective L.row) :
    ∃ (a : LinearOrder (Fin G.size)) (T : Nat → Table G a),
      (T 0).layer = I ∧ (T K).layer = L ∧ ∀ j < K, Follows j (T j) (T (j+1)) := by
  classical
  let S t := Finset.univ.filter (fun x => L.row x = t)
  have nonempty t : (S t).Nonempty := by
    obtain ⟨x,h⟩ := onto t
    exact ⟨x,by simp [S,h]⟩
  obtain ⟨a,P,hr,_,_⟩ := Lax977378.Endpoints.admissible L.row
    (fun t => (S t).min' (nonempty t)) (fun t => (S t).max' (nonempty t))
    (fun t => (Finset.mem_filter.mp ((S t).min'_mem _)).2)
    (fun t => (Finset.mem_filter.mp ((S t).max'_mem _)).2)
    (by
      intro t eq x hx
      have mem : x ∈ S t := by simp [S,hx]
      exact le_antisymm (eq ▸ (S t).le_max' x mem) ((S t).min'_le x mem))
  let top : Table G a := ⟨L.n,P,L.exceptions⟩
  have he : top.layer = L := by cases L; simp_all [top,Table.layer]
  obtain ⟨T,hi,ht,steps⟩ := readHistory G I a K top (he.symm ▸ hist)
  exact ⟨a,T,hi,ht ▸ he,steps⟩

end Lax977378Proofs.SourceTables
