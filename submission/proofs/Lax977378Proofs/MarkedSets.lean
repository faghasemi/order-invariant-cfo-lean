import Lax977378.MarkedSets
import Lax977378Proofs.Window

namespace Lax977378Proofs.MarkedSets
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests Lax977378.OrdinaryCalls
open Lax977378.TagSafety Lax977378.MarkedSets

theorem memMoved {c} {W A B : Graph c} (y : Fin W.size → Fin A.size)
    (z : Fin W.size → Fin B.size) (S : Finset (Fin A.size)) (u : Fin B.size) :
    u ∈ moved y z S ↔ ∃ j, y j ∈ S ∧ z j = u := by classical simp [moved]

/--
---
conclusion: Lax977378.MarkedSets.moveStages
assumptions:
  - Lax977378.Window.exactBall
---
Start at the common name of the exceptional vertex or endpoint. Lift the
target path, map it to the source, and apply the source covering condition.
-/
theorem moveStages {c K R} (W A B : Graph c) (mark : Finset (Fin W.size))
    (y : Fin W.size → Fin A.size) (z : Fin W.size → Fin B.size)
    (wy : Window W A R mark y) (wz : Window W B R mark z)
    (X E : Nat → Finset (Fin A.size)) (covers : Covers A K X E)
    (named : ∀ j < K, X j ∪ E (j+1) ⊆ mark.image y)
    (size : ∀ j < K, radius (j+1) ≤ R) :
    Covers B K (fun j => moved y z (X j)) (fun j => moved y z (E j)) := by
  intro j hj v hv x hx
  have start : ∃ w, y w ∈ X j ∪ E (j+1) ∧ z w = v := by
    rcases Finset.mem_union.mp hv with he | he
    · obtain ⟨w,hw,h⟩ := (memMoved ..).mp he
      exact ⟨w,Finset.mem_union_left _ hw,h⟩
    · obtain ⟨w,hw,h⟩ := (memMoved ..).mp he
      exact ⟨w,Finset.mem_union_right _ hw,h⟩
  obtain ⟨w,hs,rfl⟩ := start
  obtain ⟨m,hm,eq⟩ := Finset.mem_image.mp (named j hj hs)
  have marked : w ∈ mark := (wy.1.1 eq) ▸ hm
  have win : Window W B (0+R) mark z := by simpa using wz
  obtain ⟨u,dist,zu⟩ := (Lax977378.Window.exactBall (ρ := 0) win
    ⟨w,marked,(rfl : within W 0 w w)⟩ _ (size _ hj) _).mp hx
  exact (memMoved ..).mpr ⟨u,covers j hj _ hs _ (Window.mapWithin wy.1 dist),zu⟩

end Lax977378Proofs.MarkedSets
