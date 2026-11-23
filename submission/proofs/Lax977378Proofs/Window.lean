import Lax977378.Window
import Mathlib.Tactic

namespace Lax977378Proofs.Window
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests

theorem grow {c : Nat} {G : Graph c} {r s : Nat} {x y : Fin G.size}
    (h : within G r x y) (hrs : r ≤ s) : within G s x y := by
  induction s, hrs using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact Or.inl ih

theorem join {c : Nat} {G : Graph c} {r s : Nat} {x y z : Fin G.size}
    (h : within G r x y) (k : within G s y z) : within G (r+s) x z := by
  induction s generalizing z with
  | zero => exact (show y = z from k) ▸ h
  | succ s ih =>
    rcases k with k | ⟨v,hv,he⟩
    · exact Or.inl (ih k)
    · exact Or.inr ⟨v,ih hv,he⟩

theorem mapWithin {c : Nat} {W G : Graph c} {y : Fin W.size → Fin G.size}
    (dia : Diagram W G y) {r : Nat} {u v : Fin W.size}
    (h : within W r u v) : within G r (y u) (y v) := by
  induction r generalizing v with
  | zero => exact congrArg y h
  | succ r ih =>
    rcases h with h | ⟨z,hz,he⟩
    · exact Or.inl (ih h)
    · exact Or.inr ⟨y z,ih hz,(dia.2.1 _ _).mp he⟩

/--
---
conclusion: Lax977378.Window.exactBall
---
For the reverse passage from the ambient graph, lift the path one edge at a
time. Each next vertex is still within the radius covered by the window, so
it has a name there. The induced diagram reflects the final edge.
-/
theorem exactBall {c ρ p : Nat} {W G : Graph c} {mark : Finset (Fin W.size)}
    {y : Fin W.size → Fin G.size} (hw : Lax977378.RecordTests.Window W G (ρ+p) mark y)
    {u : Fin W.size} (near : ∃ m ∈ mark, within W ρ m u)
    (r : Nat) (hr : r ≤ p) (z : Fin G.size) :
    within G r (y u) z ↔ ∃ v, within W r u v ∧ y v = z := by
  constructor
  · intro h
    obtain ⟨m,hm,hu⟩ := near
    induction r generalizing z with
    | zero => exact ⟨u,rfl,h⟩
    | succ r ih =>
      rcases h with h | ⟨v,hv,he⟩
      · obtain ⟨w,hw',hy⟩ := ih (by omega) z h
        exact ⟨w,Or.inl hw',hy⟩
      · obtain ⟨w,hw',rfl⟩ := ih (by omega) v hv
        have hz : within G (ρ + (r+1)) (y m) z :=
          join (mapWithin hw.1 hu) (Or.inr ⟨y w,hv,he⟩ : within G (r+1) (y u) z)
        obtain ⟨v,rfl⟩ := (hw.2 z).mpr ⟨m,hm,grow hz (by omega)⟩
        exact ⟨v,Or.inr ⟨w,hw',(hw.1.2.1 _ _).mpr he⟩,rfl⟩
  · rintro ⟨v,hv,rfl⟩
    exact mapWithin hw.1 hv

end Lax977378Proofs.Window
