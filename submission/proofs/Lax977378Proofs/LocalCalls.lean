import Lax977378.LocalCalls
import Lax977378Proofs.Window

namespace Lax977378Proofs.LocalCalls
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests Lax977378.TagSafety Lax977378.LocalCalls

/--
---
conclusion: Lax977378.LocalCalls.commonCalls
assumptions:
  - Lax977378.WindowMap.matchBall
---
Upon descending to a named vertex in the inspected ball, increase the allowed
distance from the marked set by the current rank. The radius left in the
window is precisely the radius for the child call.
-/
theorem commonCalls {c} (W A B : Graph c) (mark : Finset (Fin W.size))
    (y : Fin W.size → Fin A.size) (z : Fin W.size → Fin B.size)
    (root ends : Nat → Fin A.size → Fin B.size → Prop) (i s : Nat)
    (wy : Window W A (s+radius i) mark y) (wz : Window W B (s+radius i) mark z)
    (data : ∀ j ≤ i, ∀ u, root j (y u) (z u) ∧ ends j (y u) (z u))
    (u : Fin W.size) (near : ∃ m ∈ mark, within W s m u) :
    Calls A B root ends i (y u) (z u) := by
  induction i generalizing s u with
  | zero => exact (data 0 le_rfl u).1
  | succ i ih =>
    have hrad : i+1 ≤ radius (i+1) := by simp [radius]
    obtain ⟨h,hn,hv,he⟩ := Lax977378.WindowMap.matchBall W A B mark y z wy wz u near hrad
    refine ⟨(data _ le_rfl _).1,h,fun v => hn v u,he,?_⟩
    intro v
    obtain ⟨j,hj,hy,hz⟩ := hv v
    rw [hy,hz]
    refine ⟨(data _ le_rfl _).2,?_⟩
    have eq : (s + (i+1)) + radius i = s + radius (i+1) := by simp [radius]; omega
    apply ih (s + (i+1)) (eq.symm ▸ wy) (eq.symm ▸ wz)
      (fun k hk => data k (hk.trans (Nat.le_succ _))) j
    obtain ⟨m,hm,hu⟩ := near
    exact ⟨m,hm,Lax977378Proofs.Window.join hu hj⟩

/--
---
conclusion: Lax977378.LocalCalls.innerCalls
assumptions:
  - Lax977378.WindowMap.matchBall
---
The outer slack ensures ambient distances are read exactly. Only inner
vertex data are consulted. At a recursive call the increased distance
allowance exactly offsets the reduction of the remaining inspection radius.
-/
theorem innerCalls {c} (W A B : Graph c) (mark : Finset (Fin W.size))
    (y : Fin W.size → Fin A.size) (z : Fin W.size → Fin B.size)
    (root ends : Nat → Fin A.size → Fin B.size → Prop) (i s slack : Nat)
    (wy : Window W A (s+radius i+slack) mark y) (wz : Window W B (s+radius i+slack) mark z)
    (data : ∀ j ≤ i, ∀ u, (∃ m ∈ mark, within W (s+radius i) m u) →
      root j (y u) (z u) ∧ ends j (y u) (z u))
    (u : Fin W.size) (near : ∃ m ∈ mark, within W s m u) :
    Calls A B root ends i (y u) (z u) := by
  induction i generalizing s u with
  | zero => exact (data 0 le_rfl u (by simpa [radius] using near)).1
  | succ i ih =>
    have w (G : Graph c) (y' : Fin W.size → Fin G.size) (h : Window W G (s+radius (i+1)+slack) mark y') :
        Window W G (s+(radius (i+1)+slack)) mark y' := by simpa [Nat.add_assoc] using h
    have hrad : i+1 ≤ radius (i+1)+slack := by simp [radius]; omega
    obtain ⟨h,hn,hv,he⟩ := Lax977378.WindowMap.matchBall W A B mark y z (w _ _ wy) (w _ _ wz) u near hrad
    obtain ⟨m,hm,hu⟩ := near
    refine ⟨(data _ le_rfl u ⟨m,hm,Window.grow hu (by omega)⟩).1,h,fun v => hn v u,he,?_⟩
    intro v
    obtain ⟨j,hj,hy,hz⟩ := hv v
    rw [hy,hz]
    have dist := Window.join hu hj
    have eq : (s + (i+1)) + radius i = s + radius (i+1) := by simp [radius]; omega
    have dist' : within W (s+radius (i+1)) m j := Window.grow dist (by rw [←eq]; omega)
    refine ⟨(data _ le_rfl _ ⟨m,hm,dist'⟩).2,?_⟩
    apply ih (s+(i+1)) (by simpa [eq] using wy) (by simpa [eq] using wz) _ j ⟨m,hm,dist⟩
    intro k hk w hn
    exact data k (by omega) w (by simpa [eq] using hn)

end Lax977378Proofs.LocalCalls
