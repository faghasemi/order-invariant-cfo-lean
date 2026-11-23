import Lax977378.ColouredTypes
import Lax977378Proofs.Planting

namespace Lax977378Proofs.ColouredTypes
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Planting Lax977378.RecordTests Lax977378.CountParameters

/--
---
conclusion: Lax977378.ColouredTypes.colouredTypes
---
Index requests by a catalogue index and an embedding of its named vertices
into the palette. A realised ball inherits such an embedding since any two
of its vertices have distance at most twice its radius.
-/
theorem colouredTypes {c n} (types : Fin n → Pointed c) (q : Nat) : ∃ H : Nat,
    ∀ (v : Fin n → Nat) (t : Nat), ∃ seeds : List (Request c q), seeds.length ≤ H ∧
      (∀ s ∈ seeds, ∃ j, t ≤ v j ∧ s.type = types j) ∧
      ∀ (G : Graph c) (r : Nat) (κ : Fin G.size → Fin q),
        ProperOn G (r+r) Finset.univ κ → ∀ x, x ∉ rareSet types r G v t →
          ∃ s ∈ seeds, Realised s G r κ x := by
  classical
  let Code := (j : Fin n) × (Fin (types j).pattern.size ↪ Fin q)
  let seed (z : Code) : Request c q := ⟨types z.1,z.2,z.2.injective⟩
  refine ⟨Fintype.card Code,?_⟩
  intro v t
  let codes := (Finset.univ : Finset Code).filter (fun z => t ≤ v z.1)
  refine ⟨codes.toList.map seed,by simp [Finset.card_le_univ],?_,?_⟩
  · intro s hs
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hs
    exact ⟨z.1,(Finset.mem_filter.mp (Finset.mem_toList.mp hz)).2,rfl⟩
  · intro G r κ proper x hx
    obtain ⟨j,hj,y,win,center⟩ : ∃ j, t ≤ v j ∧ Occurs (types j) r G x := by
      simpa [rareSet] using hx
    have inside (u) : within G r x (y u) := by
      have h := (win.2 (y u)).mp ⟨u,rfl⟩
      simpa [center] using h
    let paint : Fin (types j).pattern.size ↪ Fin q := ⟨fun u => κ (y u),by
      intro u w he
      by_contra ne
      exact proper _ (by simp) _ (by simp) (fun h => ne (win.1.1 h))
        (Window.join (Planting.reverseWithin (inside u)) (inside w)) he⟩
    let z : Code := ⟨j,paint⟩
    exact ⟨seed z,List.mem_map.mpr ⟨z,by simp [codes,z,hj],rfl⟩,y,win,center,fun _ => rfl⟩

end Lax977378Proofs.ColouredTypes
