import Lax977378.ColouredRun
import Lax977378Proofs.Planting

namespace Lax977378Proofs.ColouredRun
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Planting Lax977378.SourceRun Lax977378.Stage

/--
---
conclusion: Lax977378.ColouredRun.colouredRun
assumptions:
  - Lax977378.SourceRun.construct
---
Number the realised initial names. An equal name on two vertices of a
K-ball gives equal auxiliary colours, while the path through the centre
has length at most 2K. Proper colouring forces the vertices to coincide.
-/
theorem colouredRun (c d K : Nat) : ∃ N : Nat → Nat, ∀ (G : Graph c), G.Bounded d →
    ∀ (q : Nat) (κ : Fin G.size → Fin q), ProperOn G (K+K) Finset.univ κ →
    ∀ Z : Finset (Fin G.size), ∃ I L : Layer G,
      I.exceptions = Z ∧
      (∀ x y, I.row x = I.row y ↔ x = y ∨
        x ∉ Z ∧ y ∉ Z ∧ κ x = κ y ∧ ∀ p, G.pred p x ↔ G.pred p y) ∧
      History G I K L ∧ Stable G K L.row ∧ Function.Surjective L.row ∧
      L.n ≤ limit d N (Z.card + 2^c*q) K ∧ L.exceptions.card ≤ limit d N (Z.card + 2^c*q) K := by
  classical
  obtain ⟨N,run⟩ := Lax977378.SourceRun.construct c d K
  refine ⟨N,?_⟩
  intro G hd q κ proper Z
  let Name := Sum (↥Z) ((Fin c → Bool) × Fin q)
  let name (x : Fin G.size) : Name := if hx : x ∈ Z then .inl ⟨x,hx⟩
    else .inr (fun p => decide (G.pred p x),κ x)
  let S := Finset.univ.image name
  let row (x : Fin G.size) := S.equivFin ⟨name x,Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩
  have eqRows (x y) : row x = row y ↔ x = y ∨
      x ∉ Z ∧ y ∉ Z ∧ κ x = κ y ∧ ∀ p, G.pred p x ↔ G.pred p y := by
    have base : row x = row y ↔ name x = name y :=
      ⟨fun h => congrArg Subtype.val (S.equivFin.injective h), fun h => congrArg S.equivFin (Subtype.ext h)⟩
    rw [base]
    by_cases hx : x ∈ Z <;> by_cases hy : y ∈ Z
    · simp [name,Name,hx,hy]
    · have ne : x ≠ y := fun e => hy (e ▸ hx)
      simp [name,hx,hy,ne]
    · have ne : x ≠ y := fun e => hx (e ▸ hy)
      simp [name,hx,hy,ne]
    · constructor
      · intro eq
        have h : ((fun p => decide (G.pred p x)),κ x) = ((fun p => decide (G.pred p y)),κ y) := by
          dsimp only [name] at eq
          rw [dif_neg hx,dif_neg hy] at eq
          exact Sum.inr.inj eq
        exact Or.inr ⟨hx,hy,congrArg Prod.snd h,fun p => by
          simpa using congrFun (congrArg Prod.fst h) p⟩
      · rintro (rfl | ⟨_,_,e,h⟩)
        · rfl
        · dsimp only [name]; rw [dif_neg hx,dif_neg hy]
          congr 2
          · funext p; exact decide_eq_decide.mpr (h p)
  let I : Layer G := ⟨S.card,row,Z⟩
  have bound : S.card ≤ Z.card + 2^c*q := by
    simpa [Name] using (Finset.card_le_univ S)
  have hits : Function.Surjective row := by
    intro j
    obtain ⟨x,_,h⟩ := Finset.mem_image.mp (S.equivFin.symm j).property
    have e : (⟨name x,Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩ : S) = S.equivFin.symm j :=
      Subtype.ext h
    exact ⟨x,by simp [row,e]⟩
  have stable : Stable G 0 row := by
    intro a b _ _ x y eq
    rcases (eqRows x y).mp eq with rfl | ⟨_,_,_,h⟩
    · exact fun _ => Iff.rfl
    · exact h
  have sep (x) : Function.Injective (fun u : Ball G K x => row u.val) := by
    intro u v eq
    apply Subtype.ext
    rcases (eqRows _ _).mp eq with h | ⟨_,_,col,_⟩
    · exact h
    · by_contra ne
      exact proper _ (by simp) _ (by simp) ne
        (Window.join (Planting.reverseWithin u.property) v.property) col
  obtain ⟨L,hist,st,sur,n,m⟩ := run G hd I _ bound (Nat.le_add_right _ _) hits stable sep
  exact ⟨I,L,rfl,eqRows,hist,st,sur,n,m⟩

end Lax977378Proofs.ColouredRun
