import Lax977378.Stage
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

namespace Lax977378Proofs.Stage
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Blocks Lax977378.Stage

private theorem force {v m} {a : LinearOrder (Fin v)} {b : Fin v → Fin m}
    (compat : Compatible a b) {x y} (lt : b x < b y) : a.le x y := by
  rcases @le_total _ a x y with h | h
  · exact h
  · exact False.elim (lt.not_ge (compat _ _ h))

/--
---
conclusion: Lax977378.Stage.refineBlocks
assumptions:
  - Lax977378.Endpoints.admissible
  - Lax977378.ContextLabels.finiteLabels
  - Lax977378.Refinement.levelStep
---
Compute ordinary labels in one order with the chosen endpoints. Number the
realised child keys in increasing order. Every order respecting those keys
preserves the parent endpoints, so the preceding table computes the same
outer label at each vertex in every compatible order.
-/
theorem refineBlocks (c d i : Nat) : ∃ N : Nat, ∀ {n : Nat} (G : Graph c), G.Bounded d →
    ∀ (block : Fin G.size → Fin n) (first last : Fin n → Fin G.size),
    (∀ j, block (first j) = j) → (∀ j, block (last j) = j) →
    (∀ j, first j = last j → ∀ x, block x = j → x = first j) →
    ∀ (Γ : Finset (Fin G.size)), (∀ j, first j ∈ Γ ∧ last j ∈ Γ) →
    Stable G i block →
    (∀ x, Function.Injective (fun u : Ball G (i+1) x => block u.val)) →
    ∃ m : Nat, ∃ next : Fin G.size → Fin m, Function.Surjective next ∧
      m ≤ Γ.card + n * N ∧
      Stable G (i+1) next ∧
      (∀ (a : LinearOrder (Fin G.size)), Compatible a next →
        ∃ P : @Partition (Fin G.size) (Fin n) a inferInstance,
          P.block = block ∧ P.first = first ∧ P.last = last) ∧
      (∀ (a : LinearOrder (Fin G.size)), Compatible a next → ∀ x y,
        next x = next y ↔ block x = block y ∧
          (x = y ∨ x ∉ Γ ∧ y ∉ Γ ∧ same G G a a (i+1) x y)) := by
  classical
  obtain ⟨N,label,labels⟩ := Lax977378.ContextLabels.finiteLabels c d (i+1)
  refine ⟨N,?_⟩
  intro n G hd block first last hf hl single Γ ends stable separated
  obtain ⟨ref,P,hP,hF,hL⟩ := Lax977378.Endpoints.admissible block first last hf hl single
  let row (x : Fin G.size) : Nat := if x = first (block x) then 0 else
    if x = last (block x) then 3 else if x ∈ Γ then 1 else 2
  let token (x : Fin G.size) := if x ∈ Γ then x.val else (label G hd ref x).val
  let key (x : Fin G.size) := toLex (block x, toLex (row x,token x))
  let S := Finset.univ.image key
  let num := (S.orderIsoOfFin rfl).symm
  let next (x : Fin G.size) := num ⟨key x,Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩
  have leKey (x y) : next x ≤ next y ↔ key x ≤ key y := num.le_iff_le
  have ltKey (x y) : next x < next y ↔ key x < key y := num.lt_iff_lt
  have eqKey (x y) : next x = next y ↔ key x = key y :=
    ⟨fun e => congrArg Subtype.val (num.injective e),fun e => congrArg num (Subtype.ext e)⟩
  have ord (a) (hc : Compatible a next) : Compatible a block := by
    intro x y h
    rcases Prod.Lex.toLex_le_toLex.mp ((leKey _ _).mp (hc _ _ h)) with h | ⟨h,_⟩
    · exact le_of_lt h
    · exact le_of_eq h
  have par (a : LinearOrder (Fin G.size)) (hc : Compatible a next) :
      ∃ Q : @Partition (Fin G.size) (Fin n) a inferInstance,
        Q.block = block ∧ Q.first = first ∧ Q.last = last := by
    have before (x) : a.le (first (block x)) x := by
      by_cases e : x = first (block x)
      · rw [← e]; exact @le_refl _ a.toPreorder x
      · apply force hc ((ltKey _ _).mpr ?_)
        apply Prod.Lex.toLex_lt_toLex.mpr
        refine Or.inr ⟨hf _, Prod.Lex.toLex_lt_toLex.mpr (Or.inl ?_)⟩
        simp [row,hf,e]
        (repeat' split) <;> decide
    have after (x) : a.le x (last (block x)) := by
      by_cases e : x = last (block x)
      · rw [← e]; exact @le_refl _ a.toPreorder x
      · have ne : last (block x) ≠ first (block x) :=
          fun h => e ((single _ h.symm x rfl).trans h.symm)
        apply force hc ((ltKey _ _).mpr ?_)
        apply Prod.Lex.toLex_lt_toLex.mpr
        refine Or.inr ⟨(hl _).symm, Prod.Lex.toLex_lt_toLex.mpr (Or.inl ?_)⟩
        simp [row,hl,ne,e]
        (repeat' split) <;> decide
    exact ⟨⟨block,fun {x y} => ord a hc x y,first,last,hf,hl,before,after⟩,rfl,rfl,rfl⟩
  have vertex (a) (hc : Compatible a next) (x) : label G hd ref x = label G hd a x := by
    obtain ⟨Q,hQ,hQf,hQl⟩ := par a hc
    apply (labels ..).mpr
    refine Lax977378.Refinement.levelStep G G ref a P Q ?_ x x (Equiv.refl _) ?_ ?_ ?_ ?_ ?_ ?_
    · intro u v h
      apply stable ref a _ (ord a hc) u v (by simpa only [hP,hQ] using h)
      intro z w le; rw [← hP]; exact P.monotone le
    · exact fun _ => Iff.rfl
    · exact fun _ _ => Iff.rfl
    · rw [hP]; exact separated x
    · simp [hP,hQ]
    · simp [hP,hQ,hF,hQf]
    · simp [hP,hQ,hL,hQl]
  have ordinary (x) (hx : x ∉ Γ) : row x = 2 := by
    have nf : x ≠ first (block x) := fun e => hx (e ▸ (ends _).1)
    have nl : x ≠ last (block x) := fun e => hx (e ▸ (ends _).2)
    simp [row,nf,nl,hx]
  have special (x) (hx : x ∈ Γ) : row x ≠ 2 := by
    simp [row,hx]
    (repeat' split) <;> decide
  have eqBlocks (x y) : next x = next y ↔ block x = block y ∧
      (x = y ∨ x ∉ Γ ∧ y ∉ Γ ∧ label G hd ref x = label G hd ref y) := by
    rw [eqKey]
    have keys : key x = key y ↔ block x = block y ∧ row x = row y ∧ token x = token y := by
      simp [key, Prod.ext_iff]
    rw [keys]
    constructor
    · rintro ⟨b,r,t⟩; refine ⟨b,?_⟩
      by_cases hx : x ∈ Γ <;> by_cases hy : y ∈ Γ
      · exact Or.inl (Fin.ext (by simpa [token,hx,hy] using t))
      · exact False.elim (special _ hx (r.trans (ordinary _ hy)))
      · exact False.elim (special _ hy (r.symm.trans (ordinary _ hx)))
      · exact Or.inr ⟨hx,hy,Fin.ext (by simpa [token,hx,hy] using t)⟩
    · rintro ⟨b,e | ⟨hx,hy,labels'⟩⟩
      · cases e; exact ⟨rfl,rfl,rfl⟩
      · exact ⟨b,(ordinary _ hx).trans (ordinary _ hy).symm,by simp [token,hx,hy,labels']⟩
  have onto : Function.Surjective next := by
    intro j
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp (num.symm j).property
    have e : (⟨key x,Finset.mem_image_of_mem _ (Finset.mem_univ x)⟩ : S) = num.symm j :=
      Subtype.ext hx
    exact ⟨x,by simp [next,e]⟩
  have count : S.card ≤ Γ.card + n * N := by
    choose rep hrep using onto
    let code (j : Fin S.card) : Sum (↥Γ) (Fin n × Fin N) :=
      if hg : rep j ∈ Γ then .inl ⟨rep j,hg⟩ else .inr (block (rep j), label G hd ref (rep j))
    have inj : Function.Injective code := by
      intro u v eq
      rw [← hrep u, ← hrep v]
      apply (eqBlocks ..).mpr
      by_cases hu : rep u ∈ Γ <;> by_cases hv : rep v ∈ Γ
      · have e : rep u = rep v := by simpa [code,hu,hv,Prod.mk.injEq] using eq
        exact ⟨congrArg block e,Or.inl e⟩
      · simp [code,hu,hv] at eq
      · simp [code,hu,hv] at eq
      · have e : (block (rep u),label G hd ref (rep u)) = (block (rep v),label G hd ref (rep v)) :=
          by
            dsimp only [code] at eq
            rw [dif_neg hu,dif_neg hv] at eq
            exact Sum.inr.inj eq
        exact ⟨congrArg Prod.fst e,Or.inr ⟨hu,hv,congrArg Prod.snd e⟩⟩
    simpa using Fintype.card_le_of_injective code inj
  refine ⟨S.card,next,onto,count,?_,par,?_⟩
  · intro a b ha hb x y he
    apply (labels ..).mp
    rw [← vertex a ha,← vertex b hb]
    rcases ((eqBlocks ..).mp he).2 with rfl | ⟨_,_,h⟩
    · rfl
    · exact h
  · intro a hc x y
    rw [eqBlocks,← labels G G hd hd a a x y,← vertex a hc,← vertex a hc]

end Lax977378Proofs.Stage
