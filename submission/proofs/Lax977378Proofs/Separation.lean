import Lax977378.Separation
import Mathlib.Tactic

namespace Lax977378Proofs

/--
---
conclusion: Lax977378.Separation.separated
---
The union of the previously forbidden vertices and one new forbidden ball
costs at most $H$ extra vertices. The induction therefore has enough space for
all the remaining requests.
-/
theorem separated {V : Type} [DecidableEq V] (halo : V → Finset V)
    (H : Nat) (bound : ∀ x, (halo x).card ≤ H)
    (requests : List (Finset V)) (excluded : Finset V)
    (enough : ∀ s ∈ requests, excluded.card + requests.length * H < s.card) :
    ∃ centres : List V, List.Forall₂ (fun x s => x ∈ s) centres requests ∧
      (∀ x ∈ centres, x ∉ excluded) ∧ centres.Pairwise (fun x y => y ∉ halo x) := by
  induction requests generalizing excluded with
  | nil => exact ⟨[],.nil,by simp,.nil⟩
  | cons s ss ih =>
    have hc := enough s List.mem_cons_self
    obtain ⟨x,hx,hout⟩ : ∃ x ∈ s, x ∉ excluded := by
      by_contra! h
      have := Finset.card_le_card h
      omega
    obtain ⟨xs,hm,ha,hs⟩ := ih (excluded ∪ halo x) (by
      intro t ht
      have ht' := enough t (List.mem_cons_of_mem s ht)
      simp only [List.length_cons,Nat.succ_mul] at ht'
      have hu := Finset.card_union_le excluded (halo x)
      have hh := bound x
      omega)
    refine ⟨x :: xs, .cons hx hm, ?_, List.pairwise_cons.mpr ⟨?_,hs⟩⟩
    · intro y hy; rcases List.mem_cons.mp hy with rfl | h
      · exact hout
      · exact fun he => ha _ h (Finset.mem_union_left _ he)
    · intro y hy he; exact ha _ hy (Finset.mem_union_right _ he)

private theorem extendAux {V : Type} [Fintype V] [DecidableEq V] (nb : V → Finset V)
    (symm : ∀ x y, x ∈ nb y → y ∈ nb x) (loopless : ∀ x, x ∉ nb x)
    (q : Nat) (bound : ∀ x, (nb x).card < q) (P : Finset V) (colour : V → Fin q)
    (proper : ∀ x ∈ P, ∀ y ∈ P, y ∈ nb x → colour x ≠ colour y) :
    ∃ κ : V → Fin q, (∀ x ∈ P, κ x = colour x) ∧ ∀ x y, y ∈ nb x → κ x ≠ κ y := by
  classical
  by_cases all : P = Finset.univ
  · subst P; exact ⟨colour,by simp,fun x y => proper x (by simp) y (by simp)⟩
  obtain ⟨z, hz⟩ : ∃ z, z ∉ P := by simpa [Finset.eq_univ_iff_forall] using all
  have hcard := (Finset.card_image_le (s := nb z) (f := colour)).trans_lt (bound z)
  have hne : (nb z).image colour ≠ Finset.univ := by
    intro he; simp [he] at hcard
  obtain ⟨fresh,hfresh⟩ : ∃ u, u ∉ (nb z).image colour := by simpa [Finset.eq_univ_iff_forall] using hne
  let f := Function.update colour z fresh
  have hold : ∀ x ∈ P, f x = colour x := by
    intro x hx
    have hne : x ≠ z := fun e => hz (e ▸ hx)
    exact Function.update_of_ne hne _ _
  have fixed : ∀ x ∈ insert z P, ∀ y ∈ insert z P, y ∈ nb x → f x ≠ f y := by
    intro x hx y hy hadj
    by_cases he : x = z
    · subst x
      have hne : y ≠ z := by intro h; subst y; exact loopless _ hadj
      rw [show f z = fresh from Function.update_self .., show f y = colour y from Function.update_of_ne hne _ _]
      intro h; apply hfresh; rw [h]; exact Finset.mem_image_of_mem _ hadj
    · by_cases he' : y = z
      · subst y
        rw [show f z = fresh from Function.update_self .., show f x = colour x from Function.update_of_ne he _ _]
        intro h; apply hfresh; rw [← h]; exact Finset.mem_image_of_mem _ (symm _ _ hadj)
      · have hx' := (Finset.mem_insert.mp hx).resolve_left he
        have hy' := (Finset.mem_insert.mp hy).resolve_left he'
        simpa only [hold _ hx',hold _ hy'] using proper _ hx' _ hy' hadj
  obtain ⟨κ,hκ,hproper⟩ := extendAux nb symm loopless q bound (insert z P) f fixed
  exact ⟨κ, fun x hx => (hκ x (Finset.mem_insert_of_mem hx)).trans (hold x hx), hproper⟩
termination_by Fintype.card V - P.card
decreasing_by
  have hlt := Finset.card_lt_card (Finset.ssubset_univ_iff.mpr all)
  simp [Finset.card_insert_of_notMem hz] at *
  omega

/--
---
conclusion: Lax977378.Separation.extendColouring
---
Colour one as-yet unrestricted vertex with a colour outside the image of
its neighbourhood, retaining the colours of all previously fixed vertices.
-/
theorem extendColouring {V : Type} [Fintype V] [DecidableEq V] (nb : V → Finset V)
    (symm : ∀ x y, x ∈ nb y → y ∈ nb x) (loopless : ∀ x, x ∉ nb x)
    (q : Nat) (bound : ∀ x, (nb x).card < q) (P : Finset V) (colour : V → Fin q)
    (proper : ∀ x ∈ P, ∀ y ∈ P, y ∈ nb x → colour x ≠ colour y) :
    ∃ κ : V → Fin q, (∀ x ∈ P, κ x = colour x) ∧ ∀ x y, y ∈ nb x → κ x ≠ κ y :=
  extendAux nb symm loopless q bound P colour proper

end Lax977378Proofs
