import Lax977378.SourceRun
import Lax977378Proofs.Catalogue
import Lax977378Proofs.Window
import Mathlib.Data.Prod.Lex

namespace Lax977378Proofs.SourceRun
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Blocks Lax977378.Stage Lax977378.TagSafety
open Lax977378.SourceRun Lax977378Proofs.Catalogue

theorem compatibleOrder {v n} (row : Fin v → Fin n) : ∃ a, Compatible a row := by
  let key (x : Fin v) := toLex (row x,x)
  let a := LinearOrder.lift' key (fun _ _ h => congrArg (fun p => (ofLex p).2) h)
  refine ⟨a,fun x y le => ?_⟩
  rcases Prod.Lex.toLex_le_toLex.mp (show key x ≤ key y from le) with h | ⟨h,_⟩
  · exact le_of_lt h
  · exact le_of_eq h

private theorem endpoints {v n} (row : Fin v → Fin n) (onto : Function.Surjective row) :
    ∃ f l : Fin n → Fin v, (∀ t, row (f t) = t) ∧ (∀ t, row (l t) = t) ∧
      ∀ t, f t = l t → ∀ x, row x = t → x = f t := by
  classical
  let S (t) := Finset.univ.filter (fun x => row x = t)
  have ne (t) : (S t).Nonempty := by obtain ⟨x,h⟩ := onto t; exact ⟨x,by simp [S,h]⟩
  refine ⟨fun t => (S t).min' (ne t),fun t => (S t).max' (ne t),
    fun t => (Finset.mem_filter.mp ((S t).min'_mem _)).2,
    fun t => (Finset.mem_filter.mp ((S t).max'_mem _)).2,?_⟩
  intro t eq x hx
  have mem : x ∈ S t := by simp [S,hx]
  exact le_antisymm (eq ▸ (S t).le_max' x mem) ((S t).min'_le x mem)

/--
---
conclusion: Lax977378.SourceRun.construct
assumptions:
  - Lax977378.Stage.refineBlocks
---
Choose endpoints in every nonempty row. Enlarge the exceptional set by taking
the balls around it and the endpoints, then apply refinement. A child row
stays inside its parent, so separation on the full inspection ball persists.
-/
theorem construct (c d K : Nat) : ∃ N : Nat → Nat, ∀ (G : Graph c), G.Bounded d →
    ∀ (initial : Layer G) (b : Nat), initial.n ≤ b → initial.exceptions.card ≤ b →
    Function.Surjective initial.row → Stable G 0 initial.row →
    (∀ x, Function.Injective (fun u : Ball G K x => initial.row u.val)) →
    ∃ L : Layer G, History G initial K L ∧ Stable G K L.row ∧
      Function.Surjective L.row ∧ L.n ≤ limit d N b K ∧ L.exceptions.card ≤ limit d N b K := by
  classical
  choose N step using (fun j => Lax977378.Stage.refineBlocks c d j)
  refine ⟨N,?_⟩
  intro G hd initial b hn he onto stable sep
  have run (j : Nat) (hj : j ≤ K) : ∃ L : Layer G, History G initial j L ∧
      Stable G j L.row ∧ Function.Surjective L.row ∧ L.n ≤ limit d N b j ∧
      L.exceptions.card ≤ limit d N b j ∧
      ∀ x, Function.Injective (fun u : Ball G K x => L.row u.val) := by
    induction j with
    | zero => exact ⟨initial,rfl,stable,onto,hn,he,sep⟩
    | succ j ih =>
      obtain ⟨H,hist,st,sur,hrows,hex,inj⟩ := ih (by omega)
      obtain ⟨f,l,hf,hl,hs⟩ := endpoints H.row sur
      let M := H.exceptions ∪ Finset.univ.image f ∪ Finset.univ.image l
      let Γ := M.biUnion (ball G (radius (j+1)))
      have hM : M.card ≤ H.exceptions.card + H.n + H.n := by
        have u := Finset.card_union_le H.exceptions (Finset.univ.image f)
        have v := Finset.card_union_le (H.exceptions ∪ Finset.univ.image f) (Finset.univ.image l)
        have a := Finset.card_image_le (s := Finset.univ) (f := f)
        have b' := Finset.card_image_le (s := Finset.univ) (f := l)
        simp only [Finset.card_univ,Fintype.card_fin] at a b'
        dsimp [M]; omega
      have hΓ : Γ.card ≤ 3 * limit d N b j * (d+1)^radius (j+1) := by
        calc
          _ ≤ ∑ z ∈ M, (ball G (radius (j+1)) z).card := Finset.card_biUnion_le
          _ ≤ ∑ _z ∈ M, (d+1)^radius (j+1) := by gcongr with z; exact ballCard G d hd _ z
          _ = M.card * _ := by simp
          _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
      have covers (x) : x ∈ Γ ↔ ∃ z, (z ∈ H.exceptions ∨ (∃ t, f t = z) ∨ ∃ t, l t = z) ∧
          within G (radius (j+1)) z x := by simp [Γ,M]
      have inΓ (t) : f t ∈ Γ ∧ l t ∈ Γ :=
        ⟨(covers _).mpr ⟨_,Or.inr (Or.inl ⟨t,rfl⟩),centerWithin ..⟩,
          (covers _).mpr ⟨_,Or.inr (Or.inr ⟨t,rfl⟩),centerWithin ..⟩⟩
      have small (x) : Function.Injective (fun u : Ball G (j+1) x => H.row u.val) := by
        intro u v eq
        let up (w : Ball G (j+1) x) : Ball G K x := ⟨w.val,Window.grow w.property hj⟩
        exact Subtype.ext (congrArg (fun w : Ball G K x => w.val) (inj x (show H.row (up u).val = H.row (up v).val from eq)))
      obtain ⟨m,next,hit,bound,st',parent,children⟩ := step j G hd H.row f l hf hl hs Γ inΓ st small
      let L : Layer G := ⟨m,next,Γ⟩
      have arith : 3 * limit d N b j * (d+1)^radius (j+1) + limit d N b j * N j =
          limit d N b (j+1) := by simp only [limit]; ring
      have upper := Nat.add_le_add hΓ (Nat.mul_le_mul_right (N j) hrows)
      rw [arith] at upper
      refine ⟨L,⟨H,hist,f,l,covers,parent,children⟩,st',hit,bound.trans upper,
        (Nat.le_add_right _ _).trans upper,?_⟩
      obtain ⟨a,ha⟩ := compatibleOrder next
      intro x u v eq
      exact inj x (((children a ha _ _).mp eq).1)
  obtain ⟨L,h,s,o,m,z,_⟩ := run K le_rfl
  exact ⟨L,h,s,o,m,z⟩

end Lax977378Proofs.SourceRun
