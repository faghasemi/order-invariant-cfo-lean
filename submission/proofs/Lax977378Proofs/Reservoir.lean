import Lax977378.Reservoir
import Lax977378Proofs.Catalogue

namespace Lax977378Proofs.Reservoir
open Lax977378.Logic Lax977378.OuterContexts Lax977378.CountParameters Lax977378.Planting

private theorem alignedCount {V T : Type} [DecidableEq T] (rel : V → T → Prop)
    [DecidableRel rel] {xs : List V} {ts : List T} (h : List.Forall₂ rel xs ts) (s : T) :
    ts.count s ≤ (xs.filter (fun x => decide (rel x s))).length := by
  induction h with
  | nil => simp
  | @cons x t xs ts hit _ ih =>
    by_cases eq : t = s
    · subst t; simpa [hit] using ih
    · by_cases keep : rel x s <;> simp [eq,keep] <;> omega

/--
---
conclusion: Lax977378.Reservoir.reserve
assumptions:
  - Lax977378.Planting.plant
---
Aligned lists give at least m realising centres for each request. Separation
makes the centres distinct, so they cannot all lie in the later exceptional set.
-/
theorem reserve {c d q} (G : Graph c) (hd : G.Bounded d) (r p m : Nat)
    (palette : (d+1)^p ≤ q) (P : Finset (Fin G.size)) (colour : Fin G.size → Fin q)
    (proper : ProperOn G p P colour) (seeds : List (Request c q))
    (enough : ∀ s ∈ seeds, (P.card + (seeds.length*m) * (d+1)^r) * (d+1)^(2*r+p) <
      (locations s.type r G).card) :
    ∃ k : Fin G.size → Fin q, (∀ u ∈ P, k u = colour u) ∧ ProperOn G p Finset.univ k ∧
      ∀ s ∈ seeds, ∀ M : Finset (Fin G.size), M.card < m →
        ∃ x ∉ M, Realised s G r k x ∧ ∀ u ∈ P, ¬ within G (2*r+p) u x := by
  classical
  let req := seeds.flatMap (List.replicate m)
  have length : req.length = seeds.length * m := by
    dsimp [req]; induction seeds with
    | nil => simp
    | cons s ss ih => simp [Nat.add_mul,Nat.add_comm]
  obtain ⟨k,cs,keep,hp,hits,avoid,sep⟩ := Lax977378.Planting.plant G hd r p palette P colour proper req (by
    intro s hs
    obtain ⟨t,ht,hh⟩ := List.mem_flatMap.mp hs
    obtain ⟨_,eq⟩ := List.mem_replicate.mp hh
    simpa [length,eq] using enough t ht)
  refine ⟨k,keep,hp,?_⟩
  intro s hs M small
  have ncopy : m ≤ req.count s := by
    dsimp [req]
    clear hits sep avoid length enough req
    induction seeds with
    | nil => simp at hs
    | cons t ts ih =>
      rcases List.mem_cons.mp hs with rfl | ht
      · simp
      · simp; exact le_trans (ih ht) (Nat.le_add_left ..)
  let rel := fun x s => Realised s G r k x
  let good := cs.filter (fun x => decide (rel x s))
  have size : m ≤ good.length := ncopy.trans (alignedCount rel hits s)
  have nodup : cs.Nodup := by
    apply List.Pairwise.imp _ sep
    intro x y h eq
    subst y; exact h (Catalogue.centerWithin ..)
  have gn : good.Nodup := nodup.filter _
  by_contra absent
  have sub : good.toFinset ⊆ M := by
    intro x hx
    obtain ⟨inCs,real⟩ := List.mem_filter.mp (List.mem_toFinset.mp hx)
    by_contra out
    exact absent ⟨x,out,of_decide_eq_true real,avoid x inCs⟩
  have bound := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup gn] at bound
  omega

end Lax977378Proofs.Reservoir
