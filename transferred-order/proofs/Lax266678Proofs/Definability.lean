import Lax266678.Definability
import Mathlib.Tactic

namespace Lax266678Proofs.Definability
open Lax977378.Logic Lax266678.Transfer

-- The atomic diagram of an n-tuple, followed by the set of one-point
-- extensions at each remaining depth.
private abbrev Atomic (c n : Nat) :=
  (Fin n → Fin n → Bool) × (Fin n → Fin n → Bool) × (Fin c → Fin n → Bool)

private def Code (c : Nat) : Nat → Nat → Type
  | 0, n => Atomic c n
  | q+1, n => Atomic c n × Finset (Code c q (n+1))

private instance codeFinite (c q n : Nat) : Finite (Code c q n) := by
  induction q generalizing n with
  | zero => change Finite (Atomic c n); infer_instance
  | succ q ih =>
    let := ih (n+1)
    change Finite (Atomic c n × Finset (Code c q (n+1)))
    infer_instance

private noncomputable def atoms {c n} (G : Graph c) (a : Fin n → Fin G.size) :
    Atomic c n := by
  classical exact (fun i j => decide (a i = a j), fun i j => decide (G.edge (a i) (a j)),
    fun p i => decide (G.pred p (a i)))

private noncomputable def profile {c} (G : Graph c) : (q n : Nat) →
    (Fin n → Fin G.size) → Code c q n
  | 0, _, a => atoms G a
  | q+1, n, a => by
    classical exact (atoms G a, Finset.univ.image (fun x => profile G q (n+1) (Fin.cons x a)))

private def Covered {c n} {A B : Graph c} (S : List Var)
    (a : Fin n → Fin A.size) (b : Fin n → Fin B.size)
    (ea : Var → Option (Fin A.size)) (eb : Var → Option (Fin B.size)) :=
  ∀ x ∈ S, ∃ i, ea x = some (a i) ∧ eb x = some (b i)

private theorem extendCovered {c n} {A B : Graph c} {S a b ea eb}
    (h : @Covered c n A B S a b ea eb) (x : Var) (v : Fin A.size) (w : Fin B.size) :
    Covered (x::S) (Fin.cons v a) (Fin.cons w b)
      (fun z => if z=x then some v else ea z) (fun z => if z=x then some w else eb z) := by
  intro z hz
  by_cases eq : z=x
  · subst z; exact ⟨0,by simp,by simp⟩
  · obtain ⟨i,hi,hj⟩ := h z ((List.mem_cons.mp hz).resolve_left eq)
    exact ⟨i.succ,by simpa [eq] using hi,by simpa [eq] using hj⟩

private theorem atomsAgree {c q n} {A B : Graph c} {a b}
    (h : profile A q n a = profile B q n b) : atoms A a = atoms B b := by
  cases q with
  | zero => exact h
  | succ => exact congrArg Prod.fst h

private theorem matchPoint {c q n} {A B : Graph c} {a b}
    (h : profile A (q+1) n a = profile B (q+1) n b) (x : Fin A.size) :
    ∃ y, profile A q (n+1) (Fin.cons x a) = profile B q (n+1) (Fin.cons y b) := by
  classical
  have hs := congrArg Prod.snd h
  change Finset.univ.image (fun v => profile A q (n+1) (Fin.cons v a)) =
    Finset.univ.image (fun w => profile B q (n+1) (Fin.cons w b)) at hs
  have mem := Finset.mem_image_of_mem (fun v => profile A q (n+1) (Fin.cons v a))
    (Finset.mem_univ x)
  rw [hs] at mem
  obtain ⟨y,_,hy⟩ := Finset.mem_image.mp mem
  exact ⟨y,hy.symm⟩

private theorem profileSound {c} (f : Formula c) {S} (hp : Plain S f)
    {q n} {A B : Graph c} {a b ea eb} (limit : rank f ≤ q)
    (h : profile A q n a = profile B q n b) (vars : Covered S a b ea eb) :
    eval A inferInstance ea f ↔ eval B inferInstance eb f := by
  classical
  induction f generalizing S q n A B with
  | pred p x =>
    obtain ⟨i,hi,hj⟩ := vars x hp
    have eq := congrArg (fun t : Atomic c n => t.2.2 p i) (atomsAgree h)
    simpa [eval,hi,hj,atoms] using eq
  | edge x y =>
    obtain ⟨i,hi,hj⟩ := vars x hp.1
    obtain ⟨j,hu,hv⟩ := vars y hp.2
    have eq := congrArg (fun t : Atomic c n => t.2.1 i j) (atomsAgree h)
    simpa [eval,hi,hj,hu,hv,atoms] using eq
  | eq x y =>
    obtain ⟨i,hi,hj⟩ := vars x hp.1
    obtain ⟨j,hu,hv⟩ := vars y hp.2
    have eq := congrArg (fun t : Atomic c n => t.1 j i) (atomsAgree h)
    simpa [eval,hi,hj,hu,hv,atoms] using eq
  | lt => exact False.elim hp
  | neg f ih => exact not_congr (ih hp limit h vars)
  | disj f g ih jh =>
    exact or_congr (ih hp.1 ((Nat.le_max_left ..).trans limit) h vars)
      (jh hp.2 ((Nat.le_max_right ..).trans limit) h vars)
  | ex x f ih =>
    cases q with
    | zero => simp [rank] at limit
    | succ q =>
      have small : rank f ≤ q := Nat.le_of_succ_le_succ limit
      constructor
      · rintro ⟨v,hv⟩
        obtain ⟨w,eq⟩ := matchPoint h v
        exact ⟨w,(ih hp small eq (extendCovered vars x v w)).mp hv⟩
      · rintro ⟨w,hw⟩
        obtain ⟨v,eq⟩ := matchPoint h.symm w
        exact ⟨v,(ih hp small eq.symm (extendCovered vars x v w)).mpr hw⟩

private def bottom (c : Nat) : Formula c := .ex root (.neg (.eq root root))

private def disjoin {c} (fs : List (Formula c)) := fs.foldr Formula.disj (bottom c)

private theorem disjoinPlain {c} (fs : List (Formula c)) (hs : ∀ f ∈ fs, Plain [] f) :
    Plain [] (disjoin fs) := by
  induction fs with
  | nil => simp [disjoin,bottom,Plain]
  | cons f fs ih => exact ⟨hs _ List.mem_cons_self,ih (fun g hg => hs _ (List.mem_cons_of_mem _ hg))⟩

private theorem disjoinSat {c} (G : Graph c) (fs : List (Formula c)) :
    Unordered G (disjoin fs) ↔ ∃ f ∈ fs, Unordered G f := by
  induction fs with
  | nil => simp [Unordered,Holds,eval,disjoin,bottom]
  | cons f fs ih =>
    change (Unordered G f ∨ Unordered G (disjoin fs)) ↔ _
    simp [ih]

/--
---
conclusion: Lax266678.Definability.definable
---
A tuple profile consists of its atomic diagram and, recursively, the finite
set of profiles obtained by adjoining one vertex. Equal depth-q profiles
give the same truth values to all order-free formulas of rank at most q,
by induction on formulas. Take one graph per realised empty-tuple profile
in the class. Separate each positive representative from each negative
representative by a rank-bounded sentence and form the finite Boolean combination.
-/
theorem definable {c : Nat} (C P : Graph c → Prop) (q : Nat)
    (stable : ∀ A B, C A → C B → equivalentAt q A B → (P A ↔ P B)) :
    ∃ f : Formula c, Plain [] f ∧ ∀ A, C A → (P A ↔ Unordered A f) := by
  classical
  let sig (G : Graph c) := profile G q 0 Fin.elim0
  have same {G H : Graph c} (eq : sig G = sig H) : equivalentAt q G H := by
    intro f hp hr
    exact profileSound f hp hr eq (by intro x hx; simp at hx)
  let I := {s : Code c q 0 // ∃ G, C G ∧ sig G = s}
  let : Fintype I := Fintype.ofFinite _
  choose rep repClass repSig using fun i : I => i.property
  let pos := Finset.univ.filter (fun i : I => P (rep i))
  let negs := Finset.univ.filter (fun i : I => ¬ P (rep i))
  have separates (i : pos) (j : negs) : ∃ f : Formula c,
      Plain [] f ∧ rank f ≤ q ∧ Unordered (rep i.val) f ∧ ¬ Unordered (rep j.val) f := by
    have yes : P (rep i.val) := (Finset.mem_filter.mp i.property).2
    have no : ¬ P (rep j.val) := (Finset.mem_filter.mp j.property).2
    have bad : ¬ equivalentAt q (rep i.val) (rep j.val) :=
      fun e => no ((stable _ _ (repClass _) (repClass _) e).mp yes)
    unfold equivalentAt at bad
    push Not at bad
    obtain ⟨f,hp,hr,h⟩ := bad
    by_cases ht : Unordered (rep i.val) f
    · exact ⟨f,hp,hr,ht,fun ht' => by simp [ht,ht'] at h⟩
    · refine ⟨.neg f,hp,hr,ht,?_⟩
      change ¬ ¬ Unordered (rep j.val) f
      intro hn
      simp [ht,hn] at h
  choose sep good using separates
  let exclusion (i : pos) := disjoin (Finset.univ.toList.map (fun j : negs => Formula.neg (sep i j)))
  let fs := Finset.univ.toList.map (fun i : pos => Formula.neg (exclusion i))
  refine ⟨disjoin fs,disjoinPlain _ ?_,?_⟩
  · intro f hf
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hf
    apply disjoinPlain
    intro g hg
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
    exact (good i j).1
  · intro G hG
    let idx : I := ⟨sig G,G,hG,rfl⟩
    have eq := same (repSig idx)
    have hp := stable _ _ (repClass idx) hG eq
    rw [disjoinSat]
    constructor
    · intro yes
      let i : pos := ⟨idx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp.mpr yes⟩⟩
      refine ⟨_,List.mem_map.mpr ⟨i,by simp,rfl⟩,?_⟩
      change ¬ Unordered G (exclusion i)
      intro hx
      obtain ⟨_,hm,hn⟩ := (disjoinSat _ _).mp hx
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hm
      exact hn ((eq _ (good i j).1 (good i j).2.1).mp (good i j).2.2.1)
    · rintro ⟨_,hm,yes⟩
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hm
      by_contra hn
      let j : negs := ⟨idx,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun h => hn (hp.mp h)⟩⟩
      apply yes
      apply (disjoinSat _ _).mpr
      refine ⟨_,List.mem_map.mpr ⟨j,by simp,rfl⟩,?_⟩
      exact fun h => (good i j).2.2.2 ((eq _ (good i j).1 (good i j).2.1).mpr h)

end Lax266678Proofs.Definability
