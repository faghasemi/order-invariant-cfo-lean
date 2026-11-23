import Lax977378.InitialLevel
import Mathlib.Tactic

namespace Lax977378Proofs.InitialLevel
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Collapse

private def tautology (c : Nat) : Formula c := .neg (.ex root (.neg (.eq root root)))

private def allOf {c : Nat} : List (Formula c) → Formula c
  | [] => tautology c
  | f :: fs => conj f (allOf fs)

private theorem satAll {c : Nat} (fs : List (Formula c)) (G : Graph c) o env :
    eval G o env (allOf fs) ↔ ∀ f ∈ fs, eval G o env f := by
  classical
  induction fs with
  | nil => simp [allOf,tautology,eval]
  | cons x xs ih =>
    change (¬ (¬ eval G o env x ∨ ¬ eval G o env (allOf xs))) ↔ _
    simp [ih]

private theorem plainAll {c : Nat} (S : List Var) (fs : List (Formula c)) :
    Plain S (allOf fs) ↔ ∀ f ∈ fs, Plain S f := by
  induction fs with
  | nil => simp [allOf,tautology,Plain]
  | cons x xs ih =>
    change (Plain S x ∧ Plain S (allOf xs)) ↔ _
    simp [ih]

private abbrev Label (c : Nat) := Fin c → Bool

private noncomputable def label {c : Nat} (G : Graph c) (x : Fin G.size) : Label c :=
  fun p => @decide (G.pred p x) (Classical.propDecidable _)

private def literal {c : Nat} (p : Fin c) (positive : Bool) : Formula c :=
  if positive then .pred p root else .neg (.pred p root)

private def occurs {c : Nat} (l : Label c) : Formula c :=
  .ex root (allOf ((List.finRange c).map fun p => literal p (l p)))

private theorem plainOccurs {c : Nat} (l : Label c) : Plain [] (occurs l) := by
  apply (plainAll ..).mpr
  intro f hf
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hf
  cases h : l p <;> simp [literal,Plain]

private theorem satOccurs {c : Nat} (G : Graph c) (l : Label c) :
    Unordered G (occurs l) ↔ ∃ x, label G x = l := by
  classical
  change (∃ x, eval G _ _ (allOf _)) ↔ _
  apply exists_congr
  intro x
  rw [satAll]
  simp only [List.forall_mem_map, List.mem_finRange, forall_const, funext_iff]
  apply forall_congr'
  intro p
  cases h : l p <;> simp [literal,eval,label,root]

private noncomputable def labels {c : Nat} (G : Graph c) : Finset (Label c) :=
  Finset.univ.image (label G)

private noncomputable def test {c : Nat} (S : Finset (Label c)) : Formula c := by
  classical
  exact allOf ((Finset.univ : Finset (Label c)).toList.map
    (fun l => if l ∈ S then occurs l else .neg (occurs l)))

private theorem testPlain {c : Nat} (S : Finset (Label c)) : Plain [] (test S) := by
  classical
  apply (plainAll ..).mpr
  intro f hf
  obtain ⟨l,_,rfl⟩ := List.mem_map.mp hf
  split <;> exact plainOccurs l

private theorem testSat {c : Nat} (G : Graph c) (S : Finset (Label c)) :
    Unordered G (test S) ↔ labels G = S := by
  classical
  change eval G _ _ (allOf _) ↔ _
  rw [satAll]
  simp only [List.forall_mem_map, Finset.mem_toList,Finset.mem_univ,forall_const]
  rw [Finset.ext_iff]
  apply forall_congr'
  intro l
  by_cases hl : l ∈ S <;> simp [hl, labels, ← satOccurs, Unordered, Holds, eval]

private theorem agreeZero {c : Nat} (A B : Graph c) (a b) (h : labels A = labels B) :
    spectrumAgrees A B a b 0 := by
  classical
  have matchOne (X Y : Graph c) (hxy : labels X = labels Y) (x : Fin X.size) :
      ∃ y : Fin Y.size, ∀ p, X.pred p x ↔ Y.pred p y := by
    have hmem : label X x ∈ labels X := Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
    rw [hxy] at hmem
    obtain ⟨y,_,he⟩ := Finset.mem_image.mp hmem
    exact ⟨y,fun p => by simpa [label] using congrFun he.symm p⟩
  refine ⟨matchOne A B h, ?_⟩
  intro y
  obtain ⟨x,hx⟩ := matchOne B A h.symm y
  exact ⟨x,fun p => (hx p).symm⟩

private noncomputable def initial {c d : Nat} (S : Finset (Label c)) : Record (c := c) d 0 where
  test := test S
  plain := testPlain S
  order := fun _ => inferInstance
  agree := fun A B _ _ hA hB =>
    agreeZero A B _ _ (((testSat A S).mp hA).trans ((testSat B S).mp hB).symm)

/--
---
conclusion: Lax977378.InitialLevel.initialRecords
---
Enumerate every subset of the finite set of unary labels. Conjoin,
for each label, either an existential occurrence sentence or its negation.
-/
theorem initialRecords (c d : Nat) : ∃ tests : List (Record (c := c) d 0),
    ∀ G, G.Bounded d → ∃ e ∈ tests, Unordered G e.test := by
  classical
  refine ⟨(Finset.univ : Finset (Finset (Label c))).toList.map initial, ?_⟩
  intro G _
  exact ⟨initial (labels G), List.mem_map.mpr ⟨labels G,by simp,rfl⟩,(testSat G _).mpr rfl⟩

end Lax977378Proofs.InitialLevel
