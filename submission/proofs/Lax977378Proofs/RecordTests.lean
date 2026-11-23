import Lax977378.RecordTests
import Mathlib.Tactic

namespace Lax977378Proofs.RecordTests
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests

private abbrev Query (c : Nat) (I : Type) := (G : Graph c) → (I → Fin G.size) → Prop
private def Expressible {c : Nat} {I : Type} (P : Query c I) : Prop :=
  ∀ (scope : List Var) (names : I → Var), (∀ i, names i ∈ scope) →
    ∃ f : Formula c, Plain scope f ∧ ∀ G o env v, (∀ i, env (names i) = some (v i)) →
      (eval G o env f ↔ P G v)

private theorem constant {c : Nat} {I : Type} (p : Prop) :
    Expressible (c:=c) (I:=I) (fun _ _ => p) := by
  classical
  intro S _ _
  let bot : Formula c := .ex root (.neg (.eq root root))
  have hp : Plain S bot := by simp [bot, Plain]
  have hf (G : Graph c) o env : ¬ eval G o env bot := by simp [bot, eval]
  by_cases h : p
  · exact ⟨.neg bot, hp, fun G o env _ _ => iff_of_true (hf G o env) h⟩
  · exact ⟨bot,hp,fun G o env _ _ => iff_of_false (hf G o env) h⟩

private theorem eqQ {c : Nat} {I : Type} (i j : I) :
    Expressible (c:=c) (fun _ v => v i = v j) := by
  intro S nm hn
  exact ⟨.eq (nm i) (nm j),⟨hn i,hn j⟩,fun G o env v h => by simp [eval,h,eq_comm]⟩

private theorem edgeQ {c : Nat} {I : Type} (i j : I) :
    Expressible (c:=c) (fun G v => G.edge (v i) (v j)) := by
  intro S nm hn
  exact ⟨.edge (nm i) (nm j),⟨hn i,hn j⟩,fun G o env v h => by simp [eval,h]⟩

private theorem predQ {c : Nat} {I : Type} (p : Fin c) (i : I) :
    Expressible (fun G v => G.pred p (v i)) := by
  intro S nm hn
  exact ⟨.pred p (nm i),hn i,fun G o env v h => by simp [eval,h]⟩

private theorem negQ {c : Nat} {I : Type} {P : Query c I} (hp : Expressible P) :
    Expressible (fun G v => ¬ P G v) := by
  intro S nm hn
  obtain ⟨f,hf,h⟩ := hp S nm hn
  exact ⟨.neg f,hf,fun G o env v hv => not_congr (h G o env v hv)⟩

private theorem orQ {c : Nat} {I : Type} {P Q : Query c I}
    (hp : Expressible P) (hq : Expressible Q) : Expressible (fun G v => P G v ∨ Q G v) := by
  intro S nm hn
  obtain ⟨f,hf,h⟩ := hp S nm hn
  obtain ⟨g,hg,k⟩ := hq S nm hn
  exact ⟨.disj f g, ⟨hf,hg⟩,fun G o env v hv => or_congr (h G o env v hv) (k G o env v hv)⟩

private theorem congrQ {c : Nat} {I : Type} {P Q : Query c I} (hp : Expressible P)
    (h : ∀ G v, P G v ↔ Q G v) : Expressible Q := by
  intro S nm hn
  obtain ⟨f,hf,h₁⟩ := hp S nm hn
  exact ⟨f,hf,fun G o env v hv => (h₁ G o env v hv).trans (h G v)⟩

private theorem andQ {c : Nat} {I : Type} {P Q : Query c I}
    (hp : Expressible P) (hq : Expressible Q) : Expressible (fun G v => P G v ∧ Q G v) :=
  congrQ (negQ (orQ (negQ hp) (negQ hq))) (fun _ _ => by simp)

private theorem iffQ {c : Nat} {I : Type} {P Q : Query c I}
    (hp : Expressible P) (hq : Expressible Q) : Expressible (fun G v => P G v ↔ Q G v) :=
  congrQ (andQ (orQ (negQ hp) hq) (orQ (negQ hq) hp)) (fun _ _ => by tauto)

private theorem renameQ {c : Nat} {I J : Type} {P : Query c I} (hp : Expressible P)
    (idx : I → J) : Expressible (fun G v => P G (v ∘ idx)) := by
  intro S nm hn
  obtain ⟨f,hf,h⟩ := hp S (nm ∘ idx) (fun i => hn _)
  exact ⟨f,hf,fun G o env v hv => h G o env _ (fun i => hv _)⟩

private theorem exQ {c : Nat} {I : Type} {P : Query c (Option I)} (hp : Expressible P) :
    Expressible (fun G v => ∃ x, P G (fun z => z.elim x v)) := by
  intro S nm hn
  let fresh : Var := ([],(S.map Prod.snd).sum + 1)
  have hnew : fresh ∉ S := by
    intro hs
    have hmem : fresh.2 ∈ S.map Prod.snd := List.mem_map.mpr ⟨_,hs,rfl⟩
    have := List.single_le_sum (fun n _ => Nat.zero_le n) fresh.2 hmem
    simp [fresh] at this
  let names (z : Option I) : Var := z.elim fresh nm
  obtain ⟨f,hf,h⟩ := hp (fresh :: S) names (by intro z; cases z <;> simp [names,hn])
  refine ⟨.ex fresh f,hf,?_⟩
  intro G o env v hv
  apply exists_congr
  intro x
  apply h
  intro z
  cases z with
  | none => simp [names]
  | some i =>
    have ne : nm i ≠ fresh := fun he => hnew (he ▸ hn i)
    simp [names,ne,hv]

private theorem everyQ {c : Nat} {I : Type} {P : Query c (Option I)} (hp : Expressible P) :
    Expressible (fun G v => ∀ x, P G (fun z => z.elim x v)) :=
  congrQ (negQ (exQ (negQ hp))) (fun _ _ => by simp)

private theorem listAll {c : Nat} {I J : Type} (xs : List J) (P : J → Query c I)
    (hp : ∀ i, Expressible (P i)) : Expressible (fun G v => ∀ i ∈ xs, P i G v) := by
  induction xs with
  | nil => exact congrQ (constant True) (by simp)
  | cons i xs ih => exact congrQ (andQ (hp i) ih) (by simp)

private theorem finiteAll {c : Nat} {I J : Type} [Fintype J] (P : J → Query c I)
    (hp : ∀ i, Expressible (P i)) : Expressible (fun G v => ∀ i, P i G v) := by
  classical
  exact congrQ (listAll (Finset.univ : Finset J).toList P hp) (by simp)

private theorem listAny {c : Nat} {I J : Type} (xs : List J) (P : J → Query c I)
    (hp : ∀ i, Expressible (P i)) : Expressible (fun G v => ∃ i ∈ xs, P i G v) :=
  congrQ (negQ (listAll xs (fun i G v => ¬ P i G v) (fun i => negQ (hp i))))
    (fun _ _ => by simp)

private theorem tupleEx {c : Nat} {I : Type} (n : Nat) {P : Query c (Sum (Fin n) I)}
    (hp : Expressible P) : Expressible (fun G v => ∃ y, P G (Sum.elim y v)) := by
  induction n generalizing I with
  | zero => exact congrQ (renameQ hp (Sum.elim Fin.elim0 id)) (by
      intro G v
      have he (f : Fin 0 → Fin G.size) : (v ∘ Sum.elim Fin.elim0 id) = Sum.elim f v := by
        funext z; cases z with
        | inl i => exact i.elim0
        | inr _ => rfl
      exact ⟨fun h => ⟨Fin.elim0, he _ ▸ h⟩,fun ⟨f,h⟩ => he f ▸ h⟩)
  | succ k ih =>
    let m : Sum (Fin (k+1)) I → Sum (Fin k) (Option I) :=
      Sum.elim (Fin.cases (.inr none) Sum.inl) (fun i => .inr (some i))
    apply congrQ (exQ (ih (renameQ hp m)))
    intro G v
    have he (x : Fin G.size) (y : Fin k → Fin G.size) :
        (Sum.elim y (fun z : Option I => z.elim x v)) ∘ m = Sum.elim (Fin.cons x y) v := by
      funext z; cases z with
      | inl i => refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
      | inr _ => rfl
    constructor
    · rintro ⟨x,y,hy⟩; exact ⟨_,he x y ▸ hy⟩
    · rintro ⟨ys,hy⟩
      refine ⟨ys 0,Fin.tail ys,?_⟩
      simpa only [he,Fin.cons_self_tail] using hy

private theorem distQ {c : Nat} {I : Type} (r : Nat) (u v : I) :
    Expressible (c:=c) (fun G y => within G r (y u) (y v)) := by
  induction r generalizing I with
  | zero => exact eqQ u v
  | succ r ih =>
    exact orQ (ih u v) (exQ (andQ (ih (some u) none) (edgeQ none (some v))))


private theorem injectiveQ {c : Nat} {I J : Type} [Fintype J] (idx : J → I) :
    Expressible (c:=c) (fun _ v => Function.Injective (v ∘ idx)) := by
  apply congrQ (finiteAll (fun i G v => ∀ j, (v (idx i) = v (idx j) → i = j))
    (fun i => finiteAll _ (fun j =>
      congrQ (orQ (negQ (eqQ (idx i) (idx j))) (constant (i = j))) (fun _ _ => by tauto))))
  intro G v; exact ⟨fun h i j => h i j, fun h i j => @h i j⟩

private theorem diagramQ {c : Nat} {I : Type} (W : Graph c) (idx : Fin W.size → I) :
    Expressible (fun G v => Diagram W G (v ∘ idx)) := by
  apply andQ (injectiveQ idx)
  apply andQ
  · exact finiteAll _ (fun i => finiteAll _ (fun j =>
      iffQ (constant (W.edge i j)) (edgeQ (idx i) (idx j))))
  · exact finiteAll _ (fun p => finiteAll _ (fun i =>
      iffQ (constant (W.pred p i)) (predQ p (idx i))))

private theorem imageQ {c : Nat} {I J : Type} (xs : Finset J) (idx : J → I) (z : I) :
    Expressible (c:=c) (fun _ v => ∃ i ∈ xs, v (idx i) = v z) := by
  exact congrQ (listAny xs.toList _ (fun i => eqQ (idx i) z)) (by simp)

private theorem windowQ {c : Nat} {I : Type} (W : Graph c) (r : Nat)
    (marked : Finset (Fin W.size)) (idx : Fin W.size → I) :
    Expressible (fun G v => Window W G r marked (v ∘ idx)) := by
  apply andQ (diagramQ W idx)
  apply congrQ (everyQ (iffQ (imageQ Finset.univ (some ∘ idx) none)
    (listAny marked.toList _ (fun i => distQ r (some (idx i)) none))))
  simp

private theorem occursQ {c : Nat} {I : Type} (t : Pointed c) (r : Nat) (z : I) :
    Expressible (fun G v => Occurs t r G (v z)) := by
  exact tupleEx t.pattern.size (andQ (windowQ t.pattern r {t.center} Sum.inl)
    (eqQ (Sum.inl t.center) (Sum.inr z)))

private theorem atLeastQ {c : Nat} {I : Type} (t : Pointed c) (r k : Nat) :
    Expressible (I:=I) (fun G _ => AtLeast t r k G) := by
  exact tupleEx k (andQ (injectiveQ Sum.inl) (finiteAll _ (fun i => occursQ t r (Sum.inl i))))

private theorem passesQ {c : Nat} {I : Type} (D : TestData c) :
    Expressible (I:=I) (fun G _ => Passes D G) := by
  apply andQ
  · apply listAll D.counts
    intro tv
    apply andQ (constant (tv.2 ≤ D.cap))
    apply andQ (atLeastQ tv.1 D.radius tv.2)
    exact congrQ (orQ (negQ (constant (tv.2 < D.cap))) (negQ (atLeastQ tv.1 D.radius (tv.2+1))))
      (fun _ _ => by tauto)
  · exact tupleEx D.windowGraph.size (andQ (windowQ D.windowGraph D.windowRadius D.marked Sum.inl) (everyQ (iffQ (imageQ D.rare (some ∘ Sum.inl) none)
      (negQ (listAny D.frequent _ (fun t => occursQ t D.radius none))))))

/--
---
conclusion: Lax977378.RecordTests.recordTest
---
Compile bounded graph distance recursively, quantify the vertices of the
finite diagram simultaneously, and use a universal vertex variable for exact
window coverage and exact coverage of rare vertices. Positive and negative
occurrence tests give counts up to the cap.
-/
theorem recordTest {c : Nat} (D : TestData c) :
    ∃ f : Formula c, Plain [] f ∧ ∀ G, Unordered G f ↔ Passes D G := by
  obtain ⟨f,hplain,h⟩ := passesQ (I := Empty) D [] Empty.elim (fun i => i.elim)
  exact ⟨f,hplain,fun G => h G _ _ Empty.elim (fun i => i.elim)⟩

end Lax977378Proofs.RecordTests
