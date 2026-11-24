import Lax266678.WindowRank
import Mathlib.Tactic

namespace Lax266678Proofs.WindowRank
open Lax266678.WindowRank
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests

private abbrev Query (c : Nat) (I : Type) := (G : Graph c) → (I → Fin G.size) → Prop
private def Expressible {c : Nat} {I : Type} (budget : Nat) (P : Query c I) : Prop :=
  ∀ (scope : List Var) (names : I → Var), (∀ i, names i ∈ scope) →
    ∃ f : Formula c, Plain scope f ∧ rank f ≤ budget ∧ ∀ G o env v, (∀ i, env (names i) = some (v i)) →
      (eval G o env f ↔ P G v)

private theorem weaken {c : Nat} {I : Type} {P : Query c I} {a b}
    (hp : Expressible a P) (le : a ≤ b) : Expressible b P := by
  intro S nm h
  obtain ⟨f,hf,hr,eq⟩ := hp S nm h
  exact ⟨f,hf,hr.trans le,eq⟩

private theorem constant {c : Nat} {I : Type} (p : Prop) :
    Expressible (c:=c) (I:=I) 1 (fun _ _ => p) := by
  classical
  intro S _ _
  let bot : Formula c := .ex root (.neg (.eq root root))
  have hp : Plain S bot := by simp [bot, Plain]
  have hf (G : Graph c) o env : ¬ eval G o env bot := by simp [bot, eval]
  by_cases h : p
  · exact ⟨.neg bot, hp, by simp [rank,bot], fun G o env _ _ => iff_of_true (hf G o env) h⟩
  · exact ⟨bot,hp,by simp [rank,bot],fun G o env _ _ => iff_of_false (hf G o env) h⟩

private theorem eqQ {c : Nat} {I : Type} (i j : I) :
    Expressible (c:=c) 1 (fun _ v => v i = v j) := by
  intro S nm hn
  exact ⟨.eq (nm i) (nm j),⟨hn i,hn j⟩,by simp [rank],fun G o env v h => by simp [eval,h,eq_comm]⟩

private theorem edgeQ {c : Nat} {I : Type} (i j : I) :
    Expressible (c:=c) 1 (fun G v => G.edge (v i) (v j)) := by
  intro S nm hn
  exact ⟨.edge (nm i) (nm j),⟨hn i,hn j⟩,by simp [rank],fun G o env v h => by simp [eval,h]⟩

private theorem predQ {c : Nat} {I : Type} (p : Fin c) (i : I) :
    Expressible 1 (fun G v => G.pred p (v i)) := by
  intro S nm hn
  exact ⟨.pred p (nm i),hn i,by simp [rank],fun G o env v h => by simp [eval,h]⟩

private theorem negQ {c b : Nat} {I : Type} {P : Query c I} (hp : Expressible b P) :
    Expressible b (fun G v => ¬ P G v) := by
  intro S nm hn
  obtain ⟨f,hf,rf,h⟩ := hp S nm hn
  exact ⟨.neg f,hf,rf,fun G o env v hv => not_congr (h G o env v hv)⟩

private theorem orQ {c b : Nat} {I : Type} {P Q : Query c I}
    (hp : Expressible b P) (hq : Expressible b Q) : Expressible b (fun G v => P G v ∨ Q G v) := by
  intro S nm hn
  obtain ⟨f,hf,rf,h⟩ := hp S nm hn
  obtain ⟨g,hg,rg,k⟩ := hq S nm hn
  exact ⟨.disj f g, ⟨hf,hg⟩,max_le rf rg,fun G o env v hv => or_congr (h G o env v hv) (k G o env v hv)⟩

private theorem congrQ {c b : Nat} {I : Type} {P Q : Query c I} (hp : Expressible b P)
    (h : ∀ G v, P G v ↔ Q G v) : Expressible b Q := by
  intro S nm hn
  obtain ⟨f,hf,rf,h₁⟩ := hp S nm hn
  exact ⟨f,hf,rf,fun G o env v hv => (h₁ G o env v hv).trans (h G v)⟩

private theorem andQ {c b : Nat} {I : Type} {P Q : Query c I}
    (hp : Expressible b P) (hq : Expressible b Q) : Expressible b (fun G v => P G v ∧ Q G v) :=
  congrQ (negQ (orQ (negQ hp) (negQ hq))) (fun _ _ => by simp)

private theorem iffQ {c b : Nat} {I : Type} {P Q : Query c I}
    (hp : Expressible b P) (hq : Expressible b Q) : Expressible b (fun G v => P G v ↔ Q G v) :=
  congrQ (andQ (orQ (negQ hp) hq) (orQ (negQ hq) hp)) (fun _ _ => by tauto)

private theorem renameQ {c b : Nat} {I J : Type} {P : Query c I} (hp : Expressible b P)
    (idx : I → J) : Expressible b (fun G v => P G (v ∘ idx)) := by
  intro S nm hn
  obtain ⟨f,hf,rf,h⟩ := hp S (nm ∘ idx) (fun i => hn _)
  exact ⟨f,hf,rf,fun G o env v hv => h G o env _ (fun i => hv _)⟩

private theorem exQ {c b : Nat} {I : Type} {P : Query c (Option I)} (hp : Expressible b P) :
    Expressible (b+1) (fun G v => ∃ x, P G (fun z => z.elim x v)) := by
  intro S nm hn
  let fresh : Var := ([],(S.map Prod.snd).sum + 1)
  have hnew : fresh ∉ S := by
    intro hs
    have hmem : fresh.2 ∈ S.map Prod.snd := List.mem_map.mpr ⟨_,hs,rfl⟩
    have := List.single_le_sum (fun n _ => Nat.zero_le n) fresh.2 hmem
    simp [fresh] at this
  let names (z : Option I) : Var := z.elim fresh nm
  obtain ⟨f,hf,rf,h⟩ := hp (fresh :: S) names (by intro z; cases z <;> simp [names,hn])
  refine ⟨.ex fresh f,hf,Nat.succ_le_succ rf,?_⟩
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

private theorem everyQ {c b : Nat} {I : Type} {P : Query c (Option I)} (hp : Expressible b P) :
    Expressible (b+1) (fun G v => ∀ x, P G (fun z => z.elim x v)) :=
  congrQ (negQ (exQ (negQ hp))) (fun _ _ => by simp)

private theorem listAll {c b : Nat} {I J : Type} (hb : 1 ≤ b) (xs : List J) (P : J → Query c I)
    (hp : ∀ i ∈ xs, Expressible b (P i)) : Expressible b (fun G v => ∀ i ∈ xs, P i G v) := by
  induction xs with
  | nil => exact congrQ (weaken (constant True) hb) (by simp)
  | cons i xs ih => exact congrQ (andQ (hp i List.mem_cons_self) (ih (fun j hj => hp j (List.mem_cons_of_mem i hj)))) (by simp)

private theorem finiteAll {c b : Nat} {I J : Type} [Fintype J] (hb : 1 ≤ b) (P : J → Query c I)
    (hp : ∀ i, Expressible b (P i)) : Expressible b (fun G v => ∀ i, P i G v) := by
  classical
  exact congrQ (listAll hb (Finset.univ : Finset J).toList P (fun j _ => hp j)) (by simp)

private theorem listAny {c b : Nat} {I J : Type} (hb : 1 ≤ b) (xs : List J) (P : J → Query c I)
    (hp : ∀ i ∈ xs, Expressible b (P i)) : Expressible b (fun G v => ∃ i ∈ xs, P i G v) :=
  congrQ (negQ (listAll hb xs (fun i G v => ¬ P i G v) (fun i hi => negQ (hp i hi))))
    (fun _ _ => by simp)

private theorem tupleEx {c b : Nat} {I : Type} (n : Nat) {P : Query c (Sum (Fin n) I)}
    (hp : Expressible b P) : Expressible (b+n) (fun G v => ∃ y, P G (Sum.elim y v)) := by
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
    Expressible (c:=c) (r+1) (fun G y => within G r (y u) (y v)) := by
  induction r generalizing I with
  | zero => exact eqQ u v
  | succ r ih =>
    exact orQ (weaken (ih u v) (by omega))
      (exQ (andQ (ih (some u) none) (weaken (edgeQ none (some v)) (by omega))))

private theorem injectiveQ {c : Nat} {I J : Type} [Fintype J] (idx : J → I) :
    Expressible (c:=c) 1 (fun _ v => Function.Injective (v ∘ idx)) := by
  apply congrQ (finiteAll (by decide) (fun i G v => ∀ j, (v (idx i) = v (idx j) → i = j))
    (fun i => finiteAll (by decide) _ (fun j =>
      congrQ (orQ (negQ (eqQ (idx i) (idx j))) (constant (i = j))) (fun _ _ => by tauto))))
  intro G v; exact ⟨fun h i j => h i j, fun h i j => @h i j⟩

private theorem diagramQ {c : Nat} {I : Type} (W : Graph c) (idx : Fin W.size → I) :
    Expressible 1 (fun G v => Diagram W G (v ∘ idx)) := by
  apply andQ (injectiveQ idx)
  apply andQ
  · exact finiteAll le_rfl _ (fun i => finiteAll le_rfl _ (fun j =>
      iffQ (constant (W.edge i j)) (edgeQ (idx i) (idx j))))
  · exact finiteAll le_rfl _ (fun p => finiteAll le_rfl _ (fun i =>
      iffQ (constant (W.pred p i)) (predQ p (idx i))))

private theorem imageQ {c : Nat} {I J : Type} (xs : Finset J) (idx : J → I) (z : I) :
    Expressible (c:=c) 1 (fun _ v => ∃ i ∈ xs, v (idx i) = v z) :=
  congrQ (listAny le_rfl xs.toList _ (fun i _ => eqQ (idx i) z)) (by simp)

private theorem windowQ {c : Nat} {I : Type} (W : Graph c) (r : Nat)
    (marked : Finset (Fin W.size)) (idx : Fin W.size → I) :
    Expressible (r+2) (fun G v => Window W G r marked (v ∘ idx)) := by
  apply andQ (weaken (diagramQ W idx) (by omega))
  apply congrQ (everyQ (iffQ (weaken (imageQ Finset.univ (some ∘ idx) none) (by omega))
    (listAny (by omega) marked.toList _ (fun i _ => distQ r (some (idx i)) none))))
  simp

private theorem occursQ {c : Nat} {I : Type} (t : Pointed c) (r : Nat) (z : I) :
    Expressible (r+2+t.pattern.size) (fun G v => Occurs t r G (v z)) := by
  exact tupleEx t.pattern.size (andQ (windowQ t.pattern r {t.center} Sum.inl)
    (weaken (eqQ (Sum.inl t.center) (Sum.inr z)) (by omega)))

private theorem atLeastQ {c : Nat} {I : Type} (t : Pointed c) (r k : Nat) :
    Expressible (I:=I) (r+2+t.pattern.size+k) (fun G _ => AtLeast t r k G) := by
  exact tupleEx k (andQ (weaken (injectiveQ Sum.inl) (by omega))
    (finiteAll (by omega) _ (fun i => occursQ t r (Sum.inl i))))

private theorem passesQ {c : Nat} {I : Type} (D : TestData c) (b U : Nat)
    (counts : ∀ e ∈ D.counts, e.1.pattern.size ≤ b ∧ e.2 ≤ D.cap)
    (freq : ∀ e ∈ D.frequent, e.pattern.size ≤ b) (size : D.windowGraph.size ≤ U) :
    Expressible (I:=I) (bound b D.radius D.cap U D.windowRadius) (fun G _ => Passes D G) := by
  unfold bound
  apply andQ
  · apply listAll (by omega) D.counts
    intro e he
    obtain ⟨hs,ht⟩ := counts e he
    apply andQ (weaken (constant _) (by omega))
    apply andQ (weaken (atLeastQ e.1 D.radius e.2) (by omega))
    exact congrQ (orQ (weaken (negQ (constant (e.2 < D.cap))) (by omega))
      (weaken (negQ (atLeastQ e.1 D.radius (e.2+1))) (by omega))) (fun _ _ => by tauto)
  · let inner := max D.windowRadius (b+D.radius) + 4
    apply weaken (a := inner+D.windowGraph.size) _ (by dsimp [inner]; omega)
    have rareAt : Expressible (c:=c) (I:=Option (Sum (Fin D.windowGraph.size) I))
        (D.radius+2+b) (fun G v => ∃ t ∈ D.frequent, Occurs t D.radius G (v none)) :=
      listAny (by omega) D.frequent _ (fun t ht =>
        weaken (occursQ t D.radius none) (by have := freq t ht; omega))
    exact tupleEx D.windowGraph.size (andQ
      (weaken (windowQ D.windowGraph D.windowRadius D.marked Sum.inl) (by dsimp [inner]; omega))
      (weaken (everyQ (iffQ (weaken (imageQ D.rare (some ∘ Sum.inl) none) (by omega))
        (negQ rareAt))) (by dsimp [inner]; omega)))

/--
---
conclusion: Lax266678.WindowRank.windowSentence
---
Build a sentence by existentially naming the window vertices, specifying their
induced diagram, and checking exact neighbourhood coverage and rarity. Compile
bounded distance, rooted types and count inequalities with a rank budget that
is preserved by finite Boolean combinations.
-/
theorem windowSentence {c : Nat} (D : TestData c) (b U : Nat)
    (counts : ∀ e ∈ D.counts, e.1.pattern.size ≤ b ∧ e.2 ≤ D.cap)
    (freq : ∀ e ∈ D.frequent, e.pattern.size ≤ b) (size : D.windowGraph.size ≤ U) :
    ∃ f : Formula c, Plain [] f ∧ rank f ≤ bound b D.radius D.cap U D.windowRadius ∧
      ∀ G, Unordered G f ↔ Passes D G := by
  obtain ⟨f,hp,hr,h⟩ := passesQ (I := Empty) D b U counts freq size [] Empty.elim (fun i => i.elim)
  exact ⟨f,hp,hr,fun G => h G _ _ Empty.elim (fun i => i.elim)⟩

end Lax266678Proofs.WindowRank
