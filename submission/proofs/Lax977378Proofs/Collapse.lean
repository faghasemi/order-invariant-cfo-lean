import Lax977378.Collapse
import Mathlib.Tactic

namespace Lax977378Proofs
open Lax977378.Logic Lax977378.Collapse

private def bottom (c : Nat) : Formula c := .ex root (.neg (.eq root root))

private theorem bottom_false {c : Nat} (G : Graph c) : ¬ Unordered G (bottom c) := by
  simp [Unordered, Holds, bottom, eval]

private def disjoin {c : Nat} (fs : List (Formula c)) : Formula c :=
  fs.foldr Formula.disj (bottom c)

private theorem plain_disjoin {c : Nat} (fs : List (Formula c))
    (hs : ∀ f ∈ fs, Plain [] f) : Plain [] (disjoin fs) := by
  induction fs with
  | nil => simp [disjoin, bottom, Plain]
  | cons a as ih =>
    exact ⟨hs a List.mem_cons_self, ih (fun f h => hs f (List.mem_cons_of_mem _ h))⟩

private theorem sat_disjoin {c : Nat} (G : Graph c) (fs : List (Formula c)) :
    Unordered G (disjoin fs) ↔ ∃ f ∈ fs, Unordered G f := by
  induction fs with
  | nil => simp [disjoin, bottom_false]
  | cons a as ih =>
    change (Unordered G a ∨ Unordered G (disjoin as)) ↔ _
    simp [ih]

/-- Each test is conjoined with the failure of the preceding tests. -/
private def firstTests {c d K : Nat} (earlier : List (Formula c)) :
    List (Record (c := c) d K) → List (Record (c := c) d K × Formula c)
  | [] => []
  | e :: es => (e, conj e.test (.neg (disjoin earlier))) :: firstTests (e.test :: earlier) es

private theorem firstPlain {c d K : Nat} (rs : List (Record (c := c) d K))
    (earlier : List (Formula c)) (hp : ∀ f ∈ earlier, Plain [] f) :
    ∀ pair ∈ firstTests earlier rs, Plain [] pair.2 := by
  induction rs generalizing earlier with
  | nil => simp [firstTests]
  | cons e es ih =>
    intro pair h
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨e.plain, plain_disjoin _ hp⟩
    · exact ih _ (by simpa using And.intro e.plain hp) _ h

private theorem firstSound {c d K : Nat} (rs : List (Record (c := c) d K))
    (earlier : List (Formula c)) (G : Graph c) :
    ∀ pair ∈ firstTests earlier rs, Unordered G pair.2 → Unordered G pair.1.test := by
  classical
  induction rs generalizing earlier with
  | nil => simp [firstTests]
  | cons e es ih =>
    intro pair h sat
    rcases List.mem_cons.mp h with rfl | h
    · exact (not_or.mp sat).1 |> Classical.not_not.mp
    · exact ih _ _ h sat

private theorem firstCover {c d K : Nat} (rs : List (Record (c := c) d K))
    (earlier : List (Formula c)) (G : Graph c) (hp : ¬ Unordered G (disjoin earlier))
    (pass : ∃ e ∈ rs, Unordered G e.test) :
    ∃ pair ∈ firstTests earlier rs, Unordered G pair.2 := by
  classical
  induction rs generalizing earlier with
  | nil => simp at pass
  | cons e es ih =>
    by_cases he : Unordered G e.test
    · exact ⟨_, List.mem_cons_self, not_or.mpr ⟨not_not.mpr he, not_not.mpr hp⟩⟩
    · have tail : ∃ e ∈ es, Unordered G e.test := by simpa [he] using pass
      obtain ⟨p,hm,hs⟩ := ih (e.test :: earlier) (not_or.mpr ⟨he,hp⟩) tail
      exact ⟨p,List.mem_cons_of_mem _ hm,hs⟩

/--
---
conclusion: Lax977378.Collapse.relativeCollapse
assumptions:
  - Lax977378.Collapse.comparison
  - Lax977378.Collapse.records
---
Select the first-successful-test formulas with a positive witness in the class and disjoin them.
The ordered comparison and order invariance make each successful test
homogeneous for the chosen sentence.
-/
theorem relativeCollapse {c d : Nat} (C : Graph c → Prop) (bounded : ∀ G, C G → G.Bounded d)
    (f : Formula c) (legal : Legal [] f) (inv : InvariantOn C f) :
    ∃ φ : Formula c, Plain [] φ ∧ ∀ G, C G → ∀ o, Holds G o f ↔ Unordered G φ := by
  classical
  obtain ⟨rs, cover⟩ := records c d (rank f)
  let parts := firstTests [] rs
  let positive (p : Record (c := c) d (rank f) × Formula c) :=
    ∃ A, C A ∧ Unordered A p.2 ∧ Holds A (p.1.order A) f
  let selected := parts.filter (fun p => decide (positive p))
  refine ⟨disjoin (selected.map Prod.snd), plain_disjoin _ ?_, ?_⟩
  · intro φ hφ
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hφ
    exact firstPlain rs [] (by simp) p (List.mem_filter.mp hp).1
  · intro G hG o
    rw [sat_disjoin]
    constructor
    · intro yes
      obtain ⟨p,hp,hpass⟩ := firstCover rs [] G (bottom_false G) (cover G (bounded G hG))
      have hpos : positive p := ⟨G,hG,hpass,(inv G hG o (p.1.order G)).mp yes⟩
      exact ⟨_, List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, decide_eq_true hpos⟩, rfl⟩, hpass⟩
    · rintro ⟨φ,hφ,hpass⟩
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hφ
      have hpart := (List.mem_filter.mp hp).1
      obtain ⟨A,hA,htest,yes⟩ := of_decide_eq_true (List.mem_filter.mp hp).2
      have agree := p.1.agree A G (bounded A hA) (bounded G hG)
        (firstSound rs [] A p hpart htest) (firstSound rs [] G p hpart hpass)
      have hg := (comparison _ A G _ _ agree f legal (Nat.le_succ _)).mp yes
      exact (inv G hG (p.1.order G) o).mp hg

/--
---
conclusion: Lax977378.Collapse.collapse
assumptions:
  - Lax977378.Collapse.relativeCollapse
---
Global invariance restricts to every bounded-degree class.
-/
theorem collapse {c d : Nat} (C : Graph c → Prop) (bounded : ∀ G, C G → G.Bounded d)
    (f : Formula c) (legal : Legal [] f)
    (inv : ∀ G : Graph c, ∀ a b, Holds G a f ↔ Holds G b f) :
    ∃ φ : Formula c, Plain [] φ ∧ ∀ G, C G → ∀ o, Holds G o f ↔ Unordered G φ :=
  Lax977378.Collapse.relativeCollapse C bounded f legal (fun G _ => inv G)

end Lax977378Proofs
