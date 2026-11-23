import Lax977378.TableFacts
import Lax977378.ContextLabels
import Lax977378Proofs.Catalogue
import Lax977378Proofs.Window

namespace Lax977378Proofs.TableFacts
open Lax977378.Logic Lax977378.OuterContexts Lax977378.SourceTables Lax977378.OrdinaryCalls
open Lax977378.TableFacts

/--
---
conclusion: Lax977378.TableFacts.facts
assumptions:
  - Lax977378.ContextLabels.finiteLabels
---
Each old exception and each new endpoint belongs to its own ball. For
separation, project a child row equality back to the initial rows and embed
the inspected ball in the K-ball. The child group rule gives homogeneity.
-/
theorem facts {c d K} (A : Graph c) (hd : A.Bounded d) (a : LinearOrder (Fin A.size))
    (T : Nat → Table A a) (next : ∀ j < K, Follows j (T j) (T (j+1)))
    (base : ∀ x y, (T 0).part.block x = (T 0).part.block y → ∀ p, A.pred p x ↔ A.pred p y)
    (sep : ∀ x, Function.Injective (fun u : Ball A K x => (T 0).part.block u.val)) :
    (∀ i j, i ≤ j → j ≤ K → (T i).exceptions ⊆ (T j).exceptions) ∧
    (∀ j < K, endpoints (T j) ⊆ (T (j+1)).exceptions) ∧
    (∀ j ≤ K, ∀ x y, (T j).part.block x = (T j).part.block y → same A A a a j x y) ∧
    (∀ j < K, ∀ x, Function.Injective (fun u : Ball A (j+1) x => (T j).part.block u.val)) := by
  have mono j (hj : j < K) : (T j).exceptions ⊆ (T (j+1)).exceptions := by
    intro x hx
    exact ((next j hj).1 x).mpr ⟨x,Or.inl hx,Catalogue.centerWithin ..⟩
  have earlier j (hj : j ≤ K) : ∀ x y, (T j).part.block x = (T j).part.block y →
      (T 0).part.block x = (T 0).part.block y := by
    induction j with
    | zero => exact fun _ _ h => h
    | succ j ih => exact fun x y h => ih (by omega) x y (((next j (by omega)).2 x y).mp h).1
  refine ⟨?_,?_,?_,?_⟩
  · intro i j le
    induction j,le using Nat.le_induction with
    | base => intro _; exact Finset.Subset.rfl
    | succ j _ ih => intro hj; exact (ih (by omega)).trans (mono j (by omega))
  · intro j hj x hx
    apply ((next j hj).1 x).mpr
    refine ⟨x,Or.inr ?_,Catalogue.centerWithin ..⟩
    simpa [endpoints] using hx
  · intro j hj x y eq
    cases j with
    | zero => exact base _ _ eq
    | succ j =>
      rcases (((next j (by omega)).2 x y).mp eq).2 with rfl | ⟨_,_,h⟩
      · obtain ⟨_,_,agree⟩ := Lax977378.ContextLabels.finiteLabels c d (j+1)
        exact (agree A A hd hd a a x x).mp rfl
      · exact h
  · intro j hj x u v eq
    let up (w : Ball A (j+1) x) : Ball A K x := ⟨w.val,Window.grow w.property hj⟩
    have e : (T 0).part.block (up u).val = (T 0).part.block (up v).val := earlier j (by omega) _ _ eq
    exact Subtype.ext (congrArg (fun w : Ball A K x => w.val) (sep x e))

end Lax977378Proofs.TableFacts
