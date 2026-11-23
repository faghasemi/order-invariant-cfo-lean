import Lax977378.Replay
import Mathlib.Tactic

namespace Lax977378Proofs.Replay
open Lax977378.Logic Lax977378.OuterContexts Lax977378.Collapse Lax977378.RecordTests

/--
---
conclusion: Lax977378.Replay.assemble
assumptions:
  - Lax977378.RecordTests.recordTest
---
Choose an order for each entry and each passing graph. A vertex label in
either graph belongs to the final table and is therefore realised in the
other graph under its independently chosen order.
-/
theorem assemble {c d K N} (lab : (G : Graph c) → G.Bounded d →
    LinearOrder (Fin G.size) → Fin G.size → Fin N)
    (sound : ∀ A B ha hb a b x y, lab A ha a x = lab B hb b y → same A B a b K x y)
    (entries : List (TestData c × Finset (Fin N)))
    (cover : ∀ G : Graph c, G.Bounded d → ∃ e ∈ entries, Passes e.1 G)
    (replay : ∀ e ∈ entries, ∀ (G : Graph c) (hd : G.Bounded d), Passes e.1 G →
      ∃ a, Finset.univ.image (lab G hd a) = e.2) :
    ∃ tests : List (Record (c := c) d K), ∀ G, G.Bounded d → ∃ e ∈ tests, Unordered G e.test := by
  classical
  choose f hf using (fun D : TestData c => Lax977378.RecordTests.recordTest D)
  let chooseOrder (e : TestData c × Finset (Fin N)) (G : Graph c) :=
    if h : e ∈ entries ∧ G.Bounded d ∧ Passes e.1 G then
      (replay e h.1 G h.2.1 h.2.2).choose else (inferInstance : LinearOrder (Fin G.size))
  have imageEq e G (he : e ∈ entries) (hd : G.Bounded d) (hp : Passes e.1 G) :
      Finset.univ.image (lab G hd (chooseOrder e G)) = e.2 := by
    simp only [chooseOrder,dif_pos (show e ∈ entries ∧ G.Bounded d ∧ Passes e.1 G from ⟨he,hd,hp⟩)]
    exact (replay e he G hd hp).choose_spec
  let build (e : {e // e ∈ entries}) : Record (c := c) d K :=
    { test := f e.val.1, plain := (hf _).1, order := chooseOrder e.val,
      agree := by
        intro A B ha hb hA hB
        have eqA := imageEq e.val A e.property ha (((hf _).2 A).mp hA)
        have eqB := imageEq e.val B e.property hb (((hf _).2 B).mp hB)
        constructor
        · intro x
          have hx := Finset.mem_image_of_mem (lab A ha (chooseOrder e.val A)) (Finset.mem_univ x)
          rw [eqA,← eqB] at hx
          obtain ⟨y,_,hy⟩ := Finset.mem_image.mp hx
          exact ⟨y,sound _ _ _ _ _ _ _ _ hy.symm⟩
        · intro y
          have hy := Finset.mem_image_of_mem (lab B hb (chooseOrder e.val B)) (Finset.mem_univ y)
          rw [eqB,← eqA] at hy
          obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hy
          exact ⟨x,sound _ _ _ _ _ _ _ _ hx⟩ }
  refine ⟨entries.attach.map build,?_⟩
  intro G hd
  obtain ⟨e,he,hp⟩ := cover G hd
  exact ⟨build ⟨e,he⟩,List.mem_map.mpr ⟨⟨e,he⟩,by simp,rfl⟩,((hf _).2 G).mpr hp⟩

end Lax977378Proofs.Replay
