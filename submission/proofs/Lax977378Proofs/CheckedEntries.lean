import Lax977378.CheckedEntries
import Mathlib.Tactic

namespace Lax977378Proofs.CheckedEntries
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests Lax977378.Collapse

/--
---
conclusion: Lax977378.CheckedEntries.selectEntries
assumptions:
  - Lax977378.FiniteTests.finiteTests
  - Lax977378.Replay.assemble
---
Pair every bounded unordered test with every possible set of final labels.
Keep the pairs with universal replay. The source graph's own witness lies
in this list, and membership gives replay on each target independently.
-/
theorem selectEntries {c d K n N} (types : Fin n → Pointed c) (r R cap U : Nat)
    (lab : (G : Graph c) → G.Bounded d → LinearOrder (Fin G.size) → Fin G.size → Fin N)
    (sound : ∀ A B ha hb a b x y, lab A ha a x = lab B hb b y → same A B a b K x y)
    (witness : ∀ A : Graph c, A.Bounded d →
      ∃ (D : TestData c) (S : Finset (Fin N)) (v : Fin n → Fin (cap+1)) (t : Nat),
        D.radius = r ∧ D.windowRadius = R ∧ D.cap = cap ∧ D.windowGraph.size ≤ U ∧
        D.counts = List.ofFn (fun j => (types j,(v j).val)) ∧
        D.frequent = ((List.finRange n).filter (fun j => t ≤ (v j).val)).map types ∧
        Passes D A ∧ ∀ (B : Graph c) (hb : B.Bounded d), Passes D B →
          ∃ b, Finset.univ.image (lab B hb b) = S) :
    ∃ tests : List (Record (c := c) d K), ∀ G, G.Bounded d → ∃ e ∈ tests, Unordered G e.test := by
  classical
  obtain ⟨ts,_,complete⟩ := Lax977378.FiniteTests.finiteTests types r R cap U
  let sets := (Finset.univ : Finset (Finset (Fin N))).toList
  let pairs := ts.flatMap (fun e => sets.map (fun s => (e.1,s)))
  let good (e : TestData c × Finset (Fin N)) := ∀ (B : Graph c) (hb : B.Bounded d),
    Passes e.1 B → ∃ b, Finset.univ.image (lab B hb b) = e.2
  let entries := pairs.filter (fun e => decide (good e))
  apply Lax977378.Replay.assemble lab sound entries
  · intro A ha
    obtain ⟨D,S,v,t,hr,hR,hc,hu,counts,freq,hp,replay⟩ := witness A ha
    obtain ⟨f,hf⟩ := complete D hr hR hc hu v t counts freq
    have mem : (D,S) ∈ pairs := List.mem_flatMap.mpr ⟨(D,f),hf,
      List.mem_map.mpr ⟨S,by simp [sets],rfl⟩⟩
    exact ⟨(D,S),List.mem_filter.mpr ⟨mem,decide_eq_true replay⟩,hp⟩
  · intro e he
    exact of_decide_eq_true (List.mem_filter.mp he).2

end Lax977378Proofs.CheckedEntries
