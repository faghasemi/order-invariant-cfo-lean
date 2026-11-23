import Lax977378.SourceRecord

/-!
---
title: Recovering the target exceptional vertices from one successful test
type: lemma
---
The same unordered record identifies the exact low counts, the target rare
vertices, and a bijection between the source and target marked sets. Every
bounded-degree count threshold used for the source remains valid in the target.
-/
namespace Lax977378.TargetWindow
open Lax977378.Logic Lax977378.RecordTests Lax977378.CountParameters

axiom targetWindow {c n} (A B : Graph c) (D : TestData c) (types : Fin n → Pointed c)
    (v : Fin n → Nat) (t : Nat) (tcap : t ≤ D.cap)
    (counts : D.counts = List.ofFn (fun j => (types j,v j)))
    (freq : D.frequent = ((List.finRange n).filter (fun j => t ≤ v j)).map types)
    (y : Fin D.windowGraph.size → Fin A.size) (wy : Window D.windowGraph A D.windowRadius D.marked y)
    (pass : Passes D B) :
    (∀ j, v j = min D.cap (locations (types j) D.radius B).card) ∧
    (∀ j, t ≤ v j ↔ t ≤ (locations (types j) D.radius B).card) ∧
    ∃ z, Window D.windowGraph B D.windowRadius D.marked z ∧
      D.rare.image z = rareSet types D.radius B v t ∧
      ∃ e : (D.marked.image z) ≃ (D.marked.image y),
        ∀ j (hj : j ∈ D.marked), (e ⟨z j, Finset.mem_image_of_mem _ hj⟩).val = y j

end Lax977378.TargetWindow
