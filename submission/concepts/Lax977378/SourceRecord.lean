import Lax977378.SourceTables
import Lax977378.ColouredRun
import Lax977378.Extraction

/-!
---
title: A source graph yields its bounded record and final order
type: lemma
---
Given the threshold vector and a proper auxiliary colouring, produce all
source tables, their common order, and the unordered test of the actual
window around the final exceptional set. All size estimates are independent
of the source graph except through its initial number of rare vertices.
-/
namespace Lax977378.SourceRecord
open Lax977378.Logic Lax977378.SourceTables Lax977378.SourceRun Lax977378.Planting
open Lax977378.RecordTests Lax977378.CountParameters

axiom sourceRecord (c d K : Nat) : ∃ N : Nat → Nat,
    ∀ (G : Graph c), G.Bounded d → ∀ (q : Nat) (κ : Fin G.size → Fin q),
    ProperOn G (K+K) Finset.univ κ →
    ∀ {n} (types : Fin n → Pointed c) (r R cap t : Nat) (v : Fin n → Nat),
    (∀ j, v j = min cap (locations (types j) r G).card) →
    let Z := rareSet types r G v t
    ∃ (a : LinearOrder (Fin G.size)) (T : Nat → Table G a) (D : TestData c),
      (T 0).exceptions = Z ∧
      (∀ x y, (T 0).part.block x = (T 0).part.block y ↔ x = y ∨
        x ∉ Z ∧ y ∉ Z ∧ κ x = κ y ∧ ∀ p, G.pred p x ↔ G.pred p y) ∧
      (∀ j < K, Follows j (T j) (T (j+1))) ∧
      (T K).exceptions.card ≤ limit d N (Z.card + 2^c*q) K ∧
      D.radius = r ∧ D.windowRadius = R ∧ D.cap = cap ∧
      D.counts = List.ofFn (fun j => (types j,v j)) ∧
      D.frequent = ((List.finRange n).filter (fun j => t ≤ v j)).map types ∧
      D.windowGraph.size ≤ limit d N (Z.card + 2^c*q) K * (d+1)^R ∧
      (∃ y, Window D.windowGraph G R D.marked y ∧
        D.marked.image y = (T K).exceptions ∧ D.rare.image y = Z) ∧ Passes D G

end Lax977378.SourceRecord
