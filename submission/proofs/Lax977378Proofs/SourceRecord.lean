import Lax977378.SourceRecord
import Lax977378Proofs.Catalogue

namespace Lax977378Proofs.SourceRecord
open Lax977378.Logic Lax977378.SourceTables Lax977378.SourceRun Lax977378.Planting
open Lax977378.RecordTests Lax977378.CountParameters

/--
---
conclusion: Lax977378.SourceRecord.sourceRecord
assumptions:
  - Lax977378.ColouredRun.colouredRun
  - Lax977378.SourceTables.sourceTables
  - Lax977378.Extraction.extract
---
Extract the window only after the final source order and all its tables have
been obtained. Monotonicity of the exceptional sets places every rare vertex
in that window, with the very same names as in the existential test.
-/
theorem sourceRecord (c d K : Nat) : ∃ N : Nat → Nat,
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
        D.marked.image y = (T K).exceptions ∧ D.rare.image y = Z) ∧ Passes D G := by
  obtain ⟨N,run⟩ := Lax977378.ColouredRun.colouredRun c d K
  refine ⟨N,?_⟩
  intro G hd q κ proper n types r R cap t v counts Z
  obtain ⟨I,L,hI,rows,hist,_,onto,_,bound⟩ := run G hd q κ proper Z
  obtain ⟨a,T,base,top,next⟩ := Lax977378.SourceTables.sourceTables G I L hist onto
  have baseZ : (T 0).exceptions = Z := (congrArg Layer.exceptions base).trans hI
  have topBound : (T K).exceptions.card ≤ limit d N (Z.card + 2^c*q) K := by
    change (T K).layer.exceptions.card ≤ _
    rw [top]; exact bound
  have rareIn (j) (hj : j ≤ K) : Z ⊆ (T j).exceptions := by
    induction j with
    | zero => exact baseZ ▸ Finset.Subset.rfl
    | succ j ih =>
      intro x hx
      exact ((next j (by omega)).1 x).mpr
        ⟨x,Or.inl (ih (by omega) hx),Catalogue.centerWithin ..⟩
  obtain ⟨D,hr,hR,hcap,hv,hfreq,hs,hw,pass,_⟩ :=
    Lax977378.Extraction.extract G hd r R cap t types (T K).exceptions v counts (rareIn K le_rfl)
  refine ⟨a,T,D,baseZ,?_,next,topBound,hr,hR,hcap,hv,hfreq,
    hs.trans (Nat.mul_le_mul_right _ topBound),hw,pass⟩
  intro x y
  change (T 0).layer.row x = (T 0).layer.row y ↔ _
  rw [base]
  exact rows x y

end Lax977378Proofs.SourceRecord
