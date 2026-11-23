import Lax977378.Extraction
import Lax977378Proofs.Catalogue

namespace Lax977378Proofs.Extraction
open Lax977378.Logic Lax977378.RecordTests Lax977378.CountParameters Lax977378Proofs.Catalogue

/--
---
conclusion: Lax977378.Extraction.extract
assumptions:
  - Lax977378.CountParameters.countTestValue
  - Lax977378.RecordTests.recordTest
---
Enumerate the union of the marked balls and pull the graph relations back
along the enumeration. Its inverse names exactly the marked and rare vertices.
-/
theorem extract {c d n} (G : Graph c) (hd : G.Bounded d) (r R cap t : Nat)
    (types : Fin n → Pointed c) (M : Finset (Fin G.size))
    (v : Fin n → Nat) (counts : ∀ j, v j = min cap (locations (types j) r G).card)
    (contains : rareSet types r G v t ⊆ M) :
    ∃ D : TestData c, D.radius = r ∧ D.windowRadius = R ∧ D.cap = cap ∧
      D.counts = List.ofFn (fun j => (types j,v j)) ∧
      D.frequent = ((List.finRange n).filter (fun j => t ≤ v j)).map types ∧
      D.windowGraph.size ≤ M.card * (d+1)^R ∧
      (∃ y, Window D.windowGraph G R D.marked y ∧ D.marked.image y = M ∧
        D.rare.image y = rareSet types r G v t) ∧ Passes D G ∧
      ∃ f, Plain [] f ∧ Unordered G f ∧ ∀ B, Unordered B f ↔ Passes D B := by
  classical
  let S := M.biUnion (ball G R)
  let y (i : Fin S.card) := (S.equivFin.symm i).val
  have members (x) : x ∈ S ↔ ∃ u ∈ M, Lax977378.OuterContexts.within G R u x := by simp [S]
  have sub : M ⊆ S := fun x hx => (members x).mpr ⟨x,hx,centerWithin ..⟩
  have range (x) : (∃ i, y i = x) ↔ x ∈ S :=
    ⟨fun ⟨i,hi⟩ => hi ▸ (S.equivFin.symm i).property,
      fun hx => ⟨S.equivFin ⟨x,hx⟩,by simp [y]⟩⟩
  let W : Graph c := ⟨S.card,fun i j => G.edge (y i) (y j),
    fun i j => G.symm _ _,fun i => G.loopless _,fun p i => G.pred p (y i)⟩
  let names (U : Finset (Fin G.size)) := Finset.univ.filter (fun i => y i ∈ U)
  have imageNames (U) (hu : U ⊆ S) : (names U).image y = U := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hi).2
    · intro hx
      obtain ⟨i,hi⟩ := (range x).mpr (hu hx)
      exact Finset.mem_image.mpr ⟨i,by simp [names,hi,hx],hi⟩
  have win : Window W G R (names M) y := by
    refine ⟨⟨fun i j e => S.equivFin.symm.injective (Subtype.ext e),fun _ _ => Iff.rfl,fun _ _ => Iff.rfl⟩,?_⟩
    intro x
    rw [range,members]
    constructor
    · rintro ⟨u,hu,h⟩
      obtain ⟨j,rfl⟩ := (range u).mpr (sub hu)
      exact ⟨j,by simp [names,hu],h⟩
    · rintro ⟨j,hj,h⟩
      exact ⟨_,(Finset.mem_filter.mp hj).2,h⟩
  let D : TestData c := ⟨r,R,W,names M,names (rareSet types r G v t),cap,
    List.ofFn (fun j => (types j,v j)),((List.finRange n).filter (fun j => t ≤ v j)).map types⟩
  have rare := imageNames _ (contains.trans sub)
  have pass : Passes D G := by
    refine ⟨?_,y,win,?_⟩
    · intro tv h
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp h
      exact (Lax977378.CountParameters.countTestValue ..).mpr (counts j)
    · intro x
      change (∃ i ∈ names _, y i = x) ↔ _
      rw [← Finset.mem_image,rare]
      simp [rareSet,D]
  obtain ⟨f,hf,sat⟩ := Lax977378.RecordTests.recordTest D
  refine ⟨D,rfl,rfl,rfl,rfl,rfl,?_,⟨y,win,imageNames M sub,rare⟩,pass,f,hf,(sat G).mpr pass,sat⟩
  calc
    S.card ≤ ∑ u ∈ M, (ball G R u).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ M, (d+1)^R := by gcongr with u; exact ballCard G d hd R u
    _ = _ := by simp

end Lax977378Proofs.Extraction
