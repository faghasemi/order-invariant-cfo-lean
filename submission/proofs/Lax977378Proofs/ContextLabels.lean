import Lax977378.ContextLabels
import Lax977378Proofs.Catalogue

namespace Lax977378Proofs.ContextLabels
open Lax977378.Logic Lax977378.OuterContexts

-- For each named ball vertex these two bits place z to its left, at it or to its right.
private abbrev Cut (n : Nat) := Fin n → Bool × Bool
private abbrev Signature (n N : Nat) :=
  (Fin n → Bool) × (Fin n → Fin n → Bool) × (Fin n → Fin n → Bool) ×
  (Fin n → Fin N) × Set (Fin N × Cut n)

private noncomputable def cut {c r n} {G : Graph c} {x : Fin G.size}
    (a : LinearOrder (Fin G.size)) (e : Fin n ≃ Ball G r x) (z : Fin G.size) :
    Cut n := by
  classical exact fun j => (decide (a.lt z (e j).val), decide (a.lt (e j).val z))

private noncomputable def signature {c r n N} {G : Graph c} {x : Fin G.size}
    (a : LinearOrder (Fin G.size)) (lab : Fin G.size → Fin N) (e : Fin n ≃ Ball G r x) :
    Signature n N := by
  classical exact (fun j => decide ((e j).val = x),
    fun j k => decide (G.edge (e j).val (e k).val),
    fun j k => decide (a.lt (e j).val (e k).val),
    fun j => lab (e j).val,
    Set.range (fun z => (lab z, cut a e z)))

private theorem cuts {c r n} {A B : Graph c} {x : Fin A.size} {y : Fin B.size}
    (a : LinearOrder (Fin A.size)) (b : LinearOrder (Fin B.size))
    (e : Fin n ≃ Ball A r x) (f : Fin n ≃ Ball B r y) (z w) :
    cut a e z = cut b f w ↔ ∀ j,
      (a.lt z (e j).val ↔ b.lt w (f j).val) ∧
      (a.lt (e j).val z ↔ b.lt (f j).val w) := by
  classical simp [cut, funext_iff, Prod.mk.injEq]

private theorem signatureEq {c i n N} {A B : Graph c} {a : LinearOrder (Fin A.size)}
    {b : LinearOrder (Fin B.size)} {x y} (L : Fin A.size → Fin N) (M : Fin B.size → Fin N)
    (lower : ∀ z w, L z = M w ↔ same A B a b i z w)
    (e : Fin n ≃ Ball A (i+1) x) (f : Fin n ≃ Ball B (i+1) y) :
    signature a L e = signature b M f ↔
    (∀ j, (e j).val = x ↔ (f j).val = y) ∧
    (∀ j k, A.edge (e j).val (e k).val ↔ B.edge (f j).val (f k).val) ∧
    (∀ j k, a.lt (e j).val (e k).val ↔ b.lt (f j).val (f k).val) ∧
    (∀ j, same A B a b i (e j).val (f j).val) ∧
    (∀ z, ∃ w, same A B a b i z w ∧ cut a e z = cut b f w) ∧
    (∀ w, ∃ z, same A B a b i z w ∧ cut a e z = cut b f w) := by
  classical
  simp only [signature, Prod.mk.injEq, funext_iff, decide_eq_decide, lower]
  iterate 4 (apply and_congr_right; intro _)
  rw [Set.Subset.antisymm_iff]
  constructor
  · rintro ⟨forward,back⟩
    constructor
    · intro z
      obtain ⟨w, hw⟩ := forward (Set.mem_range_self z)
      exact ⟨w, (lower _ _).mp (congrArg Prod.fst hw.symm), congrFun (congrArg Prod.snd hw.symm)⟩
    · intro w
      obtain ⟨z,hz⟩ := back (Set.mem_range_self w)
      exact ⟨z,(lower _ _).mp (congrArg Prod.fst hz),congrFun (congrArg Prod.snd hz)⟩
  · rintro ⟨forward,back⟩
    constructor
    · rintro _ ⟨z,rfl⟩
      obtain ⟨w,h,hc⟩ := forward z
      exact ⟨w, Prod.ext ((lower _ _).mpr h).symm (funext hc).symm⟩
    · rintro _ ⟨w,rfl⟩
      obtain ⟨z,h,hc⟩ := back w
      exact ⟨z, Prod.ext ((lower _ _).mpr h) (funext hc)⟩

private theorem transport {c i n N} {A B : Graph c} {a : LinearOrder (Fin A.size)}
    {b : LinearOrder (Fin B.size)} {x y} (L : Fin A.size → Fin N) (M : Fin B.size → Fin N)
    (lower : ∀ z w, L z = M w ↔ same A B a b i z w)
    (h : same A B a b (i+1) x y) :
    (∀ e : Fin n ≃ Ball A (i+1) x, ∃ f : Fin n ≃ Ball B (i+1) y,
      signature a L e = signature b M f) ∧
    (∀ f : Fin n ≃ Ball B (i+1) y, ∃ e : Fin n ≃ Ball A (i+1) x,
      signature a L e = signature b M f) := by
  obtain ⟨iso,root,edges,order,labels,forward,back⟩ := h
  have matched (e : Fin n ≃ Ball A (i+1) x) (f : Fin n ≃ Ball B (i+1) y)
      (he : ∀ j, iso (e j) = f j) : signature a L e = signature b M f := by
    apply (signatureEq L M lower e f).mpr
    refine ⟨fun j => by simpa only [← he] using root (e j),
      fun j k => by simpa only [← he] using edges (e j) (e k),
      fun j k => by simpa only [← he] using order (e j) (e k),
      fun j => by simpa only [← he] using labels (e j), ?_, ?_⟩
    · intro z
      obtain ⟨w,hw,hs⟩ := forward z
      exact ⟨w,hw,(cuts ..).mpr (fun j => by simpa only [← he] using hs (e j))⟩
    · intro w
      obtain ⟨z,hz,hs⟩ := back w
      exact ⟨z,hz,(cuts ..).mpr (fun j => by simpa only [← he] using hs (e j))⟩
  exact ⟨fun e => ⟨e.trans iso, matched _ _ (fun _ => rfl)⟩,
    fun f => ⟨f.trans iso.symm,matched _ _ (by simp)⟩⟩

private theorem agree {c i n N} {A B : Graph c} {a : LinearOrder (Fin A.size)}
    {b : LinearOrder (Fin B.size)} {x y} (L : Fin A.size → Fin N) (M : Fin B.size → Fin N)
    (lower : ∀ z w, L z = M w ↔ same A B a b i z w)
    (e : Fin n ≃ Ball A (i+1) x) (f : Fin n ≃ Ball B (i+1) y)
    (h : signature a L e = signature b M f) : same A B a b (i+1) x y := by
  obtain ⟨hr,hed,ho,hl,hf,hb⟩ := (signatureEq L M lower e f).mp h
  refine ⟨e.symm.trans f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u; simpa using hr (e.symm u)
  · intro u v; simpa using hed (e.symm u) (e.symm v)
  · intro u v; simpa using ho (e.symm u) (e.symm v)
  · intro u; simpa using hl (e.symm u)
  · intro z
    obtain ⟨w,hw,hc⟩ := hf z
    exact ⟨w,hw,fun u => by simpa using (cuts ..).mp hc (e.symm u)⟩
  · intro w
    obtain ⟨z,hz,hc⟩ := hb w
    exact ⟨z,hz,fun u => by simpa using (cuts ..).mp hc (e.symm u)⟩

private abbrev Shapes (bound N : Nat) := (n : Fin (bound+1)) × Signature n.val N

private def shapes {c r N : Nat} (bound : Nat) {G : Graph c} (a : LinearOrder (Fin G.size))
    (lab : Fin G.size → Fin N) (x : Fin G.size) : Set (Shapes bound N) :=
  fun s => ∃ e : Fin s.1.val ≃ Ball G r x, s.2 = signature a lab e

/--
---
conclusion: Lax977378.ContextLabels.finiteLabels
---
Record all numberings of the rooted ball. Alongside the ball, each numbering
records the set of lower labels and order positions realised in the graph.
Transporting a numbering along a context isomorphism preserves these data.
Conversely a common numbered description supplies the required isomorphism.
-/
theorem finiteLabels (c d i : Nat) :
    ∃ N : Nat, ∃ label : (G : Graph c) → G.Bounded d →
        LinearOrder (Fin G.size) → Fin G.size → Fin N,
      ∀ A B ha hb a b x y, label A ha a x = label B hb b y ↔ same A B a b i x y := by
  classical
  induction i with
  | zero =>
    let enc := Fintype.equivFin (Fin c → Bool)
    refine ⟨_,fun G _ _ x => enc (fun p => decide (G.pred p x)),?_⟩
    intro A B _ _ a b x y
    simp [enc.injective.eq_iff,funext_iff,same]
  | succ i ih =>
    obtain ⟨N,lab,lower⟩ := ih
    let bound := (d+1)^(i+1)
    let enc := Fintype.equivFin (Set (Shapes bound N))
    refine ⟨_,fun G hd a x => enc (shapes (r := i+1) bound a (lab G hd a) x),?_⟩
    intro A B ha hb a b x y
    rw [enc.injective.eq_iff]
    constructor
    · intro h
      let S := Catalogue.ball A (i+1) x
      let n : Fin (bound+1) := ⟨S.card, Nat.lt_succ_of_le (Catalogue.ballCard A d ha _ x)⟩
      let u : S ≃ Ball A (i+1) x := Equiv.subtypeEquivRight (fun z => Catalogue.mem_ball A _ x z)
      let e : Fin n.val ≃ Ball A (i+1) x := S.equivFin.symm.trans u
      let s : Shapes bound N := ⟨n, signature a (lab A ha a) e⟩
      have hs : s ∈ shapes (r := i+1) bound a (lab A ha a) x := ⟨e,rfl⟩
      rw [h] at hs
      obtain ⟨f,hf⟩ := hs
      exact agree _ _ (lower A B ha hb a b) e f hf
    · intro h
      ext s
      obtain ⟨hf,hb'⟩ := transport (n := s.1.val) _ _ (lower A B ha hb a b) h
      exact ⟨fun ⟨e,he⟩ => let ⟨f,hf'⟩ := hf e; ⟨f,he.trans hf'⟩,
        fun ⟨f,hg⟩ => let ⟨e,he⟩ := hb' f; ⟨e,hg.trans he.symm⟩⟩

end Lax977378Proofs.ContextLabels
