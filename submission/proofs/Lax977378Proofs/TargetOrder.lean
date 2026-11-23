import Lax977378.TargetOrder
import Lax977378Proofs.MarkedSets
import Mathlib.Tactic

namespace Lax977378Proofs.TargetOrder
open Lax977378.Logic Lax977378.OuterContexts Lax977378.RecordTests Lax977378.Planting
open Lax977378.SourceTables Lax977378.TagSafety Lax977378.TableFacts Lax977378.MarkedSets
open Lax977378.CallAgreement

set_option maxHeartbeats 1000000

private theorem radiusMono : Monotone radius := monotone_nat_of_le_succ (by intro j; simp [radius])

/--
---
conclusion: Lax977378.TargetOrder.targetOrder
assumptions:
  - Lax977378.TableFacts.facts
  - Lax977378.MarkedSets.moveStages
  - Lax977378.LocalCover.coverCalls
  - Lax977378.CoverReplay.orderFromCover
---
Use a source vertex number only for vertices already exceptional at the
current stage. The target reads that number through its window name. Matching
full tags then isolates each endpoint in both graphs.
-/
theorem targetOrder {c d K q p} (W A B : Graph c) (ha : A.Bounded d) (hb : B.Bounded d)
    (a : LinearOrder (Fin A.size)) (T : Nat → Table A a)
    (next : ∀ j < K, Follows j (T j) (T (j+1)))
    (κ : Fin A.size → Fin q) (kB : Fin B.size → Fin q)
    (base : ∀ x y, (T 0).part.block x = (T 0).part.block y ↔ x = y ∨
      x ∉ (T 0).exceptions ∧ y ∉ (T 0).exceptions ∧ κ x = κ y ∧ ∀ i, A.pred i x ↔ A.pred i y)
    (sep : ∀ x, Function.Injective (fun u : Ball A K x => (T 0).part.block u.val))
    (mark : Finset (Fin W.size)) (y : Fin W.size → Fin A.size) (z : Fin W.size → Fin B.size)
    (wy : Window W A (radius K+p) mark y) (wz : Window W B (radius K+p) mark z)
    (named : mark.image y = (T K).exceptions)
    (col : ∀ j, (∃ m ∈ mark, within W (radius K) m j) → κ (y j) = kB (z j))
    (seeds : List (Request c q))
    (typesA : ∀ x ∉ (T K).exceptions, ∃ s ∈ seeds, Realised s A (radius K) κ x)
    (typesB : ∀ w ∉ mark.image z, ∃ s ∈ seeds, Realised s B (radius K) kB w)
    (copiesA : ∀ s ∈ seeds, ∃ x ∉ (T K).exceptions, Realised s A (radius K) κ x)
    (copiesB : ∀ s ∈ seeds, ∃ w ∉ mark.image z, Realised s B (radius K) kB w) :
    ∃ b, spectrumAgrees A B a b K := by
  classical
  let X j := (T j).exceptions
  let E j := endpoints (T (j-1))
  let Y j := moved y z (X j)
  let F j := moved y z (E j)
  have basePred x u (eq : (T 0).part.block x = (T 0).part.block u) :
      ∀ i, A.pred i x ↔ A.pred i u := by
    rcases (base _ _).mp eq with rfl | ⟨_,_,_,h⟩
    · exact fun _ => Iff.rfl
    · exact h
  obtain ⟨grows,endsIn,hom,separated⟩ := Lax977378.TableFacts.facts A ha a T next basePred sep
  have endSet j : E (j+1) = endpoints (T j) := rfl
  have covA : Lax977378.OrdinaryCalls.Covers A K X E := by
    intro j hj v hv x dist
    apply ((next j hj).1 x).mpr
    exact ⟨v,by simpa [X,endSet,endpoints,or_assoc] using hv,dist⟩
  have namedAll j (hj : j < K) : X j ∪ E (j+1) ⊆ mark.image y := by
    rw [named]
    exact Finset.union_subset (grows _ _ (by omega) le_rfl) ((endsIn _ hj).trans (grows _ _ hj le_rfl))
  have covB := Lax977378.MarkedSets.moveStages W A B mark y z wy wz X E covA namedAll
    (fun j hj => (radiusMono hj).trans (Nat.le_add_right _ _))
  have markB : mark.image z = Y K := by
    ext w
    rw [Finset.mem_image,show Y K = moved y z (X K) from rfl,MarkedSets.memMoved]
    constructor
    · rintro ⟨m,hm,rfl⟩; exact ⟨m,by change y m ∈ (T K).exceptions; rw [← named]; exact Finset.mem_image_of_mem _ hm,rfl⟩
    · rintro ⟨m,hm,rfl⟩
      change y m ∈ (T K).exceptions at hm
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp (named.symm ▸ hm)
      exact ⟨j,hj,congrArg z (wy.1.1 he)⟩
  let origin (w : Fin B.size) : Option (Fin A.size) :=
    if h : ∃ u, z u = w then some (y h.choose) else none
  have atName (u) : origin (z u) = some (y u) := by
    have h : ∃ j, z j = z u := ⟨u,rfl⟩
    simp only [origin,dif_pos h,wz.1.1 h.choose_spec]
  have originIff w x : origin w = some x ↔ ∃ u, z u = w ∧ y u = x := by
    constructor
    · dsimp [origin]; split
      · rename_i hh; intro e; exact ⟨_,hh.choose_spec,Option.some.inj e⟩
      · simp
    · rintro ⟨u,rfl,rfl⟩; exact atName u
  have movedIff (S : Finset (Fin A.size)) w :
      w ∈ moved y z S ↔ ∃ x ∈ S, origin w = some x := by
    rw [MarkedSets.memMoved]
    exact ⟨fun ⟨u,hu,hw⟩ => ⟨y u,hu,(originIff ..).mpr ⟨u,hw,rfl⟩⟩,
      fun ⟨x,hx,he⟩ => let ⟨u,hu,hy⟩ := (originIff ..).mp he; ⟨u,hy ▸ hx,hu⟩⟩
  let tag j (x : Fin A.size) := if x ∈ X j then some x else none
  let btag j w := (origin w).bind (tag j)
  have noTag j w (hw : w ∉ Y j) : btag j w = none := by
    cases eq : origin w with
    | none => simp [btag,eq]
    | some x =>
      have out : x ∉ X j := fun hx => hw ((movedIff ..).mpr ⟨x,hx,eq⟩)
      simp [btag,eq,tag,out]
  let Flags := Bool × Bool
  let flags j x : Flags := (decide (x = (T (j-1)).part.first ((T (j-1)).part.block x)),
    decide (x = (T (j-1)).part.last ((T (j-1)).part.block x)))
  let bf j w := (origin w).elim (false,false) (flags j)
  have interiorA j x (hx : x ∉ E (j+1)) : flags (j+1) x = (false,false) := by
    have h := hx
    simp [endSet,endpoints] at h
    simp [flags,Ne.symm (h.1 _),Ne.symm (h.2 _)]
  let Root := Option (Fin A.size) × (Fin c → Bool) × Fin q
  let encode (v : Root) := ((Fintype.equivFin Root) v).val
  have inject : Function.Injective encode := fun _ _ eq => (Fintype.equivFin Root).injective (Fin.ext eq)
  let en (v : Flags) := ((Fintype.equivFin Flags) v).val
  have finj : Function.Injective en := fun _ _ eq => (Fintype.equivFin Flags).injective (Fin.ext eq)
  let ra j x := encode (tag j x,fun i => decide (A.pred i x),κ x)
  let rb j w := encode (btag j w,fun i => decide (B.pred i w),kB w)
  let ea j x := en (flags j x)
  let eb j w := en (bf j w)
  let root j x w := ra j x = rb j w
  let ends j x w := ea j x = eb j w
  have inside j (_ : j ≤ K) u (near : ∃ m ∈ mark, within W (radius K) m u) :
      root j (y u) (z u) ∧ ends j (y u) (z u) := by
    have preds i := (wy.1.2.2 i u).symm.trans (wz.1.2.2 i u)
    simp [root,ra,rb,btag,atName,preds,col u near,ends,ea,eb,bf]
  have ordinary j (_ : j ≤ K) x (hx : x ∉ X j) w (hw : w ∉ Y j)
      (same : κ x = kB w ∧ ∀ i, A.pred i x ↔ B.pred i w) : root j x w := by
    simp [root,ra,rb,tag,hx,noTag j w hw,same.1,same.2]
  have inner j (_ : j < K) x (hx : x ∉ E (j+1)) w (hw : w ∉ F (j+1)) : ends (j+1) x w := by
    cases eq : origin w with
    | none => simp [ends,ea,eb,bf,eq,interiorA j x hx]
    | some u =>
      have hu : u ∉ E (j+1) := fun h => hw ((movedIff ..).mpr ⟨u,h,eq⟩)
      simp [ends,ea,eb,bf,eq,interiorA j x hx,interiorA j u hu]
  obtain ⟨fwd,back⟩ := Lax977378.LocalCover.coverCalls W A B mark y z wy wz X E Y F covA covB
    named markB κ kB root ends inside ordinary inner seeds typesA (markB ▸ typesB) copiesA (markB ▸ copiesB)
  have equalTag j x u (eq : ra j x = ra j u) : tag j x = tag j u :=
    congrArg Prod.fst (inject eq)
  have splitTag j x u (eq : tag j x = tag j u) : x = u ∨ x ∉ X j ∧ u ∉ X j := by
    by_cases hx : x ∈ X j <;> by_cases hu : u ∈ X j <;> simp_all [tag]
  refine Lax977378.CoverReplay.orderFromCover A B ha hb a (fun j => (T j).n) (fun j => (T j).part)
    ra ea rb eb fwd back ?_ ?_ ?_ hom ?_ ?_ separated ?_
  · intro x w eq i
    simpa using congrFun (congrArg (fun v : Root => v.2.1) (inject eq)) i
  · intro x u eq
    apply (base _ _).mpr
    rcases splitTag 0 x u (equalTag _ _ _ eq) with h | ⟨hx,hu⟩
    · exact Or.inl h
    · exact Or.inr ⟨hx,hu,congrArg (fun v : Root => v.2.2) (inject eq),
        fun i => by simpa using congrFun (congrArg (fun v : Root => v.2.1) (inject eq)) i⟩
  · intro j hj x u eq parent same
    apply ((next j hj).2 x u).mpr
    exact ⟨parent,(splitTag _ _ _ (equalTag _ _ _ eq)).imp_right (fun h => ⟨h.1,h.2,same⟩)⟩
  · intro j hj x u eq; exact (((next j hj).2 x u).mp eq).1
  · intro j hj t e he
    have endpoint : e ∈ endpoints (T j) := by
      rcases List.mem_cons.mp he with rfl | h
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))
      · obtain rfl := List.mem_singleton.mp h
        exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))
    have ex := endsIn j hj endpoint
    have final : e ∈ X K := grows _ _ hj le_rfl ex
    have nameE : tag K e = some e := by simp [tag,final]
    have recognise w (eq : rb K w = ra K e) : origin w = some e := by
      have h : btag K w = some e := (congrArg Prod.fst (inject eq)).trans nameE
      cases ho : origin w with
      | none => simp [btag,ho] at h
      | some u =>
        by_cases hu : u ∈ X K
        · simpa only [btag,ho,Option.bind_some,tag,if_pos hu] using h
        · simp only [btag,ho,Option.bind_some,tag,if_neg hu] at h
          cases h
    refine ⟨?_,?_,?_⟩
    · intro x eq
      rcases (((next j hj).2 x e).mp eq).2 with h | ⟨_,no,_⟩
      · exact h
      · exact False.elim (no ex)
    · intro x eq; exact (splitTag _ _ _ (equalTag _ _ _ eq)).resolve_right (fun h => h.2 final)
    · intro w v hw hv
      obtain ⟨i,hi,hy⟩ := (originIff ..).mp (recognise w hw)
      obtain ⟨l,hl,hz⟩ := (originIff ..).mp (recognise v hv)
      exact hi.symm.trans ((congrArg z (wy.1.1 (hy.trans hz.symm))).trans hl)
  · intro j hj x u eq
    have h := finj eq
    exact ⟨by simpa [flags] using congrArg Prod.fst h,by simpa [flags] using congrArg Prod.snd h⟩

end Lax977378Proofs.TargetOrder
