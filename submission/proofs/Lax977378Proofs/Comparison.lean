import Lax977378.Collapse
import Mathlib.Tactic

namespace Lax977378Proofs.Comparison
open Lax977378.Logic Lax977378.OuterContexts

private theorem centerWithin {c : Nat} (G : Graph c) (r : Nat) (x : Fin G.size) :
    within G r x x := by
  induction r with
  | zero => rfl
  | succ i ih => exact Or.inl ih

private theorem grow {c : Nat} {G : Graph c} {r s : Nat} {x y : Fin G.size}
    (h : within G r x y) (hrs : r ≤ s) : within G s x y := by
  induction s, hrs using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact Or.inl ih

private structure Box {c : Nat} (A B : Graph c) (a : LinearOrder (Fin A.size))
    (b : LinearOrder (Fin B.size)) where
  r : Nat
  x : Fin A.size
  y : Fin B.size
  iso : Ball A r x ≃ Ball B r y
  center : ∀ u, u.val = x ↔ (iso u).val = y
  edge : ∀ u v, A.edge u.val v.val ↔ B.edge (iso u).val (iso v).val
  order : ∀ u v, a.lt u.val v.val ↔ b.lt (iso u).val (iso v).val
  pred : ∀ u p, A.pred p u.val ↔ B.pred p (iso u).val
  next : ∀ j, r = j+1 →
    let matchAt := fun z w => same A B a b j z w ∧ ∀ u,
      (a.lt z u.val ↔ b.lt w (iso u).val) ∧ (a.lt u.val z ↔ b.lt (iso u).val w)
    (∀ z, ∃ w, matchAt z w) ∧ (∀ w, ∃ z, matchAt z w)

private theorem samePred {c : Nat} {A B : Graph c} {a : LinearOrder (Fin A.size)}
    {b : LinearOrder (Fin B.size)} {r : Nat} {x y} (hs : same A B a b r x y) :
    ∀ p, A.pred p x ↔ B.pred p y := by
  induction r generalizing x y with
  | zero => exact hs
  | succ i ih =>
    obtain ⟨h, cent, _, _, lower, _⟩ := hs
    let u : Ball A (i+1) x := ⟨x, centerWithin A _ x⟩
    have hy : (h u).val = y := (cent u).mp rfl
    simpa only [hy] using ih (lower u)

private theorem makeBox {c : Nat} {A B : Graph c} {a : LinearOrder (Fin A.size)}
    {b : LinearOrder (Fin B.size)} {r : Nat} {x y} (hs : same A B a b r x y) :
    ∃ F : Box A B a b, F.r = r ∧ F.x = x ∧ F.y = y := by
  cases r with
  | zero =>
    let e : Ball A 0 x ≃ Ball B 0 y :=
      ⟨fun _ => ⟨y, rfl⟩, fun _ => ⟨x, rfl⟩,
       fun u => Subtype.ext (show x = u.val from u.property),
       fun v => Subtype.ext (show y = v.val from v.property)⟩
    refine ⟨⟨0,x,y,e,?_,?_,?_,?_,?_⟩,rfl,rfl,rfl⟩
    · intro u; exact iff_of_true (Eq.symm u.property) rfl
    · intro u v
      have hu : x = u.val := u.property
      have hv : x = v.val := v.property
      exact iff_of_false (by rw [← hu, ← hv]; exact A.loopless x) (B.loopless y)
    · intro u v
      have hu : x = u.val := u.property
      have hv : x = v.val := v.property
      exact iff_of_false (by rw [← hu, ← hv]; exact @lt_irrefl _ a.toPreorder x)
        (@lt_irrefl _ b.toPreorder y)
    · intro u p
      have hu : x = u.val := u.property
      exact hu ▸ hs p
    · intro j h; omega
  | succ i =>
    obtain ⟨h, cent, edge, ord, lower, rest⟩ := hs
    refine ⟨⟨i+1,x,y,h,cent,edge,ord,fun u => samePred (lower u),?_⟩,rfl,rfl,rfl⟩
    intro j hj
    cases Nat.succ.inj hj
    exact rest

private def side {X Y : Type} (a : LinearOrder X) (b : LinearOrder Y)
    (x : X) (y : Y) (u : X) (v : Y) : Prop :=
  (a.lt x u ↔ b.lt y v) ∧ (a.lt u x ↔ b.lt v y)

private theorem sideEq {X Y : Type} {a : LinearOrder X} {b : LinearOrder Y}
    {x u : X} {y v : Y} (h : side a b x y u v) : x = u ↔ y = v := by
  let := a
  let := b
  exact ⟨fun e => le_antisymm (le_of_not_gt (fun hh => (ne_of_gt (h.2.mpr hh)) e))
      (le_of_not_gt (fun hh => (ne_of_lt (h.1.mpr hh)) e)),
    fun e => le_antisymm (le_of_not_gt (fun hh => (ne_of_gt (h.2.mp hh)) e))
      (le_of_not_gt (fun hh => (ne_of_lt (h.1.mp hh)) e))⟩


private abbrev Env (n : Nat) := Var → Option (Fin n)
private def put {n : Nat} (env : Env n) (v : Var) (x : Fin n) : Env n :=
  fun z => if z = v then some x else env z

private def Roots (S : List Var) : Prop :=
  (∀ v ∈ S, (v.1,0) ∈ S) ∧ (∀ w a, child w a ∈ S → (w,0) ∈ S)

private theorem child_inj {u v : List Nat} {i j : Nat} (h : child u i = child v j) :
    u = v ∧ i = j := by
  have h' : u ++ [i] = v ++ [j] := congrArg Prod.fst h
  have hl := congrArg List.length h'
  simp at hl
  simpa using List.append_inj h' hl

private theorem rootsAdd {S : List Var} (hs : Roots S) {z : Var}
    (own : (z.1,0) ∈ z :: S) (parent : ∀ w a, z = child w a → (w,0) ∈ S) :
    Roots (z :: S) := by
  constructor
  · intro v hv; rcases List.mem_cons.mp hv with rfl | h
    · exact own
    · exact List.mem_cons_of_mem _ (hs.1 _ h)
  · intro w a hv
    rcases List.mem_cons.mp hv with h | h
    · exact List.mem_cons_of_mem _ (parent _ _ h.symm)
    · exact List.mem_cons_of_mem _ (hs.2 _ _ h)

section Positions
variable {c : Nat} {A B : Graph c} {a : LinearOrder (Fin A.size)}
  {b : LinearOrder (Fin B.size)}

private def Local (F : Box A B a b) (n : Nat) (x : Fin A.size) (y : Fin B.size) : Prop :=
  ∃ u : Ball A F.r F.x, u.val = x ∧ (F.iso u).val = y ∧
    ∃ t, t+n ≤ F.r ∧ within A t F.x x ∧ within B t F.y y

private def Profile (F : Box A B a b) (x : Fin A.size) (y : Fin B.size) : Prop :=
  ∀ u : Ball A F.r F.x, side a b x y u.val (F.iso u).val

private def At (ea : Env A.size) (eb : Env B.size) (z : Var)
    (R : Fin A.size → Fin B.size → Prop) : Prop :=
  ∃ x y, ea z = some x ∧ eb z = some y ∧ R x y

private structure Track (F : Box A B a b) (w : List Nat) (S : List Var)
    (ea : Env A.size) (eb : Env B.size) (n : Nat) : Prop where
  room : n ≤ F.r
  localAt : ∀ i, (w,i) ∈ S → At ea eb (w,i) (Local F n)
  childAt : ∀ j, child w j ∈ S → At ea eb (child w j) (Profile F)

private abbrev Pos (S : List Var) (ea : Env A.size) (eb : Env B.size) (n : Nat) :=
  ∀ w, (w,0) ∈ S → ∃ F : Box A B a b, Track F w S ea eb n

private theorem centerLocal (F : Box A B a b) {n} (hn : n ≤ F.r) :
    Local F n F.x F.y := by
  let u : Ball A F.r F.x := ⟨F.x, centerWithin _ _ _⟩
  exact ⟨u, rfl, (F.center u).mp rfl, 0, by omega, rfl, rfl⟩

private theorem extendTrack (F : Box A B a b) {w S ea eb n} (old : Track F w S ea eb (n+1))
    {z x y} (fresh : z ∉ S) (hl : z.1 = w → Local F n x y)
    (hc : ∀ j, z = child w j → Profile F x y) :
    Track F w (z :: S) (put ea z x) (put eb z y) n := by
  refine ⟨by have := old.room; omega, ?_, ?_⟩
  · intro i hi
    rcases List.mem_cons.mp hi with he | he
    · exact ⟨x,y,by simp [put,he],by simp [put,he],hl (by rw [← he])⟩
    · obtain ⟨u,v,hu,hv,p,hp,hq,t,ht,ha,hb⟩ := old.localAt i he
      have hne : (w,i) ≠ z := fun e => fresh (e ▸ he)
      exact ⟨u,v,by simpa [put,hne] using hu,by simpa [put,hne] using hv,
        p,hp,hq,t,by omega,ha,hb⟩
  · intro j hj
    rcases List.mem_cons.mp hj with he | he
    · exact ⟨x,y,by simp [put,he],by simp [put,he],hc _ he.symm⟩
    · obtain ⟨u,v,hu,hv,pr⟩ := old.childAt j he
      have hne : child w j ≠ z := fun e => fresh (e ▸ he)
      exact ⟨u,v,by simpa [put,hne] using hu,by simpa [put,hne] using hv,pr⟩

private theorem newTrack {w S ea eb n} (hs : Roots S) (fresh : (w,0) ∉ S)
    (F : Box A B a b) (hn : n ≤ F.r) :
    Track F w ((w,0) :: S) (put ea (w,0) F.x) (put eb (w,0) F.y) n := by
  refine ⟨hn, ?_, ?_⟩
  · intro i hi
    rcases List.mem_cons.mp hi with h | h
    · exact ⟨_,_,by simp [put,h],by simp [put,h],centerLocal F hn⟩
    · exact False.elim (fresh (hs.1 _ h))
  · intro j hj
    rcases List.mem_cons.mp hj with h | h
    · have e := congrArg (fun (z : Var) => z.1.length) h
      simp [child] at e
    · exact False.elim (fresh (hs.2 w j h))

private theorem fromA (F : Box A B a b) {n u v} (hu : Local F (n+1) u v)
    {x} (hx : A.edge x u) : ∃ y, B.edge y v ∧ Local F n x y := by
  obtain ⟨i,rfl,rfl,t,ht,hu,hv⟩ := hu
  have hdist : within A (t+1) F.x x := Or.inr ⟨_,hu,A.symm _ _ hx⟩
  let j : Ball A F.r F.x := ⟨x,grow hdist (by omega)⟩
  have edge := (F.edge j i).mp hx
  exact ⟨_, edge, j, rfl,rfl,t+1,by omega,hdist,Or.inr ⟨_,hv,B.symm _ _ edge⟩⟩

private theorem fromB (F : Box A B a b) {n u v} (hu : Local F (n+1) u v)
    {y} (hy : B.edge y v) : ∃ x, A.edge x u ∧ Local F n x y := by
  obtain ⟨i,rfl,rfl,t,ht,hu,hv⟩ := hu
  have hdist : within B (t+1) F.y y := Or.inr ⟨_,hv,B.symm _ _ hy⟩
  let j : Ball B F.r F.y := ⟨y,grow hdist (by omega)⟩
  have hj : (F.iso (F.iso.symm j)).val = y := congrArg Subtype.val (F.iso.apply_symm_apply j)
  have edge := (F.edge (F.iso.symm j) i).mpr (by rwa [hj])
  exact ⟨_,edge,F.iso.symm j,rfl,hj,t+1,by omega,Or.inr ⟨_,hu,A.symm _ _ edge⟩,hdist⟩

private theorem addCont {S ea eb n w i x y} (pos : Pos (a:=a) (b:=b) S ea eb (n+1))
    (F : Box A B a b) (state : Track F w S ea eb (n+1)) (fresh : (w,i) ∉ S)
    (hi : 0 < i) (hxy : Local F n x y) :
    Pos (a:=a) (b:=b) ((w,i) :: S) (put ea (w,i) x) (put eb (w,i) y) n := by
  intro v hv
  have hc : ∀ (u : List Nat) j, (w,i) ≠ child u j := by
    intro u j h; have := congrArg Prod.snd h; simp [child] at this; omega
  by_cases he : v = w
  · subst v; exact ⟨F,extendTrack F state fresh (fun _ => hxy) (fun j h => (hc _ j h).elim)⟩
  · have hmem : (v,0) ∈ S := by
      rcases List.mem_cons.mp hv with h | h
      · exact (he (congrArg Prod.fst h)).elim
      · exact h
    obtain ⟨F',hf⟩ := pos v hmem
    exact ⟨F',extendTrack F' hf fresh (fun h => (he h.symm).elim) (fun j h => (hc _ j h).elim)⟩

private theorem addChild {S ea eb n w j x y}
    (pos : Pos (a:=a) (b:=b) S ea eb (n+1)) (hs : Roots S)
    (F : Box A B a b) (state : Track F w S ea eb (n+1))
    (fresh : child w j ∉ S) (pr : Profile F x y)
    (newF : Box A B a b) (hn : n ≤ newF.r) (hx : newF.x = x) (hy : newF.y = y) :
    Pos (a:=a) (b:=b) (child w j :: S) (put ea (child w j) x) (put eb (child w j) y) n := by
  subst x; subst y
  intro v hv
  by_cases hnew : v = (child w j).1
  · subst v; exact ⟨newF,newTrack hs fresh newF hn⟩
  · have hmem : (v,0) ∈ S := by
      rcases List.mem_cons.mp hv with h | h
      · exact (hnew (congrArg Prod.fst h)).elim
      · exact h
    by_cases he : v = w
    · subst v; exact ⟨F,extendTrack F state fresh (fun h => (hnew h.symm).elim) (fun _ _ => pr)⟩
    · obtain ⟨G,hg⟩ := pos v hmem
      exact ⟨G,extendTrack G hg fresh (fun h => (hnew h.symm).elim)
        (fun _ h => (he (child_inj h).1.symm).elim)⟩

private theorem rootPos {ea : Env A.size} {eb : Env B.size} {n} (F : Box A B a b)
    (hn : n ≤ F.r) : Pos (a:=a) (b:=b) [root] (put ea root F.x) (put eb root F.y) n := by
  intro w hw
  have he : w = [] := congrArg Prod.fst (List.mem_singleton.mp hw)
  subst w
  exact ⟨F,newTrack (S:=[]) (by simp [Roots]) (by simp) F hn⟩

private theorem sameCluster {S ea eb n w i j}
    (pos : Pos (a:=a) (b:=b) S ea eb n) (hs : Roots S)
    (hi : (w,i) ∈ S) (hj : (w,j) ∈ S) :
    ∃ x y u v, ea (w,i) = some x ∧ eb (w,i) = some y ∧
      ea (w,j) = some u ∧ eb (w,j) = some v ∧
      side a b x y u v ∧ (A.edge x u ↔ B.edge y v) ∧ (∀ p, A.pred p x ↔ B.pred p y) := by
  obtain ⟨F,hF⟩ := pos w (hs.1 _ hi)
  obtain ⟨_,_,hx,hy,z,rfl,rfl,_⟩ := hF.localAt _ hi
  obtain ⟨_,_,hu,hv,t,rfl,rfl,_⟩ := hF.localAt _ hj
  exact ⟨_,_,_,_,hx,hy,hu,hv,⟨F.order z t,F.order t z⟩,F.edge z t,F.pred z⟩

private theorem childSide {S ea eb n w j i}
    (pos : Pos (a:=a) (b:=b) S ea eb n) (hs : Roots S)
    (hi : child w i ∈ S) (hj : (w,j) ∈ S) :
    ∃ x y u v, ea (child w i) = some x ∧ eb (child w i) = some y ∧
      ea (w,j) = some u ∧ eb (w,j) = some v ∧ side a b x y u v := by
  obtain ⟨F,hF⟩ := pos w (hs.1 _ hj)
  obtain ⟨x,y,hx,hy,pr⟩ := hF.childAt _ hi
  obtain ⟨_,_,hu,hv,t,rfl,rfl,_⟩ := hF.localAt _ hj
  exact ⟨_,_,_,_,hx,hy,hu,hv,pr t⟩

private theorem compareSide {S ea eb n z t} (pos : Pos (a:=a) (b:=b) S ea eb n)
    (hs : Roots S) (hz : z ∈ S) (ht : t ∈ S) (comp : comparable z t) :
    ∃ x y u v, ea z = some x ∧ eb z = some y ∧ ea t = some u ∧ eb t = some v ∧
      side a b x y u v := by
  obtain ⟨w,i⟩ := z; obtain ⟨w',j⟩ := t
  rcases comp with h | ⟨l,h⟩ | ⟨l,h⟩
  · change w = w' at h; subst w'
    obtain ⟨x,y,u,v,hx,hy,hu,hv,hord,_⟩ := sameCluster pos hs hz ht
    exact ⟨x,y,u,v,hx,hy,hu,hv,hord⟩
  · rw [h] at hz ⊢
    exact childSide pos hs hz ht
  · rw [h] at ht ⊢
    obtain ⟨x,y,u,v,hx,hy,hu,hv,hord⟩ := childSide pos hs ht hz
    exact ⟨u,v,x,y,hu,hv,hx,hy,⟨hord.2,hord.1⟩⟩

private theorem exBridge {X Y : Type} {P : X → Prop} {Q : Y → Prop} {R : X → Y → Prop}
    (forth : ∀ x, P x → ∃ y, R x y) (back : ∀ y, Q y → ∃ x, R x y)
    (agree : ∀ x y, R x y → (P x ↔ Q y)) : (∃ x, P x) ↔ ∃ y, Q y := by
  constructor
  · rintro ⟨x,hx⟩; obtain ⟨y,h⟩ := forth x hx; exact ⟨y,(agree x y h).mp hx⟩
  · rintro ⟨y,hy⟩; obtain ⟨x,h⟩ := back y hy; exact ⟨x,(agree x y h).mpr hy⟩

private theorem guarded {G : Graph c} {o : LinearOrder (Fin G.size)} {env : Env G.size}
    {z v : Var} {u : Fin G.size} (h : env v = some u) (hv : v ≠ z) (f : Formula c) :
    eval G o env (.ex z (conj (.edge z v) f)) ↔
      ∃ x, G.edge x u ∧ eval G o (put env z x) f := by
  classical
  change (∃ x, ¬ (¬ eval G o (put env z x) (.edge z v) ∨ ¬ eval G o (put env z x) f)) ↔ _
  simp [eval, put, hv, h]

private theorem play {K : Nat} (sp : spectrumAgrees A B a b K)
    {S : List Var} {f : Formula c} (hf : Legal S f) :
    ∀ n, rank f ≤ n → n ≤ K+1 → ∀ ea eb, Roots S → Pos (a:=a) (b:=b) S ea eb n →
      (eval A a ea f ↔ eval B b eb f) := by
  induction hf with
  | @pred S z p hz =>
    intro n _ _ ea eb hs pos
    obtain ⟨w,i⟩ := z
    obtain ⟨x,y,_,_,hx,hy,_,_,_,_,hp⟩ := sameCluster pos hs hz hz
    simpa [eval,hx,hy] using hp p
  | @edge S z t hz ht hw =>
    intro n _ _ ea eb hs pos
    obtain ⟨w,i⟩ := z; obtain ⟨w',j⟩ := t
    change w = w' at hw; subst w'
    obtain ⟨x,y,u,v,hx,hy,hu,hv,_,he,_⟩ := sameCluster pos hs hz ht
    simpa [eval,hx,hy,hu,hv] using he
  | eq hz ht comp =>
    intro n _ _ ea eb hs pos
    obtain ⟨x,y,u,v,hx,hy,hu,hv,hord⟩ := compareSide pos hs hz ht comp
    simpa [eval,hx,hy,hu,hv,eq_comm] using sideEq hord
  | lt hz ht comp =>
    intro n _ _ ea eb hs pos
    obtain ⟨x,y,u,v,hx,hy,hu,hv,hord⟩ := compareSide pos hs hz ht comp
    simpa [eval,hx,hy,hu,hv] using hord.1
  | neg _ ih =>
    intro n h hK ea eb hs pos
    exact not_congr (ih n h hK ea eb hs pos)
  | disj _ _ ih₁ ih₂ =>
    intro n h hK ea eb hs pos
    exact or_congr (ih₁ n ((le_max_left ..).trans h) hK ea eb hs pos)
      (ih₂ n ((le_max_right ..).trans h) hK ea eb hs pos)
  | rootEx _ ih =>
    intro n h hK ea eb _ _
    cases n with
    | zero => simp [rank] at h
    | succ n =>
      have hn : n ≤ K := by omega
      apply exBridge (R := same A B a b K)
        (fun x _ => sp.1 x) (fun y _ => sp.2 y)
      intro x y hxy
      obtain ⟨F,hr,rfl,rfl⟩ := makeBox hxy
      exact ih n (Nat.le_of_succ_le_succ h) (by omega) _ _
        (by apply rootsAdd (S := []) (by simp [Roots]) (by simp [root])
            intro w j hj
            have := congrArg (fun (z : Var) => z.1.length) hj
            simp [root,child] at this)
        (rootPos F (by omega))
  | @childEx S w j f hpar fresh _ ih =>
    intro n h hK ea eb hs pos
    cases n with
    | zero => simp [rank] at h
    | succ n =>
      obtain ⟨F,hF⟩ := pos w hpar
      obtain ⟨r,hr⟩ : ∃ r, F.r = r+1 := ⟨F.r-1, by have := hF.room; omega⟩
      have moves := F.next r hr
      apply exBridge (R := fun x y => same A B a b r x y ∧ Profile F x y)
        (fun x _ => moves.1 x) (fun y _ => moves.2 y)
      rintro x y ⟨hxy,pr⟩
      obtain ⟨G,hGr,hGx,hGy⟩ := makeBox hxy
      apply ih n (Nat.le_of_succ_le_succ h) (by omega)
      · apply rootsAdd hs (by simp [child])
        intro v l hl; simpa only [(child_inj hl).1.symm] using hpar
      · exact addChild pos hs F hF fresh pr G (by have := hF.room; omega) hGx hGy
  | @continuation S w i j f hguard hji fresh _ _ ih =>
    intro n h hK ea eb hs pos
    cases n with
    | zero => simp [rank] at h
    | succ n =>
      have hroot := hs.1 _ hguard
      obtain ⟨F,hF⟩ := pos w hroot
      obtain ⟨u,v,hu,hv,huv⟩ := hF.localAt j hguard
      have hne : (w,j) ≠ (w,i) := by simp [Nat.ne_of_lt hji]
      rw [guarded hu hne, guarded hv hne]
      apply exBridge (R := fun x y => A.edge x u ∧ B.edge y v ∧ Local F n x y)
      · rintro x ⟨hx,_⟩; obtain ⟨y,hy,hl⟩ := fromA F huv hx
        exact ⟨y,hx,hy,hl⟩
      · rintro y ⟨hy,_⟩; obtain ⟨x,hx,hl⟩ := fromB F huv hy
        exact ⟨x,hx,hy,hl⟩
      · rintro x y ⟨hx,hy,hl⟩
        simp only [hx,hy,true_and]
        apply ih n (by simpa [rank,conj] using h) (by omega)
        · apply rootsAdd (z := (w,i)) hs (List.mem_cons_of_mem _ hroot)
          intro v l hh
          have := congrArg Prod.snd hh; simp [child] at this; omega
        · exact addCont pos F hF fresh (by omega) hl

end Positions

/--
---
conclusion: Lax977378.Collapse.comparison
---
Use a pointed ordered ball isomorphism for each introduced cluster. Its
remaining radius covers all further guarded continuations. A child root
matches the comparisons to every vertex of its parent's ball, including
vertices that have not yet been played. The induction follows the CFO grammar.
-/
theorem comparison {c : Nat} (K : Nat) (A B : Graph c) (a : LinearOrder (Fin A.size))
    (b : LinearOrder (Fin B.size)) (agree : spectrumAgrees A B a b K)
    (f : Formula c) (legal : Legal [] f) (bound : rank f ≤ K+1) :
    Holds A a f ↔ Holds B b f :=
  play agree legal (K+1) bound le_rfl _ _ (by simp [Roots]) (fun _ h => by simp at h)

end Lax977378Proofs.Comparison
