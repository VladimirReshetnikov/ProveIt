import ZFCinPA.ValidatorSeedLogicalImages222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Actual raw transitive containers, guarded transitive containers and exact
 tagged pairs, with internal parameters and explicit source proof witnesses.
 No container, source validity or marker-freshness premise is supplied. -/
namespace LeanProofs.ZFCinPA.ValidatorSeedTransitive222
open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory LO.Entailment LO.Entailment.FiniteContext
open ValidatorSourceFullSeed222 ValidatorFullSeedTheory222 ValidatorSeedSourceBasis222
open ValidatorSeedRawComprehension222 ValidatorSeedGuardedComprehension222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] pairAt pairExists pairMatrix

private theorem singleton_unique (p z a : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt p z 🡒 singletonAt p a 🡒 eqTerm z a := by
  cl_prover [singleton_mem p z,singleton_spec p a z]

attribute [local irreducible] singletonAt subsetTerm closureTerm hitBody

def transitiveMatrix : Semiformula V ℒₛₑₜ 2 :=
  singTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0)

@[simp] theorem transitiveMatrix_shift : (transitiveMatrix (V := V)).shift=transitiveMatrix := by
  simp [transitiveMatrix,singTerm,memTerm,eqTerm]
@[simp] theorem transitiveMatrix_subst (v p : Term V ℒₛₑₜ) :
    (transitiveMatrix (V := V)).subst ![v,p]=singletonAt p v := by
  rcases term_is_fvar v with ⟨v,rfl⟩
  rcases term_is_fvar p with ⟨p,rfl⟩
  simp [transitiveMatrix,singTerm,singletonAt,memTerm,eqTerm,SemitermVec.q,
    Matrix.vecHead,Matrix.vecTail]

attribute [local irreducible] transitiveMatrix

private theorem singleton_transfer (p v z c : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt p v 🡒 singletonAt p z 🡒 memTerm v c 🡒 memTerm z c := by
  cl_prover [singleton_unique p v z, source_mem_congr v z c]

private theorem singleton_hit (p z c : Term V ℒₛₑₜ) :
    Source V ⊢ (∃⁰ hitBody transitiveMatrix p c) 🡒 singletonAt p z 🡒 memTerm z c := by
  apply exists_elim
  rw [hitBody_free,transitiveMatrix_shift,transitiveMatrix_subst]
  have h := singleton_transfer p.shift (Bootstrapping.Semiterm.fvar 0) z.shift c.shift
  have h' : Source V ⊢ (singletonAt p.shift (Bootstrapping.Semiterm.fvar 0) ⋏
      memTerm (Bootstrapping.Semiterm.fvar 0) c.shift) 🡒
      singletonAt p.shift z.shift 🡒 memTerm z.shift c.shift := by cl_prover [h]
  simpa [Bootstrapping.Semiformula.shift_imp,singletonAt_shift,memTerm] using h'

private theorem pair_contains (s a c : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt s a 🡒 pairAt transitiveMatrix s c 🡒 memTerm a c := by
  have hr : Source V ⊢ pairAt transitiveMatrix s c 🡒
      transitiveMatrix.subst ![a,s] 🡒 ∃⁰ hitBody transitiveMatrix s c := by
    simpa only [hitBody] using pair_request (transitiveMatrix (V := V)) s c a
  rw [transitiveMatrix_subst] at hr
  cl_prover [hr,singleton_hit s a c]

private theorem pair_closed_singleton (s c y z p : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt p z 🡒 pairAt transitiveMatrix s c 🡒
      memTerm y c 🡒 memTerm z y 🡒 memTerm z c := by
  have hstep := closure_step (transitiveMatrix (V := V)) c y p z
  rw [transitiveMatrix_subst] at hstep
  have hex : Source V ⊢ singletonAt p z 🡒 pairAt transitiveMatrix s c 🡒
      memTerm y c 🡒 memTerm z y 🡒 ∃⁰ hitBody transitiveMatrix p c := by
    cl_prover [pair_closure (transitiveMatrix (V := V)) s c y,
      singleton_subset p z y, hstep]
  cl_prover [hex, singleton_hit p z c]

private theorem pair_closed_point (s c y z : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt transitiveMatrix s c 🡒 memTerm y c 🡒 memTerm z y 🡒 memTerm z c := by
  have he : Source V ⊢ (∃⁰ singletonBody z) 🡒
      (pairAt transitiveMatrix s c 🡒 memTerm y c 🡒 memTerm z y 🡒 memTerm z c) := by
    apply exists_elim
    rw [singletonBody_free']
    simpa [Bootstrapping.Semiformula.shift_imp,pairAt_shift,memTerm] using
      pair_closed_singleton s.shift c.shift y.shift z.shift (Bootstrapping.Semiterm.fvar 0)
  exact ⟨he.get ⨀ (singleton_object z).get⟩

private theorem all_intro {H : Formula V ℒₛₑₜ} {p : Semiformula V ℒₛₑₜ 1}
    (h : Source V ⊢ H.shift 🡒 p.free) : Source V ⊢ H 🡒 ∀⁰ p :=
  ⟨TProof.generalizeAux h.get⟩

private theorem pair_subset (s c y : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt transitiveMatrix s c 🡒 memTerm y c 🡒 subsetTerm y c := by
  have ha : Source V ⊢ (pairAt transitiveMatrix s c ⋏ memTerm y c) 🡒 subsetTerm y c := by
    unfold subsetTerm
    apply all_intro
    simpa [Bootstrapping.Semiformula.shift_and,pairAt_shift,memTerm,
      Bootstrapping.Semiformula.free,←Bootstrapping.Semiterm.bShift_shift_comm] using
      (show Source V ⊢ (pairAt transitiveMatrix s.shift c.shift ⋏ memTerm y.shift c.shift) 🡒
        (memTerm (Bootstrapping.Semiterm.fvar 0) y.shift 🡒
          memTerm (Bootstrapping.Semiterm.fvar 0) c.shift) from by
        cl_prover [pair_closed_point s.shift c.shift y.shift (Bootstrapping.Semiterm.fvar 0)])
  cl_prover [ha]

def transitiveTerm {n : ℕ} (c : Semiterm V ℒₛₑₜ n) : Semiformula V ℒₛₑₜ n :=
  ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift 🡒
    subsetTerm (Bootstrapping.Semiterm.bvar 0) c.bShift)
def rawTransitiveBody (a : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  memTerm a.bShift (Bootstrapping.Semiterm.bvar 0) ⋏ transitiveTerm (Bootstrapping.Semiterm.bvar 0)
def rawTransitiveAt (a c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (rawTransitiveBody a).subst ![c]

@[simp] theorem transitiveTerm_shift {n : ℕ} (c : Semiterm V ℒₛₑₜ n) :
    (transitiveTerm c).shift=transitiveTerm c.shift := by
  simp [transitiveTerm,subsetTerm,memTerm,←Bootstrapping.Semiterm.bShift_shift_comm]
@[simp] theorem rawTransitiveBody_shift (a : Term V ℒₛₑₜ) :
    (rawTransitiveBody a).shift=rawTransitiveBody a.shift := by
  simp [rawTransitiveBody,memTerm,←Bootstrapping.Semiterm.bShift_shift_comm]
@[simp] theorem rawTransitiveAt_shift (a c : Term V ℒₛₑₜ) :
    (rawTransitiveAt a c).shift=rawTransitiveAt a.shift c.shift := by
  simp [rawTransitiveAt,Bootstrapping.Semiformula.shift_substs,Matrix.vecHead,Matrix.vecTail]
@[simp] theorem rawTransitiveBody_free (a : Term V ℒₛₑₜ) :
    (rawTransitiveBody a).free=rawTransitiveAt a.shift (Bootstrapping.Semiterm.fvar 0) := by
  simp [rawTransitiveAt,Bootstrapping.Semiformula.free]
theorem rawTransitiveAt_eq (a c : Term V ℒₛₑₜ) :
    rawTransitiveAt a c=memTerm a c ⋏ transitiveTerm c := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  simp [rawTransitiveAt,rawTransitiveBody,transitiveTerm,subsetTerm,memTerm,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail]

attribute [local irreducible] transitiveTerm rawTransitiveBody rawTransitiveAt

private theorem pair_transitive (s c : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt transitiveMatrix s c 🡒 transitiveTerm c := by
  rcases term_is_fvar s with ⟨sIdx,rfl⟩
  rcases term_is_fvar c with ⟨cIdx,rfl⟩
  unfold transitiveTerm
  apply all_intro
  simpa [pairAt_shift,memTerm,subsetTerm,Bootstrapping.Semiformula.free,
    ←Bootstrapping.Semiterm.bShift_shift_comm,SemitermVec.q] using
    pair_subset (Bootstrapping.Semiterm.fvar sIdx).shift (Bootstrapping.Semiterm.fvar cIdx).shift (Bootstrapping.Semiterm.fvar 0)

private theorem raw_of_singleton (a s : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt s a 🡒 ∃⁰ rawTransitiveBody a := by
  have he : [singletonAt s a] ⊢[Source V]
      (∃⁰ pairExists transitiveMatrix s) 🡒 ∃⁰ rawTransitiveBody a := by
    apply TProof.exs_imp_exs!
    rw [pairExists_free,rawTransitiveBody_free,transitiveMatrix_shift,rawTransitiveAt_eq]
    let Γ := [singletonAt s a].map Bootstrapping.Semiformula.shift
    have hmem := FiniteContext.of'! (Γ := Γ)
      (pair_contains s.shift a.shift (Bootstrapping.Semiterm.fvar 0))
    have htr := FiniteContext.of'! (Γ := Γ)
      (pair_transitive s.shift (Bootstrapping.Semiterm.fvar 0))
    have hsing : Γ ⊢[Source V] singletonAt s.shift a.shift := by
      simp only [Γ,List.map_cons,List.map_nil,singletonAt_shift]; exact by_axm₀!
    cl_prover [hmem,htr,hsing]
  have hx := FiniteContext.of'! (Γ := [singletonAt s a]) (pair_exists (transitiveMatrix (V := V)) s)
  apply deduct'!
  exact ⟨he.get ⨀ hx.get⟩

/-- The same full-seed witness contains a and is genuinely raw-transitive. -/
theorem raw_transitive (a : Term V ℒₛₑₜ) : Source V ⊢ ∃⁰ rawTransitiveBody a := by
  have he : Source V ⊢ (∃⁰ singletonBody a) 🡒 ∃⁰ rawTransitiveBody a := by
    apply exists_elim
    simpa only [singletonBody_free',Bootstrapping.Semiformula.shift_exs,rawTransitiveBody_shift] using
      raw_of_singleton a.shift (Bootstrapping.Semiterm.fvar 0)
  exact ⟨he.get ⨀ (singleton_object a).get⟩

private theorem transitive_spec (U y z : Term V ℒₛₑₜ) :
    Source V ⊢ transitiveTerm U 🡒 memTerm y U 🡒 memTerm z y 🡒 memTerm z U := by
  rcases term_is_fvar U with ⟨UIdx,rfl⟩
  rcases term_is_fvar y with ⟨yIdx,rfl⟩
  rcases term_is_fvar z with ⟨zIdx,rfl⟩
  apply deduct'!
  have h : [transitiveTerm (Bootstrapping.Semiterm.fvar UIdx)] ⊢[Source V] transitiveTerm (Bootstrapping.Semiterm.fvar UIdx) := by_axm₀!
  unfold transitiveTerm at h
  have h' : [transitiveTerm (Bootstrapping.Semiterm.fvar UIdx)] ⊢[Source V] memTerm (Bootstrapping.Semiterm.fvar yIdx) (Bootstrapping.Semiterm.fvar UIdx) 🡒 subsetTerm (Bootstrapping.Semiterm.fvar yIdx) (Bootstrapping.Semiterm.fvar UIdx) := by
    simpa [transitiveTerm,subsetTerm,memTerm,SemitermVec.q] using TProof.specialize_with_ctx! h (Bootstrapping.Semiterm.fvar yIdx)
  apply FiniteContext.deduct!
  have hm : [memTerm (Bootstrapping.Semiterm.fvar yIdx) (Bootstrapping.Semiterm.fvar UIdx),transitiveTerm (Bootstrapping.Semiterm.fvar UIdx)] ⊢[Source V] memTerm (Bootstrapping.Semiterm.fvar yIdx) (Bootstrapping.Semiterm.fvar UIdx) := by_axm₀!
  have hs : [memTerm (Bootstrapping.Semiterm.fvar yIdx) (Bootstrapping.Semiterm.fvar UIdx),transitiveTerm (Bootstrapping.Semiterm.fvar UIdx)] ⊢[Source V] subsetTerm (Bootstrapping.Semiterm.fvar yIdx) (Bootstrapping.Semiterm.fvar UIdx) := by
    have h'' := FiniteContext.weakening! (show [transitiveTerm (Bootstrapping.Semiterm.fvar UIdx)]⊆[memTerm (Bootstrapping.Semiterm.fvar yIdx) (Bootstrapping.Semiterm.fvar UIdx),transitiveTerm (Bootstrapping.Semiterm.fvar UIdx)] by simp) h'
    exact ⟨h''.get ⨀ hm.get⟩
  unfold subsetTerm at hs
  simpa [subsetTerm,memTerm] using TProof.specialize_with_ctx! hs (Bootstrapping.Semiterm.fvar zIdx)

private theorem cut_tag (U t c : Term V ℒₛₑₜ) :
    Source V ⊢ guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c 🡒 memTerm t c := by
  rcases term_is_fvar U with ⟨U,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  simp only [guardedAt,guardedBody,Bootstrapping.Semiformula.substs_and]
  simp [memTerm]

private theorem cut_spec (U t c z : Term V ℒₛₑₜ) :
    Source V ⊢ guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c 🡒 memTerm t z 🡒
      (memTerm z c 🡘 memTerm z U) := by
  rcases term_is_fvar U with ⟨U,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  apply deduct'!
  have h : [guardedAt (⊤ : Semiformula V ℒₛₑₜ 1)
      (Bootstrapping.Semiterm.fvar U) (Bootstrapping.Semiterm.fvar t) (Bootstrapping.Semiterm.fvar c)] ⊢[Source V]
      guardedAt (⊤ : Semiformula V ℒₛₑₜ 1)
      (Bootstrapping.Semiterm.fvar U) (Bootstrapping.Semiterm.fvar t) (Bootstrapping.Semiterm.fvar c) := by_axm₀!
  simp only [guardedAt,guardedBody,Bootstrapping.Semiformula.substs_and] at h
  have hr := K!_right h
  simp only [Bootstrapping.Semiformula.substs_all] at hr
  have hz := TProof.specialize_with_ctx! hr z
  have hz' : [guardedAt (⊤ : Semiformula V ℒₛₑₜ 1)
      (Bootstrapping.Semiterm.fvar U) (Bootstrapping.Semiterm.fvar t) (Bootstrapping.Semiterm.fvar c)] ⊢[Source V]
      memTerm (Bootstrapping.Semiterm.fvar t) z 🡒
      (memTerm z (Bootstrapping.Semiterm.fvar c) 🡘 (memTerm z (Bootstrapping.Semiterm.fvar U) ⋏ ⊤)) := by
    simpa [guardedAt,guardedBody,memTerm,SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using hz
  cl_prover [hz']

private theorem cut_forward (U t c z : Term V ℒₛₑₜ) :
    Source V ⊢ guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c 🡒 memTerm t z 🡒 memTerm z c 🡒 memTerm z U := by
  cl_prover [cut_spec U t c z]
private theorem cut_backward (U t c z : Term V ℒₛₑₜ) :
    Source V ⊢ guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c 🡒 memTerm t z 🡒 memTerm z U 🡒 memTerm z c := by
  cl_prover [cut_spec U t c z]

private theorem cut_point (U t c y z : Term V ℒₛₑₜ) :
    Source V ⊢ guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c 🡒 transitiveTerm U 🡒
      memTerm t y 🡒 memTerm y c 🡒 memTerm t z 🡒 memTerm z y 🡒 memTerm z c := by
  apply deduct'!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  let Γ := [memTerm z y,memTerm t z,memTerm y c,memTerm t y,transitiveTerm U,
    guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c]
  have hg : Γ ⊢[Source V] guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c := by simp only [Γ]; exact by_axm!
  have htr : Γ ⊢[Source V] transitiveTerm U := by simp only [Γ]; exact by_axm!
  have hty : Γ ⊢[Source V] memTerm t y := by simp only [Γ]; exact by_axm!
  have hyc : Γ ⊢[Source V] memTerm y c := by simp only [Γ]; exact by_axm!
  have htz : Γ ⊢[Source V] memTerm t z := by simp only [Γ]; exact by_axm!
  have hzy : Γ ⊢[Source V] memTerm z y := by_axm₀!
  have hf := FiniteContext.of'! (Γ := Γ) (cut_forward U t c y)
  have hyU : Γ ⊢[Source V] memTerm y U := ⟨((hf.get ⨀ hg.get) ⨀ hty.get) ⨀ hyc.get⟩
  have hts := FiniteContext.of'! (Γ := Γ) (transitive_spec U y z)
  have hzU : Γ ⊢[Source V] memTerm z U := ⟨((hts.get ⨀ htr.get) ⨀ hyU.get) ⨀ hzy.get⟩
  have hb := FiniteContext.of'! (Γ := Γ) (cut_backward U t c z)
  exact ⟨((hb.get ⨀ hg.get) ⨀ htz.get) ⨀ hzU.get⟩

def taggedSubsetTerm {n : ℕ} (t c y : Semiterm V ℒₛₑₜ n) : Semiformula V ℒₛₑₜ n :=
  ∀⁰ (memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) 🡒
    memTerm (Bootstrapping.Semiterm.bvar 0) y.bShift 🡒
      memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift)
def taggedTransitiveTerm {n : ℕ} (t c : Semiterm V ℒₛₑₜ n) : Semiformula V ℒₛₑₜ n :=
  ∀⁰ (memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) 🡒
    memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift 🡒
      taggedSubsetTerm t.bShift c.bShift (Bootstrapping.Semiterm.bvar 0))
def taggedTransitiveBody (a t : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
    (memTerm a.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
      taggedTransitiveTerm t.bShift (Bootstrapping.Semiterm.bvar 0))
def taggedTransitiveAt (a t c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (taggedTransitiveBody a t).subst ![c]
def taggedPairBody (x y t : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
    (∀⁰ (memTerm t.bShift.bShift (Bootstrapping.Semiterm.bvar 0) 🡒
      (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡘
        (eqTerm (Bootstrapping.Semiterm.bvar 0) x.bShift.bShift ⋎
          eqTerm (Bootstrapping.Semiterm.bvar 0) y.bShift.bShift))))
def taggedPairAt (x y t c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (taggedPairBody x y t).subst ![c]

@[simp] theorem taggedSubsetTerm_shift {n : ℕ} (t c y : Semiterm V ℒₛₑₜ n) :
    (taggedSubsetTerm t c y).shift=taggedSubsetTerm t.shift c.shift y.shift := by
  simp [taggedSubsetTerm,memTerm,←Bootstrapping.Semiterm.bShift_shift_comm]
@[simp] theorem taggedTransitiveTerm_shift {n : ℕ} (t c : Semiterm V ℒₛₑₜ n) :
    (taggedTransitiveTerm t c).shift=taggedTransitiveTerm t.shift c.shift := by
  simp [taggedTransitiveTerm,memTerm,←Bootstrapping.Semiterm.bShift_shift_comm]
@[simp] theorem taggedTransitiveBody_shift (a t : Term V ℒₛₑₜ) :
    (taggedTransitiveBody a t).shift=taggedTransitiveBody a.shift t.shift := by
  simp [taggedTransitiveBody,memTerm,←Bootstrapping.Semiterm.bShift_shift_comm]
@[simp] theorem taggedPairBody_shift (x y t : Term V ℒₛₑₜ) :
    (taggedPairBody x y t).shift=taggedPairBody x.shift y.shift t.shift := by
  simp [taggedPairBody,memTerm,eqTerm,←Bootstrapping.Semiterm.bShift_shift_comm]
@[simp] theorem taggedTransitiveBody_free (a t : Term V ℒₛₑₜ) :
    (taggedTransitiveBody a t).free=taggedTransitiveAt a.shift t.shift (Bootstrapping.Semiterm.fvar 0) := by
  simp [taggedTransitiveAt,Bootstrapping.Semiformula.free]
@[simp] theorem taggedPairBody_free (x y t : Term V ℒₛₑₜ) :
    (taggedPairBody x y t).free=taggedPairAt x.shift y.shift t.shift (Bootstrapping.Semiterm.fvar 0) := by
  simp [taggedPairAt,Bootstrapping.Semiformula.free]
theorem taggedTransitiveAt_eq (a t c : Term V ℒₛₑₜ) :
    taggedTransitiveAt a t c=memTerm t c ⋏ (memTerm a c ⋏ taggedTransitiveTerm t c) := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  simp [taggedTransitiveAt,taggedTransitiveBody,taggedTransitiveTerm,taggedSubsetTerm,memTerm,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail]

attribute [local irreducible] taggedSubsetTerm taggedTransitiveTerm taggedTransitiveBody taggedTransitiveAt taggedPairBody taggedPairAt

private theorem cut_subset (U t c y : Term V ℒₛₑₜ) :
    Source V ⊢ guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c 🡒 transitiveTerm U 🡒
      memTerm t y 🡒 memTerm y c 🡒 taggedSubsetTerm t c y := by
  apply deduct'!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  unfold taggedSubsetTerm
  apply TProof.generalize!
  let Γ := [memTerm y c,memTerm t y,transitiveTerm U,
    guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c].map Bootstrapping.Semiformula.shift
  have hg : Γ ⊢[Source V] guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U.shift t.shift c.shift := by
    simp only [Γ,List.map_cons,List.map_nil,guardedAt_shift,Bootstrapping.Semiformula.shift_verum]
    exact by_axm!
  have htr : Γ ⊢[Source V] transitiveTerm U.shift := by
    simp only [Γ,List.map_cons,List.map_nil,transitiveTerm_shift]
    exact by_axm!
  have hty : Γ ⊢[Source V] memTerm t.shift y.shift := by
    simp [Γ,memTerm]; exact by_axm!
  have hyc : Γ ⊢[Source V] memTerm y.shift c.shift := by
    simp [Γ,memTerm]; exact by_axm₀!
  have hp := FiniteContext.of'! (Γ := Γ)
    (cut_point U.shift t.shift c.shift y.shift (Bootstrapping.Semiterm.fvar 0))
  have h : Γ ⊢[Source V] memTerm t.shift (Bootstrapping.Semiterm.fvar 0) 🡒
      memTerm (Bootstrapping.Semiterm.fvar 0) y.shift 🡒
      memTerm (Bootstrapping.Semiterm.fvar 0) c.shift :=
    ⟨(((hp.get ⨀ hg.get) ⨀ htr.get) ⨀ hty.get) ⨀ hyc.get⟩
  simpa [Γ,memTerm,Bootstrapping.Semiformula.free,←Bootstrapping.Semiterm.bShift_shift_comm] using h

private theorem cut_transitive (U t c : Term V ℒₛₑₜ) :
    Source V ⊢ guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c 🡒
      transitiveTerm U 🡒 taggedTransitiveTerm t c := by
  rcases term_is_fvar U with ⟨UIdx,rfl⟩
  rcases term_is_fvar t with ⟨tIdx,rfl⟩
  rcases term_is_fvar c with ⟨cIdx,rfl⟩
  have ha : Source V ⊢ (guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) (Bootstrapping.Semiterm.fvar UIdx) (Bootstrapping.Semiterm.fvar tIdx) (Bootstrapping.Semiterm.fvar cIdx) ⋏ transitiveTerm (Bootstrapping.Semiterm.fvar UIdx)) 🡒
      taggedTransitiveTerm (Bootstrapping.Semiterm.fvar tIdx) (Bootstrapping.Semiterm.fvar cIdx) := by
    unfold taggedTransitiveTerm
    apply all_intro
    simpa [Bootstrapping.Semiformula.shift_and,guardedAt_shift,memTerm,taggedSubsetTerm,
      Bootstrapping.Semiformula.free,←Bootstrapping.Semiterm.bShift_shift_comm,SemitermVec.q] using
      (show Source V ⊢ (guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) (Bootstrapping.Semiterm.fvar UIdx).shift (Bootstrapping.Semiterm.fvar tIdx).shift (Bootstrapping.Semiterm.fvar cIdx).shift ⋏
        transitiveTerm (Bootstrapping.Semiterm.fvar UIdx).shift) 🡒 memTerm (Bootstrapping.Semiterm.fvar tIdx).shift (Bootstrapping.Semiterm.fvar 0) 🡒
        memTerm (Bootstrapping.Semiterm.fvar 0) (Bootstrapping.Semiterm.fvar cIdx).shift 🡒
        taggedSubsetTerm (Bootstrapping.Semiterm.fvar tIdx).shift (Bootstrapping.Semiterm.fvar cIdx).shift (Bootstrapping.Semiterm.fvar 0) from by
          cl_prover [cut_subset (Bootstrapping.Semiterm.fvar UIdx).shift (Bootstrapping.Semiterm.fvar tIdx).shift (Bootstrapping.Semiterm.fvar cIdx).shift (Bootstrapping.Semiterm.fvar 0)])
  cl_prover [ha]

private theorem cut_raw (a U t c : Term V ℒₛₑₜ) :
    Source V ⊢ rawTransitiveAt a U 🡒 memTerm t a 🡒
      guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c 🡒 taggedTransitiveAt a t c := by
  rw [rawTransitiveAt_eq,taggedTransitiveAt_eq]
  cl_prover [cut_tag U t c,cut_backward U t c a,cut_transitive U t c]

private theorem tagged_of_raw (a U t : Term V ℒₛₑₜ) :
    Source V ⊢ rawTransitiveAt a U 🡒 emptyAt t 🡒 memTerm t a 🡒 ∃⁰ taggedTransitiveBody a t := by
  have hm : Source V ⊢ rawTransitiveAt a U 🡒 memTerm t a 🡒
      (∃⁰ guardedBody (⊤ : Semiformula V ℒₛₑₜ 1) U t) 🡒 ∃⁰ taggedTransitiveBody a t := by
    apply deduct'!
    apply FiniteContext.deduct!
    apply TProof.exs_imp_exs!
    rw [guardedBody_free,taggedTransitiveBody_free]
    let Γ := [memTerm t a,rawTransitiveAt a U].map Bootstrapping.Semiformula.shift
    have hr : Γ ⊢[Source V] rawTransitiveAt a.shift U.shift := by
      simp only [Γ,List.map_cons,List.map_nil,rawTransitiveAt_shift]; exact by_axm!
    have ht : Γ ⊢[Source V] memTerm t.shift a.shift := by
      simp [Γ,memTerm]; exact by_axm₀!
    have hp := FiniteContext.of'! (Γ := Γ)
      (cut_raw a.shift U.shift t.shift (Bootstrapping.Semiterm.fvar 0))
    simpa only [Γ,List.map_cons,List.map_nil,rawTransitiveAt_shift,Bootstrapping.Semiformula.shift_verum] using
      (show Γ ⊢[Source V] guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U.shift t.shift
        (Bootstrapping.Semiterm.fvar 0) 🡒 taggedTransitiveAt a.shift t.shift
        (Bootstrapping.Semiterm.fvar 0) from by cl_prover [hr,ht,hp])
  cl_prover [hm,guarded_comprehension (⊤ : Semiformula V ℒₛₑₜ 1) U t]

/-- The raw bound is constructed, and the guard has no U≠t exception. -/
theorem tagged_transitive (a t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 memTerm t a 🡒 ∃⁰ taggedTransitiveBody a t := by
  have he : Source V ⊢ (∃⁰ rawTransitiveBody a) 🡒
      (emptyAt t 🡒 memTerm t a 🡒 ∃⁰ taggedTransitiveBody a t) := by
    apply exists_elim
    rw [rawTransitiveBody_free]
    simpa [Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_exs,
      emptyAt,memTerm,taggedTransitiveBody_shift,←Bootstrapping.Semiterm.bShift_shift_comm] using
      tagged_of_raw a.shift (Bootstrapping.Semiterm.fvar 0) t.shift
  exact ⟨he.get ⨀ (raw_transitive a).get⟩

private theorem raw_pair_spec (x y U z : Term V ℒₛₑₜ) :
    Source V ⊢ rawPairAt x y U 🡒 (memTerm z U 🡘 (eqTerm z x ⋎ eqTerm z y)) := by
  rcases term_is_fvar x with ⟨x,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  rcases term_is_fvar U with ⟨U,rfl⟩
  apply deduct'!
  have h : [rawPairAt (Bootstrapping.Semiterm.fvar x) (Bootstrapping.Semiterm.fvar y)
      (Bootstrapping.Semiterm.fvar U)] ⊢[Source V] rawPairAt (Bootstrapping.Semiterm.fvar x)
      (Bootstrapping.Semiterm.fvar y) (Bootstrapping.Semiterm.fvar U) := by_axm₀!
  simp only [rawPairAt,rawPairBody,Bootstrapping.Semiformula.substs_all] at h
  simpa [rawPairAt,rawPairBody,memTerm,eqTerm,SemitermVec.q,
    Matrix.vecHead,Matrix.vecTail] using TProof.specialize_with_ctx! h z

private def taggedPairAll (x y t c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  ∀⁰ (memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) 🡒
    (memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift 🡘
      (eqTerm (Bootstrapping.Semiterm.bvar 0) x.bShift ⋎ eqTerm (Bootstrapping.Semiterm.bvar 0) y.bShift)))
private theorem taggedPairAt_eq (x y t c : Term V ℒₛₑₜ) :
    taggedPairAt x y t c=memTerm t c ⋏ taggedPairAll x y t c := by
  rcases term_is_fvar x with ⟨x,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  simp [taggedPairAt,taggedPairBody,taggedPairAll,memTerm,eqTerm,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail]

private theorem cut_pair (x y U t c : Term V ℒₛₑₜ) :
    Source V ⊢ rawPairAt x y U 🡒 guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c 🡒 taggedPairAt x y t c := by
  have ha : Source V ⊢ (rawPairAt x y U ⋏ guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U t c) 🡒
      taggedPairAll x y t c := by
    unfold taggedPairAll
    apply all_intro
    simpa [Bootstrapping.Semiformula.shift_and,rawPairAt_shift,guardedAt_shift,memTerm,eqTerm,
      Bootstrapping.Semiformula.free,←Bootstrapping.Semiterm.bShift_shift_comm] using
      (show Source V ⊢ (rawPairAt x.shift y.shift U.shift ⋏
        guardedAt (⊤ : Semiformula V ℒₛₑₜ 1) U.shift t.shift c.shift) 🡒
        (memTerm t.shift (Bootstrapping.Semiterm.fvar 0) 🡒
          (memTerm (Bootstrapping.Semiterm.fvar 0) c.shift 🡘
            (eqTerm (Bootstrapping.Semiterm.fvar 0) x.shift ⋎
              eqTerm (Bootstrapping.Semiterm.fvar 0) y.shift))) from by
          cl_prover [raw_pair_spec x.shift y.shift U.shift (Bootstrapping.Semiterm.fvar 0),
            cut_spec U.shift t.shift c.shift (Bootstrapping.Semiterm.fvar 0)])
  rw [taggedPairAt_eq]
  cl_prover [ha,cut_tag U t c]

private theorem tagged_pair_of_raw (x y U t : Term V ℒₛₑₜ) :
    Source V ⊢ rawPairAt x y U 🡒 emptyAt t 🡒 ∃⁰ taggedPairBody x y t := by
  have hm : Source V ⊢ rawPairAt x y U 🡒
      (∃⁰ guardedBody (⊤ : Semiformula V ℒₛₑₜ 1) U t) 🡒 ∃⁰ taggedPairBody x y t := by
    apply deduct'!
    apply TProof.exs_imp_exs!
    rw [guardedBody_free,taggedPairBody_free]
    let Γ := [rawPairAt x y U].map Bootstrapping.Semiformula.shift
    have hr : Γ ⊢[Source V] rawPairAt x.shift y.shift U.shift := by
      simp only [Γ,List.map_cons,List.map_nil,rawPairAt_shift]; exact by_axm₀!
    have hp := FiniteContext.of'! (Γ := Γ)
      (cut_pair x.shift y.shift U.shift t.shift (Bootstrapping.Semiterm.fvar 0))
    simpa only [Γ,List.map_cons,List.map_nil,rawPairAt_shift,Bootstrapping.Semiformula.shift_verum] using (show Γ ⊢[Source V] guardedAt (⊤ : Semiformula V ℒₛₑₜ 1)
      U.shift t.shift (Bootstrapping.Semiterm.fvar 0) 🡒
      taggedPairAt x.shift y.shift t.shift (Bootstrapping.Semiterm.fvar 0) from by cl_prover [hr,hp])
  cl_prover [hm,guarded_comprehension (⊤ : Semiformula V ℒₛₑₜ 1) U t]

/-- Exact pairs on tagged tests, even when x or y is not itself tagged. -/
theorem tagged_pair (x y t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∃⁰ taggedPairBody x y t := by
  have he : Source V ⊢ (∃⁰ rawPairBody x y) 🡒 (emptyAt t 🡒 ∃⁰ taggedPairBody x y t) := by
    apply exists_elim
    rw [rawPairBody_free]
    simpa [Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_exs,
      emptyAt,memTerm,taggedPairBody_shift,←Bootstrapping.Semiterm.bShift_shift_comm] using
      tagged_pair_of_raw x.shift y.shift (Bootstrapping.Semiterm.fvar 0) t.shift
  exact ⟨he.get ⨀ (raw_pair x y).get⟩

def rawTransitiveProof (a : Term V ℒₛₑₜ) : Source V ⊢! ∃⁰ rawTransitiveBody a :=
  (raw_transitive a).get
def taggedTransitiveProof (a t : Term V ℒₛₑₜ) :
    Source V ⊢! emptyAt t 🡒 memTerm t a 🡒 ∃⁰ taggedTransitiveBody a t := (tagged_transitive a t).get
def taggedPairProof (x y t : Term V ℒₛₑₜ) :
    Source V ⊢! emptyAt t 🡒 ∃⁰ taggedPairBody x y t := (tagged_pair x y t).get

theorem rawTransitiveProof_isProof (a : Term V ℒₛₑₜ) :
    Proof seedTheory (rawTransitiveProof a).val (∃⁰ rawTransitiveBody a).val := by
  simpa only [Source,Theory.internalize,Proof,Sequent.val_insert,Sequent.val_empty,singleton_eq_insert]
    using (rawTransitiveProof a).derivationOf
theorem taggedTransitiveProof_isProof (a t : Term V ℒₛₑₜ) :
    Proof seedTheory (taggedTransitiveProof a t).val
      (emptyAt t 🡒 memTerm t a 🡒 ∃⁰ taggedTransitiveBody a t).val := by
  simpa only [Source,Theory.internalize,Proof,Sequent.val_insert,Sequent.val_empty,singleton_eq_insert]
    using (taggedTransitiveProof a t).derivationOf
theorem taggedPairProof_isProof (x y t : Term V ℒₛₑₜ) :
    Proof seedTheory (taggedPairProof x y t).val (emptyAt t 🡒 ∃⁰ taggedPairBody x y t).val := by
  simpa only [Source,Theory.internalize,Proof,Sequent.val_insert,Sequent.val_empty,singleton_eq_insert]
    using (taggedPairProof x y t).derivationOf

/-! Total formula constructors. Their arguments are term codes, not labels;
the `.get` proof selectors above are not asserted to have Σ₁ graphs. -/
def transitiveMatrixMeta : SetTheorySemiproposition 2 :=
  ∀⁰ (seedMem 3 0 2 🡘 FirstOrder.Semiformula.rel Language.Eq.eq ![#0,#1])
private def rawTransitiveMeta : SetTheorySemiproposition 2 :=
  seedMem 2 1 0 ⋏ (∀⁰ (seedMem 3 0 1 🡒 ∀⁰ (seedMem 4 0 1 🡒 seedMem 4 0 2)))
private def taggedTransitiveMeta : SetTheorySemiproposition 3 :=
  seedMem 3 2 0 ⋏ (seedMem 3 1 0 ⋏ (∀⁰ (seedMem 4 3 0 🡒 seedMem 4 0 1 🡒
    ∀⁰ (seedMem 5 4 0 🡒 seedMem 5 0 1 🡒 seedMem 5 0 2))))
private def taggedPairMeta : SetTheorySemiproposition 4 :=
  seedMem 4 3 0 ⋏ (∀⁰ (seedMem 5 4 0 🡒 (seedMem 5 0 1 🡘
    (FirstOrder.Semiformula.rel Language.Eq.eq ![#0,#2] ⋎
      FirstOrder.Semiformula.rel Language.Eq.eq ![#0,#3]))))
def transitiveMatrixCode : ℕ := ⌜transitiveMatrixMeta⌝
private def rawMetaCode : ℕ := ⌜rawTransitiveMeta⌝
private def tagMetaCode : ℕ := ⌜taggedTransitiveMeta⌝
private def pairMetaCode : ℕ := ⌜taggedPairMeta⌝
private def b0Code : ℕ := ⌜(#0 : SyntacticSemiterm ℒₛₑₜ 1)⌝

theorem transitiveMatrix_quote : (⌜transitiveMatrixMeta⌝ : Semiformula V ℒₛₑₜ 2)=transitiveMatrix := by
  apply Bootstrapping.Semiformula.ext
  simp [transitiveMatrixMeta,transitiveMatrix,singTerm,seedMem,memTerm,eqTerm,
    Matrix.vecHead,Matrix.vecTail,Bootstrapping.iff]
theorem transitiveMatrixCode_eq : (transitiveMatrixCode : V)=(transitiveMatrix (V := V)).val := by
  rw [transitiveMatrixCode,FirstOrder.Semiformula.coe_quote_eq_quote]
  exact congrArg Bootstrapping.Semiformula.val (transitiveMatrix_quote (V := V))

def rawTransitiveBodyCode (a : V) : V := subst ℒₛₑₜ ((b0Code : V)∷a∷0) (rawMetaCode : V)
def taggedTransitiveBodyCode (a t : V) : V := subst ℒₛₑₜ ((b0Code : V)∷a∷t∷0) (tagMetaCode : V)
def taggedPairBodyCode (x y t : V) : V := subst ℒₛₑₜ ((b0Code : V)∷x∷y∷t∷0) (pairMetaCode : V)
def rawTransitiveBodyGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “out a. ∃ tail vec, !adjoinDef tail a 0 ∧ !adjoinDef vec ↑b0Code tail ∧
    !(Bootstrapping.substsGraph ℒₛₑₜ) out vec ↑rawMetaCode”
def taggedTransitiveBodyGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out a t. ∃ tail mid vec, !adjoinDef tail t 0 ∧ !adjoinDef mid a tail ∧
    !adjoinDef vec ↑b0Code mid ∧ !(Bootstrapping.substsGraph ℒₛₑₜ) out vec ↑tagMetaCode”
def taggedPairBodyGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out x y t. ∃ tail mid inner vec, !adjoinDef tail t 0 ∧ !adjoinDef mid y tail ∧
    !adjoinDef inner x mid ∧ !adjoinDef vec ↑b0Code inner ∧
    !(Bootstrapping.substsGraph ℒₛₑₜ) out vec ↑pairMetaCode”
instance rawTransitiveBody_defined : 𝚺₁-Function₁[V] rawTransitiveBodyCode via rawTransitiveBodyGraph :=
  .mk fun v => by simp [rawTransitiveBodyGraph,rawTransitiveBodyCode,numeral_eq_natCast]
instance taggedTransitiveBody_defined : 𝚺₁-Function₂[V] taggedTransitiveBodyCode via taggedTransitiveBodyGraph :=
  .mk fun v => by simp [taggedTransitiveBodyGraph,taggedTransitiveBodyCode,numeral_eq_natCast]
instance taggedPairBody_defined : 𝚺₁-Function₃[V] taggedPairBodyCode via taggedPairBodyGraph :=
  .mk fun v => by simp [taggedPairBodyGraph,taggedPairBodyCode,numeral_eq_natCast]

private theorem b0_cast : (b0Code : V)=(^#0 : V) := by
  rw [b0Code,FirstOrder.Semiterm.coe_quote_eq_quote]
  rfl

theorem rawTransitiveBodyCode_eq (a : Term V ℒₛₑₜ) :
    rawTransitiveBodyCode a.val=(rawTransitiveBody a).val := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rw [rawTransitiveBodyCode,rawMetaCode,FirstOrder.Semiformula.coe_quote_eq_quote,b0_cast]
  change ((⌜rawTransitiveMeta⌝ : Semiformula V ℒₛₑₜ 2).subst
    ![Bootstrapping.Semiterm.bvar 0,(Bootstrapping.Semiterm.fvar a : Semiterm V ℒₛₑₜ 1)]).val=_
  congr 1
  simp [rawTransitiveMeta,rawTransitiveBody,transitiveTerm,subsetTerm,memTerm,seedMem,
    SemitermVec.q,Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail]

theorem taggedTransitiveBodyCode_eq (a t : Term V ℒₛₑₜ) :
    taggedTransitiveBodyCode a.val t.val=(taggedTransitiveBody a t).val := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  rw [taggedTransitiveBodyCode,tagMetaCode,FirstOrder.Semiformula.coe_quote_eq_quote,b0_cast]
  change ((⌜taggedTransitiveMeta⌝ : Semiformula V ℒₛₑₜ 3).subst
    ![Bootstrapping.Semiterm.bvar 0,(Bootstrapping.Semiterm.fvar a : Semiterm V ℒₛₑₜ 1),
      Bootstrapping.Semiterm.fvar t]).val=_
  congr 1
  simp [taggedTransitiveMeta,taggedTransitiveBody,taggedTransitiveTerm,taggedSubsetTerm,memTerm,seedMem,
    SemitermVec.q,Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail]

theorem taggedPairBodyCode_eq (x y t : Term V ℒₛₑₜ) :
    taggedPairBodyCode x.val y.val t.val=(taggedPairBody x y t).val := by
  rcases term_is_fvar x with ⟨x,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  rw [taggedPairBodyCode,pairMetaCode,FirstOrder.Semiformula.coe_quote_eq_quote,b0_cast]
  change ((⌜taggedPairMeta⌝ : Semiformula V ℒₛₑₜ 4).subst
    ![Bootstrapping.Semiterm.bvar 0,(Bootstrapping.Semiterm.fvar x : Semiterm V ℒₛₑₜ 1),
      Bootstrapping.Semiterm.fvar y,Bootstrapping.Semiterm.fvar t]).val=_
  congr 1
  simp [taggedPairMeta,taggedPairBody,memTerm,eqTerm,seedMem,
    SemitermVec.q,Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail]

end LeanProofs.ZFCinPA.ValidatorSeedTransitive222

