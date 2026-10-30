import ZFCinPA.ValidatorSeedSourceBasis222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Actual finite source proofs of augmented raw comprehension. All formula
parameters are internally typed and may have arbitrary internal free labels.
No CP/GIC or semantic source-image premise is supplied. -/
namespace LeanProofs.ZFCinPA.ValidatorSeedRawComprehension222
open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory LO.Entailment LO.Entailment.FiniteContext
open ValidatorSourceFullSeed222 ValidatorFullSeedTheory222 ValidatorSeedSourceBasis222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] pairAt pairExists pairMatrix

def subsetTerm {n : ℕ} (p y : Semiterm V ℒₛₑₜ n) : Semiformula V ℒₛₑₜ n :=
  ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) p.bShift 🡒
    memTerm (Bootstrapping.Semiterm.bvar 0) y.bShift)

def singTerm {n : ℕ} (p y : Semiterm V ℒₛₑₜ n) : Semiformula V ℒₛₑₜ n :=
  ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) p.bShift 🡘
    eqTerm (Bootstrapping.Semiterm.bvar 0) y.bShift)

def closureTerm {n : ℕ} (K : Semiformula V ℒₛₑₜ 2)
    (c y : Semiterm V ℒₛₑₜ n) : Semiformula V ℒₛₑₜ n :=
  ∀⁰ (subsetTerm (Bootstrapping.Semiterm.bvar 0) y.bShift 🡒
    ∀⁰ (K.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 1] 🡒
      ∃⁰ (K.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 2] ⋏
        memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift.bShift.bShift)))

def supportBody (K : Semiformula V ℒₛₑₜ 2) (c y : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  K.subst ![y.bShift,Bootstrapping.Semiterm.bvar 0] ⋏ closureTerm K c.bShift y.bShift

def hitBody (K : Semiformula V ℒₛₑₜ 2) (p c : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  K.subst ![Bootstrapping.Semiterm.bvar 0,p.bShift] ⋏
    memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift

@[simp] theorem closureTerm_shift {n : ℕ} (K : Semiformula V ℒₛₑₜ 2)
    (c y : Semiterm V ℒₛₑₜ n) :
    (closureTerm K c y).shift=closureTerm K.shift c.shift y.shift := by
  simp [closureTerm,subsetTerm,memTerm,Bootstrapping.Semiformula.shift_substs,
    ←Bootstrapping.Semiterm.bShift_shift_comm]

@[simp] theorem supportBody_free (K : Semiformula V ℒₛₑₜ 2) (c y : Term V ℒₛₑₜ) :
    (supportBody K c y).free=
      (K.shift.subst ![y.shift,Bootstrapping.Semiterm.fvar 0] ⋏ closureTerm K.shift c.shift y.shift) := by
  rcases term_is_fvar c with ⟨c,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  simp [supportBody,closureTerm,subsetTerm,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail]

@[simp] theorem hitBody_free (K : Semiformula V ℒₛₑₜ 2) (p c : Term V ℒₛₑₜ) :
    (hitBody K p c).free=(K.shift.subst ![Bootstrapping.Semiterm.fvar 0,p.shift] ⋏
      memTerm (Bootstrapping.Semiterm.fvar 0) c.shift) := by
  rcases term_is_fvar p with ⟨p,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  simp [hitBody,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs]

private theorem pair_support_full (K : Semiformula V ℒₛₑₜ 2) (a c y : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt K a c 🡒 memTerm y c 🡒 ∃⁰ supportBody K c y := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  apply deduct'!
  have hp : [pairAt K (Bootstrapping.Semiterm.fvar a) (Bootstrapping.Semiterm.fvar c)] ⊢[Source V]
      pairAt K (Bootstrapping.Semiterm.fvar a) (Bootstrapping.Semiterm.fvar c) := by_axm₀!
  simp only [pairAt,pairMatrix,Bootstrapping.Semiformula.substs_and] at hp
  have hs := K!_left hp
  simp only [Bootstrapping.Semiformula.substs_all] at hs
  have hx := TProof.specialize_with_ctx! hs (Bootstrapping.Semiterm.fvar y)
  simpa [pairAt,pairMatrix,supportBody,closureTerm,subsetTerm,memTerm,seedMem,seedSubset,
    Bootstrapping.Semiformula.substs_substs,SemitermVec.q,Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail] using hx

theorem pair_closure (K : Semiformula V ℒₛₑₜ 2) (a c y : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt K a c 🡒 memTerm y c 🡒 closureTerm K c y := by
  have h : Source V ⊢ (∃⁰ supportBody K c y) 🡒 closureTerm K c y := by
    apply exists_elim
    rw [supportBody_free,closureTerm_shift]
    cl_prover
  cl_prover [pair_support_full K a c y,h]

def seedPairAt (K : Semiformula V ℒₛₑₜ 2) (a c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  pairAt K a c
def memberClosure (K : Semiformula V ℒₛₑₜ 2) (c y : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  closureTerm K c y
theorem full_member_closure (K : Semiformula V ℒₛₑₜ 2) (a c y : Term V ℒₛₑₜ) :
    Source V ⊢ seedPairAt K a c 🡒 memTerm y c 🡒 memberClosure K c y :=
  pair_closure K a c y

theorem closure_step (K : Semiformula V ℒₛₑₜ 2) (c y p v : Term V ℒₛₑₜ) :
    Source V ⊢ closureTerm K c y 🡒 subsetTerm p y 🡒 K.subst ![v,p] 🡒 ∃⁰ hitBody K p c := by
  rcases term_is_fvar c with ⟨c,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  rcases term_is_fvar p with ⟨p,rfl⟩
  rcases term_is_fvar v with ⟨v,rfl⟩
  apply deduct'!
  apply FiniteContext.deduct!
  have hc : [subsetTerm (Bootstrapping.Semiterm.fvar p) (Bootstrapping.Semiterm.fvar y),
      closureTerm K (Bootstrapping.Semiterm.fvar c) (Bootstrapping.Semiterm.fvar y)] ⊢[Source V]
      closureTerm K (Bootstrapping.Semiterm.fvar c) (Bootstrapping.Semiterm.fvar y) := by_axm!
  unfold closureTerm at hc
  have hs := TProof.specialize_with_ctx! hc (Bootstrapping.Semiterm.fvar p)
  simp [subsetTerm,memTerm,Bootstrapping.Semiformula.substs_substs,SemitermVec.q,
    Matrix.vecHead,Matrix.vecTail] at hs
  have hp : [subsetTerm (Bootstrapping.Semiterm.fvar p) (Bootstrapping.Semiterm.fvar y),
      closureTerm K (Bootstrapping.Semiterm.fvar c) (Bootstrapping.Semiterm.fvar y)] ⊢[Source V]
      subsetTerm (Bootstrapping.Semiterm.fvar p) (Bootstrapping.Semiterm.fvar y) := by_axm₀!
  have hp' := hp
  simp [closureTerm,subsetTerm,memTerm] at hp'
  have ha := show _ ⊢[Source V] _ from ⟨hs.get ⨀ hp'.get⟩
  have hv := TProof.specialize_with_ctx! ha (Bootstrapping.Semiterm.fvar v)
  simpa [closureTerm,subsetTerm,hitBody,memTerm,Bootstrapping.Semiformula.substs_substs,SemitermVec.q,
    Matrix.vecHead,Matrix.vecTail] using hv

theorem singleton_spec (p z w : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt p z 🡒 (memTerm w p 🡘 eqTerm w z) := by
  apply deduct'!
  have h : [singletonAt p z] ⊢[Source V] singletonAt p z := by_axm₀!
  unfold singletonAt at h
  simpa [singletonAt,eqTerm,memTerm] using TProof.specialize_with_ctx! h w

theorem singleton_mem (p z : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt p z 🡒 memTerm z p := by
  have h := singleton_spec p z z
  have hr : Source V ⊢ eqTerm z z := ⟨source_refl z⟩
  cl_prover [h,hr]

theorem singleton_unique (p r z a : Term V ℒₛₑₜ) :
    Source V ⊢ eqTerm p r 🡒 singletonAt p z 🡒 singletonAt r a 🡒 eqTerm z a := by
  have hz := singleton_mem p z
  have ha := singleton_spec r a z
  have hm := source_mem_ext z z p r
  have hr : Source V ⊢ eqTerm z z := ⟨source_refl z⟩
  have hm' : Source V ⊢ eqTerm p r 🡒 memTerm z p 🡒 memTerm z r := by
    cl_prover [hm,hr]
  have hz' : Source V ⊢ eqTerm p r 🡒 singletonAt p z 🡒 memTerm z r := by
    cl_prover [hm',hz]
  cl_prover [hz',ha]

@[simp] theorem singletonAt_shift (p z : Term V ℒₛₑₜ) :
    (singletonAt p z).shift=singletonAt p.shift z.shift := by
  simp [singletonAt,eqTerm,memTerm,←Bootstrapping.Semiterm.bShift_shift_comm]

@[simp] theorem subsetTerm_shift {n : ℕ} (p y : Semiterm V ℒₛₑₜ n) :
    (subsetTerm p y).shift=subsetTerm p.shift y.shift := by
  simp [subsetTerm,memTerm,←Bootstrapping.Semiterm.bShift_shift_comm]

@[simp] theorem singletonBody_free' (t : Term V ℒₛₑₜ) :
    (singletonBody t).free=singletonAt (Bootstrapping.Semiterm.fvar 0) t.shift := by
  rcases term_is_fvar t with ⟨t,rfl⟩
  simp [singletonBody,singletonAt,eqTerm,memTerm,Bootstrapping.Semiformula.free,
    SemitermVec.q]

attribute [local irreducible] singletonAt subsetTerm closureTerm supportBody hitBody

theorem singleton_subset (p z a : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt p z 🡒 memTerm z a 🡒 subsetTerm p a := by
  apply deduct'!
  apply FiniteContext.deduct!
  unfold subsetTerm
  apply TProof.generalize!
  have hs := FiniteContext.of'! (Γ := [memTerm z a,singletonAt p z].map Bootstrapping.Semiformula.shift)
    (singleton_spec p.shift z.shift (Bootstrapping.Semiterm.fvar 0))
  have hm := FiniteContext.of'! (Γ := [memTerm z a,singletonAt p z].map Bootstrapping.Semiformula.shift)
    (source_mem_congr z.shift (Bootstrapping.Semiterm.fvar 0) a.shift)
  have he := FiniteContext.of'! (Γ := [memTerm z a,singletonAt p z].map Bootstrapping.Semiformula.shift)
    (source_symm (Bootstrapping.Semiterm.fvar 0) z.shift)
  have hp : [memTerm z a,singletonAt p z].map Bootstrapping.Semiformula.shift ⊢[Source V]
      singletonAt p.shift z.shift := by simp only [List.map_cons,List.map_nil,singletonAt_shift]; exact by_axm!
  have hz : [memTerm z a,singletonAt p z].map Bootstrapping.Semiformula.shift ⊢[Source V]
      memTerm z.shift a.shift := by simp [memTerm] ; exact by_axm₀!
  simpa [memTerm,Bootstrapping.Semiformula.free,←Bootstrapping.Semiterm.bShift_shift_comm] using
    (show [memTerm z a,singletonAt p z].map Bootstrapping.Semiformula.shift ⊢[Source V]
      memTerm (Bootstrapping.Semiterm.fvar 0) p.shift 🡒 memTerm (Bootstrapping.Semiterm.fvar 0) a.shift from by
        cl_prover [hs,hm,he,hp,hz])

def rawAugMatrix (θ : Semiformula V ℒₛₑₜ 1) (a r : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 2 :=
  (eqTerm (Bootstrapping.Semiterm.bvar 1) r.bShift.bShift ⋏
    eqTerm (Bootstrapping.Semiterm.bvar 0) a.bShift.bShift) ⋎
  (singTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0) ⋏
    (memTerm (Bootstrapping.Semiterm.bvar 0) a.bShift.bShift ⋏
      θ.subst ![Bootstrapping.Semiterm.bvar 0]))

def rawAugBody (θ : Semiformula V ℒₛₑₜ 1) (a : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡘
    (eqTerm (Bootstrapping.Semiterm.bvar 0) a.bShift.bShift ⋎
      (memTerm (Bootstrapping.Semiterm.bvar 0) a.bShift.bShift ⋏
        θ.subst ![Bootstrapping.Semiterm.bvar 0])))

def rawAugAt (θ : Semiformula V ℒₛₑₜ 1) (a c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (rawAugBody θ a).subst ![c]

@[simp] theorem rawAugMatrix_shift (θ : Semiformula V ℒₛₑₜ 1) (a r : Term V ℒₛₑₜ) :
    (rawAugMatrix θ a r).shift=rawAugMatrix θ.shift a.shift r.shift := by
  simp [rawAugMatrix,singTerm,eqTerm,memTerm,Bootstrapping.Semiformula.shift_substs,
    ←Bootstrapping.Semiterm.bShift_shift_comm]

@[simp] theorem rawAugBody_shift (θ : Semiformula V ℒₛₑₜ 1) (a : Term V ℒₛₑₜ) :
    (rawAugBody θ a).shift=rawAugBody θ.shift a.shift := by
  simp [rawAugBody,eqTerm,memTerm,Bootstrapping.Semiformula.shift_substs,
    ←Bootstrapping.Semiterm.bShift_shift_comm]

@[simp] theorem rawAugBody_free (θ : Semiformula V ℒₛₑₜ 1) (a : Term V ℒₛₑₜ) :
    (rawAugBody θ a).free=rawAugAt θ.shift a.shift (Bootstrapping.Semiterm.fvar 0) := by
  simp [Bootstrapping.Semiformula.free,rawAugAt]

@[simp] theorem rawAugMatrix_subst (θ : Semiformula V ℒₛₑₜ 1) (a r y x : Term V ℒₛₑₜ) :
    (rawAugMatrix θ a r).subst ![y,x]=
      ((eqTerm x r ⋏ eqTerm y a) ⋎ (singletonAt x y ⋏ (memTerm y a ⋏ θ.subst ![y]))) := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar r with ⟨r,rfl⟩
  simp [rawAugMatrix,singTerm,singletonAt,eqTerm,memTerm,
    Bootstrapping.Semiformula.substs_substs,SemitermVec.q,Matrix.vecHead,Matrix.vecTail]

attribute [local irreducible] rawAugMatrix rawAugBody rawAugAt

private theorem eq_common_right (y z a : Term V ℒₛₑₜ) :
    Source V ⊢ eqTerm y a 🡒 eqTerm z a 🡒 eqTerm y z := by
  have hs := source_symm z a
  have ht := source_trans y a z
  cl_prover [hs,ht]

private theorem matrix_unique_root (θ : Semiformula V ℒₛₑₜ 1) (a r p y z : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt r a 🡒 eqTerm p r 🡒 eqTerm y a 🡒
      (rawAugMatrix θ a r).subst ![z,p] 🡒 eqTerm y z := by
  have hz := singleton_unique p r z a
  have hc := eq_common_right y z a
  have h : Source V ⊢ singletonAt r a 🡒 eqTerm p r 🡒
      (rawAugMatrix θ a r).subst ![z,p] 🡒 eqTerm z a := by
    rw [rawAugMatrix_subst]
    cl_prover [hz]
  cl_prover [h,hc]

private theorem matrix_unique_singleton (θ : Semiformula V ℒₛₑₜ 1) (a r p y z : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt r a 🡒 singletonAt p y 🡒
      (rawAugMatrix θ a r).subst ![z,p] 🡒 eqTerm y z := by
  have hy := singleton_unique p r y a
  have hc := eq_common_right y z a
  have hroot : Source V ⊢ singletonAt r a 🡒 singletonAt p y 🡒
      eqTerm p r 🡒 eqTerm z a 🡒 eqTerm y z := by cl_prover [hy,hc]
  have hp := singleton_unique p p y z
  have hr : Source V ⊢ eqTerm p p := ⟨source_refl p⟩
  have hsing : Source V ⊢ singletonAt p y 🡒 singletonAt p z 🡒 eqTerm y z := by
    cl_prover [hp,hr]
  rw [rawAugMatrix_subst]
  cl_prover [hroot,hsing]

private theorem matrix_unique (θ : Semiformula V ℒₛₑₜ 1) (a r p y z : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt r a 🡒 (rawAugMatrix θ a r).subst ![y,p] 🡒
      (rawAugMatrix θ a r).subst ![z,p] 🡒 eqTerm y z := by
  have hr := matrix_unique_root θ a r p y z
  have hs := matrix_unique_singleton θ a r p y z
  rw [rawAugMatrix_subst]
  cl_prover 48 [hr,hs]

private theorem matrix_root (θ : Semiformula V ℒₛₑₜ 1) (a r : Term V ℒₛₑₜ) :
    Source V ⊢ (rawAugMatrix θ a r).subst ![a,r] := by
  rw [rawAugMatrix_subst]
  have ha : Source V ⊢ eqTerm a a := ⟨source_refl a⟩
  have hr : Source V ⊢ eqTerm r r := ⟨source_refl r⟩
  cl_prover [ha,hr]

private theorem matrix_hit (θ : Semiformula V ℒₛₑₜ 1) (a r p v c : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt r a 🡒 (rawAugMatrix θ a r).subst ![v,p] 🡒
      (∃⁰ hitBody (rawAugMatrix θ a r) p c) 🡒 memTerm v c := by
  have h : Source V ⊢ (∃⁰ hitBody (rawAugMatrix θ a r) p c) 🡒
      (singletonAt r a 🡒 (rawAugMatrix θ a r).subst ![v,p] 🡒 memTerm v c) := by
    apply exists_elim
    rw [hitBody_free]
    simp only [Bootstrapping.Semiformula.shift_imp,singletonAt_shift,rawAugMatrix_shift,
      Bootstrapping.Semiformula.shift_substs]
    have hu := matrix_unique θ.shift a.shift r.shift p.shift (Bootstrapping.Semiterm.fvar 0) v.shift
    have hm := source_mem_congr (Bootstrapping.Semiterm.fvar 0) v.shift c.shift
    simpa [memTerm,Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail] using
      (show Source V ⊢
        ((rawAugMatrix θ.shift a.shift r.shift).subst ![Bootstrapping.Semiterm.fvar 0,p.shift] ⋏
          memTerm (Bootstrapping.Semiterm.fvar 0) c.shift) 🡒
        singletonAt r.shift a.shift 🡒 (rawAugMatrix θ.shift a.shift r.shift).subst ![v.shift,p.shift] 🡒
          memTerm v.shift c.shift from by cl_prover [hu,hm])
  cl_prover [h]

private theorem pair_aug_member (θ : Semiformula V ℒₛₑₜ 1) (a r c : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt r a 🡒 pairAt (rawAugMatrix θ a r) r c 🡒 memTerm a c := by
  have h := pair_request (rawAugMatrix θ a r) r c a
  have hr := matrix_root θ a r
  have hm := matrix_hit θ a r r a c
  have h' : Source V ⊢ pairAt (rawAugMatrix θ a r) r c 🡒
    (rawAugMatrix θ a r).subst ![a,r] 🡒 ∃⁰ hitBody (rawAugMatrix θ a r) r c := by
    simpa only [hitBody] using h
  cl_prover [h',hr,hm]

private def supportCore (K : Semiformula V ℒₛₑₜ 2) (z : Term V ℒₛₑₜ) :
    Semiformula V ℒₛₑₜ 1 := K.subst ![z.bShift,Bootstrapping.Semiterm.bvar 0]
private def rawProperty (θ : Semiformula V ℒₛₑₜ 1) (a z : Term V ℒₛₑₜ) :
    Formula V ℒₛₑₜ := eqTerm z a ⋎ (memTerm z a ⋏ θ.subst ![z])
@[simp] private theorem supportCore_free (K : Semiformula V ℒₛₑₜ 2) (z : Term V ℒₛₑₜ) :
    (supportCore K z).free=K.shift.subst ![z.shift,Bootstrapping.Semiterm.fvar 0] := by
  rcases term_is_fvar z with ⟨z,rfl⟩
  simp [supportCore,Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs,Matrix.vecHead,Matrix.vecTail]
@[simp] private theorem rawProperty_shift (θ : Semiformula V ℒₛₑₜ 1) (a z : Term V ℒₛₑₜ) :
    (rawProperty θ a z).shift=rawProperty θ.shift a.shift z.shift := by
  simp [rawProperty,eqTerm,memTerm,Bootstrapping.Semiformula.shift_substs,
    Matrix.vecHead,Matrix.vecTail]
attribute [local irreducible] supportCore rawProperty

private theorem pair_aug_cover (θ : Semiformula V ℒₛₑₜ 1) (a r c z : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt (rawAugMatrix θ a r) r c 🡒 memTerm z c 🡒
      (eqTerm z a ⋎ (memTerm z a ⋏ θ.subst ![z])) := by
  have he : Source V ⊢ (∃⁰ supportCore (rawAugMatrix θ a r) z) 🡒 rawProperty θ a z := by
    apply exists_elim
    rw [supportCore_free,rawProperty_shift,rawAugMatrix_shift,rawAugMatrix_subst]
    unfold rawProperty
    cl_prover
  have hs := pair_support (rawAugMatrix θ a r) r c z
  have he' : Source V ⊢ (∃⁰ (rawAugMatrix θ a r).subst ![z.bShift,Bootstrapping.Semiterm.bvar 0]) 🡒
      (eqTerm z a ⋎ (memTerm z a ⋏ θ.subst ![z])) := by
    simpa only [supportCore,rawProperty] using he
  cl_prover [hs,he']

private theorem pair_aug_step (θ : Semiformula V ℒₛₑₜ 1) (a r c z : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt r a 🡒 pairAt (rawAugMatrix θ a r) r c 🡒
      memTerm z a 🡒 θ.subst ![z] 🡒 memTerm z c := by
  have he : Source V ⊢ (∃⁰ singletonBody z) 🡒
      (singletonAt r a 🡒 pairAt (rawAugMatrix θ a r) r c 🡒
        memTerm z a 🡒 θ.subst ![z] 🡒 memTerm z c) := by
    apply exists_elim
    let p : Term V ℒₛₑₜ := Bootstrapping.Semiterm.fvar 0
    have hm := pair_aug_member θ.shift a.shift r.shift c.shift
    have hc := pair_closure (rawAugMatrix θ.shift a.shift r.shift) r.shift c.shift a.shift
    have hs := singleton_subset p z.shift a.shift
    have hst := closure_step (rawAugMatrix θ.shift a.shift r.shift) c.shift a.shift p z.shift
    have hh := matrix_hit θ.shift a.shift r.shift p z.shift c.shift
    have hk : Source V ⊢ singletonAt p z.shift 🡒 memTerm z.shift a.shift 🡒
        θ.shift.subst ![z.shift] 🡒 (rawAugMatrix θ.shift a.shift r.shift).subst ![z.shift,p] := by
      rw [rawAugMatrix_subst]; cl_prover
    have h : Source V ⊢ singletonAt p z.shift 🡒 singletonAt r.shift a.shift 🡒
        pairAt (rawAugMatrix θ.shift a.shift r.shift) r.shift c.shift 🡒
        memTerm z.shift a.shift 🡒 θ.shift.subst ![z.shift] 🡒 memTerm z.shift c.shift := by
      have hc' : Source V ⊢ singletonAt r.shift a.shift 🡒
          pairAt (rawAugMatrix θ.shift a.shift r.shift) r.shift c.shift 🡒
            closureTerm (rawAugMatrix θ.shift a.shift r.shift) c.shift a.shift := by
        cl_prover [hm,hc]
      have hst' : Source V ⊢ singletonAt p z.shift 🡒 memTerm z.shift a.shift 🡒
          θ.shift.subst ![z.shift] 🡒 closureTerm (rawAugMatrix θ.shift a.shift r.shift) c.shift a.shift 🡒
          ∃⁰ hitBody (rawAugMatrix θ.shift a.shift r.shift) p c.shift := by
        cl_prover [hs,hk,hst]
      have hh' : Source V ⊢ singletonAt p z.shift 🡒 memTerm z.shift a.shift 🡒
          θ.shift.subst ![z.shift] 🡒 singletonAt r.shift a.shift 🡒
          (∃⁰ hitBody (rawAugMatrix θ.shift a.shift r.shift) p c.shift) 🡒 memTerm z.shift c.shift := by
        cl_prover [hk,hh]
      cl_prover 64 [hc',hst',hh']
    simpa [singletonBody_free',singletonAt_shift,memTerm,
      Bootstrapping.Semiformula.shift_substs,Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail,p] using h
  have hz := singleton_object z
  exact ⟨he.get ⨀ hz.get⟩

private theorem rawAugAt_eq_all (θ : Semiformula V ℒₛₑₜ 1) (a c : Term V ℒₛₑₜ) :
    rawAugAt θ a c = ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift 🡘
      (eqTerm (Bootstrapping.Semiterm.bvar 0) a.bShift ⋎
        (memTerm (Bootstrapping.Semiterm.bvar 0) a.bShift ⋏ θ.subst ![Bootstrapping.Semiterm.bvar 0]))) := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  simp [rawAugAt,rawAugBody,eqTerm,memTerm,SemitermVec.q,
    Bootstrapping.Semiformula.substs_substs,Matrix.vecHead,Matrix.vecTail]

private theorem pair_aug (θ : Semiformula V ℒₛₑₜ 1) (a r c : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt r a 🡒 pairAt (rawAugMatrix θ a r) r c 🡒 rawAugAt θ a c := by
  apply deduct'!
  apply FiniteContext.deduct!
  rw [rawAugAt_eq_all]
  apply TProof.generalize!
  let Γ := [pairAt (rawAugMatrix θ a r) r c,singletonAt r a].map Bootstrapping.Semiformula.shift
  let z : Term V ℒₛₑₜ := Bootstrapping.Semiterm.fvar 0
  have hp : Γ ⊢[Source V] pairAt (rawAugMatrix θ.shift a.shift r.shift) r.shift c.shift := by
    simp only [Γ,List.map_cons,List.map_nil,pairAt_shift,rawAugMatrix_shift]
    exact by_axm₀!
  have hr : Γ ⊢[Source V] singletonAt r.shift a.shift := by
    simp only [Γ,List.map_cons,List.map_nil,singletonAt_shift]
    exact by_axm!
  have hc := FiniteContext.of'! (Γ := Γ) (pair_aug_cover θ.shift a.shift r.shift c.shift z)
  have hs := FiniteContext.of'! (Γ := Γ) (pair_aug_step θ.shift a.shift r.shift c.shift z)
  have hm := FiniteContext.of'! (Γ := Γ) (pair_aug_member θ.shift a.shift r.shift c.shift)
  have ht := FiniteContext.of'! (Γ := Γ) (source_mem_congr a.shift z c.shift)
  have he := FiniteContext.of'! (Γ := Γ) (source_symm z a.shift)
  have hcover : Γ ⊢[Source V] memTerm z c.shift 🡒
      (eqTerm z a.shift ⋎ (memTerm z a.shift ⋏ θ.shift.subst ![z])) := by
    cl_prover [hp,hc]
  have hmember : Γ ⊢[Source V] memTerm a.shift c.shift := by cl_prover [hr,hp,hm]
  have hroot : Γ ⊢[Source V] eqTerm z a.shift 🡒 memTerm z c.shift := by
    cl_prover [hmember,ht,he]
  have hselected : Γ ⊢[Source V] memTerm z a.shift 🡒 θ.shift.subst ![z] 🡒 memTerm z c.shift := by
    cl_prover [hr,hp,hs]
  have h : Γ ⊢[Source V] memTerm z c.shift 🡘
      (eqTerm z a.shift ⋎ (memTerm z a.shift ⋏ θ.shift.subst ![z])) := by
    cl_prover [hcover,hroot,hselected]
  simpa [Γ,z,eqTerm,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.comp_vecCons',Matrix.vecHead,Matrix.vecTail,
    ←Bootstrapping.Semiterm.bShift_shift_comm] using h

private theorem augmented_of_singleton (θ : Semiformula V ℒₛₑₜ 1) (a r : Term V ℒₛₑₜ) :
    Source V ⊢ singletonAt r a 🡒 ∃⁰ rawAugBody θ a := by
  have h : [singletonAt r a] ⊢[Source V]
      (∃⁰ pairExists (rawAugMatrix θ a r) r) 🡒 ∃⁰ rawAugBody θ a := by
    apply TProof.exs_imp_exs!
    rw [pairExists_free,rawAugBody_free,rawAugMatrix_shift]
    have hp := FiniteContext.of'! (Γ := [singletonAt r a].map Bootstrapping.Semiformula.shift)
      (pair_aug θ.shift a.shift r.shift (Bootstrapping.Semiterm.fvar 0))
    have hs : [singletonAt r a].map Bootstrapping.Semiformula.shift ⊢[Source V]
        singletonAt r.shift a.shift := by
      simp only [List.map_cons,List.map_nil,singletonAt_shift]; exact by_axm₀!
    cl_prover [hp,hs]
  have hx := FiniteContext.of'! (Γ := [singletonAt r a]) (pair_exists (rawAugMatrix θ a r) r)
  apply deduct'!
  exact ⟨h.get ⨀ hx.get⟩

/-- Augmented raw comprehension with arbitrary internal matrix and parameters.
The proof uses only equality, full seed and singleton; no irreflexivity step
or congruence induction on the arbitrary matrix is needed. -/
theorem raw_augmented (θ : Semiformula V ℒₛₑₜ 1) (a : Term V ℒₛₑₜ) :
    Source V ⊢ ∃⁰ rawAugBody θ a := by
  have h : Source V ⊢ (∃⁰ singletonBody a) 🡒 ∃⁰ rawAugBody θ a := by
    apply exists_elim
    have h' := augmented_of_singleton θ.shift a.shift (Bootstrapping.Semiterm.fvar 0)
    simpa only [singletonBody_free',Bootstrapping.Semiformula.shift_exs,rawAugBody_shift] using h'
  exact ⟨h.get ⨀ (singleton_object a).get⟩

def rawAugProof (θ : Semiformula V ℒₛₑₜ 1) (a : Term V ℒₛₑₜ) :
    Source V ⊢! ∃⁰ rawAugBody θ a := (raw_augmented θ a).get

theorem rawAugProof_isProof (θ : Semiformula V ℒₛₑₜ 1) (a : Term V ℒₛₑₜ) :
    Proof seedTheory (rawAugProof θ a).val (∃⁰ rawAugBody θ a).val := by
  simpa only [Source,Theory.internalize,Proof,Sequent.val_insert,Sequent.val_empty,singleton_eq_insert] using (rawAugProof θ a).derivationOf

/-! Fixed total raw syntax constructors; no total proof-search graph is claimed. -/
def eqMeta : SetTheorySemiproposition 2 :=
  FirstOrder.Semiformula.rel Language.Eq.eq ![#0,#1]
def singMeta : SetTheorySemiproposition 2 :=
  ∀⁰ (seedMem 3 0 2 🡘 FirstOrder.Semiformula.rel Language.Eq.eq ![#0,#1])
def eqCode : ℕ := ⌜eqMeta⌝
def memCode : ℕ := ⌜seedMem 2 0 1⌝
def singCode : ℕ := ⌜singMeta⌝
def b0Code : ℕ := ⌜(#0 : SyntacticSemiterm ℒₛₑₜ 2)⌝
def b1Code : ℕ := ⌜(#1 : SyntacticSemiterm ℒₛₑₜ 2)⌝
def at2Code (u v k : V) : V := subst ℒₛₑₜ (u∷v∷0) k
def at1Code (u k : V) : V := subst ℒₛₑₜ (u∷0) k
def at2Graph : 𝚺₁.Semisentence 4 := .mkSigma
  “out u v k. ∃ tail vec, !adjoinDef tail v 0 ∧ !adjoinDef vec u tail ∧
    !(Bootstrapping.substsGraph ℒₛₑₜ) out vec k”
def at1Graph : 𝚺₁.Semisentence 3 := .mkSigma
  “out u k. ∃ vec, !adjoinDef vec u 0 ∧ !(Bootstrapping.substsGraph ℒₛₑₜ) out vec k”
instance at2_defined : 𝚺₁-Function₃ (at2Code : V→V→V→V) via at2Graph :=
  .mk fun v => by simp [at2Graph,at2Code]
instance at1_defined : 𝚺₁-Function₂ (at1Code : V→V→V) via at1Graph :=
  .mk fun v => by simp [at1Graph,at1Code]

/-- Inputs a and r are raw term codes, not numeric free-variable labels. -/
def rawAugMatrixCode (k a r : V) : V :=
  (at2Code b1Code r eqCode ^⋏ at2Code b0Code a eqCode) ^⋎
    ((singCode : V) ^⋏ (at2Code b0Code a memCode ^⋏ at1Code b0Code k))
def rawAugBodyCode (k a : V) : V :=
  ^∀ (Bootstrapping.iff ℒₛₑₜ (memCode : V)
    (at2Code b0Code a eqCode ^⋎ (at2Code b0Code a memCode ^⋏ at1Code b0Code k)))

def rawAugMatrixGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out k a r. ∃ er ea ma th root tail right,
    !at2Graph er ↑b1Code r ↑eqCode ∧ !at2Graph ea ↑b0Code a ↑eqCode ∧
    !at2Graph ma ↑b0Code a ↑memCode ∧ !at1Graph th ↑b0Code k ∧
    !qqAndDef root er ea ∧ !qqAndDef tail ma th ∧
    !qqAndDef right ↑singCode tail ∧ !qqOrDef out root right”
def rawAugBodyGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out k a. ∃ ea ma th tail right body,
    !at2Graph ea ↑b0Code a ↑eqCode ∧ !at2Graph ma ↑b0Code a ↑memCode ∧
    !at1Graph th ↑b0Code k ∧ !qqAndDef tail ma th ∧ !qqOrDef right ea tail ∧
    !(Bootstrapping.iffGraph ℒₛₑₜ) body ↑memCode right ∧ !qqAllDef out body”

instance rawAugMatrix_defined : 𝚺₁-Function₃ (rawAugMatrixCode : V→V→V→V) via rawAugMatrixGraph :=
  .mk fun v => by simp [rawAugMatrixGraph,rawAugMatrixCode,numeral_eq_natCast]
instance rawAugBody_defined : 𝚺₁-Function₂ (rawAugBodyCode : V→V→V) via rawAugBodyGraph :=
  .mk fun v => by simp [rawAugBodyGraph,rawAugBodyCode,numeral_eq_natCast]

lemma b0_cast : (b0Code : V)=(^#0 : V) := by
  rw [b0Code,FirstOrder.Semiterm.coe_quote_eq_quote]
  rfl
lemma b1_cast : (b1Code : V)=(^#1 : V) := by
  rw [b1Code,FirstOrder.Semiterm.coe_quote_eq_quote]
  simp [FirstOrder.Semiterm.quote_def]
lemma eq_cast : (eqCode : V)=(⌜eqMeta⌝ : V) :=
  FirstOrder.Semiformula.coe_quote_eq_quote eqMeta
lemma mem_cast : (memCode : V)=(⌜seedMem 2 0 1⌝ : V) :=
  FirstOrder.Semiformula.coe_quote_eq_quote (seedMem 2 0 1)
lemma sing_cast : (singCode : V)=(⌜singMeta⌝ : V) :=
  FirstOrder.Semiformula.coe_quote_eq_quote singMeta

theorem at2_eq {n : ℕ} (u v : Semiterm V ℒₛₑₜ n) :
    at2Code u.val v.val eqCode=(eqTerm u v).val := by
  rw [eq_cast]
  change (((⌜eqMeta⌝ : Semiformula V ℒₛₑₜ 2).subst ![u,v]).val)=(eqTerm u v).val
  congr 1
  simp [eqMeta,eqTerm,Matrix.vecHead,Matrix.vecTail]
theorem at2_mem {n : ℕ} (u v : Semiterm V ℒₛₑₜ n) :
    at2Code u.val v.val memCode=(memTerm u v).val := by
  rw [mem_cast]
  change (((⌜seedMem 2 0 1⌝ : Semiformula V ℒₛₑₜ 2).subst ![u,v]).val)=(memTerm u v).val
  congr 1
  simp [seedMem,memTerm,Matrix.vecHead,Matrix.vecTail]

theorem rawAugMatrixCode_eq (θ : Semiformula V ℒₛₑₜ 1) (a r : Term V ℒₛₑₜ) :
    rawAugMatrixCode θ.val a.val r.val=(rawAugMatrix θ a r).val := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  rcases term_is_fvar r with ⟨r,rfl⟩
  have he0 := at2_eq (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar a)
  have hm0 := at2_mem (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar a)
  have he1 := at2_eq (Bootstrapping.Semiterm.bvar (1 : Fin 2)) (Bootstrapping.Semiterm.fvar r)
  simp [Bootstrapping.Semiterm.bvar,Bootstrapping.Semiterm.fvar,eqTerm,memTerm] at he0 hm0 he1
  simp only [rawAugMatrixCode,b0_cast,b1_cast,Bootstrapping.Semiterm.fvar,he0,hm0,he1]
  simp [rawAugMatrix,at1Code,sing_cast,singMeta,seedMem,singTerm,eqTerm,memTerm,
    FirstOrder.Semiformula.quote_def,Matrix.vecHead,Matrix.vecTail]

theorem rawAugBodyCode_eq (θ : Semiformula V ℒₛₑₜ 1) (a : Term V ℒₛₑₜ) :
    rawAugBodyCode θ.val a.val=(rawAugBody θ a).val := by
  rcases term_is_fvar a with ⟨a,rfl⟩
  have he0 := at2_eq (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar a)
  have hm0 := at2_mem (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar a)
  simp [Bootstrapping.Semiterm.bvar,Bootstrapping.Semiterm.fvar,eqTerm,memTerm] at he0 hm0
  simp only [rawAugBodyCode,b0_cast,Bootstrapping.Semiterm.fvar,he0,hm0]
  simp [rawAugBody,at1Code,mem_cast,seedMem,eqTerm,memTerm,
    FirstOrder.Semiformula.quote_def,Matrix.vecHead,Matrix.vecTail,Bootstrapping.iff]

end LeanProofs.ZFCinPA.ValidatorSeedRawComprehension222

