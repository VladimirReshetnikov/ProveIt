import ZFCinPA.ValidatorSeedRawComprehension222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Actual finite source proofs of pairs, two-root and guarded comprehension. All formula
parameters are internally typed and may have arbitrary internal free labels.
No CP/GIC or semantic source-image premise is supplied. -/
namespace LeanProofs.ZFCinPA.ValidatorSeedGuardedComprehension222
open Classical
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory LO.Entailment LO.Entailment.FiniteContext
open ValidatorSourceFullSeed222 ValidatorFullSeedTheory222 ValidatorSeedSourceBasis222
open ValidatorSeedRawComprehension222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] pairAt pairExists pairMatrix

attribute [local irreducible] singletonAt subsetTerm closureTerm supportBody hitBody

theorem source_mem_right (z a b : Term V ℒₛₑₜ) :
    Source V ⊢ eqTerm a b 🡒 memTerm z a 🡒 memTerm z b := by
  have h := source_mem_ext z z a b
  have hr : Source V ⊢ eqTerm z z := ⟨source_refl z⟩
  cl_prover [h,hr]

theorem source_irrefl (t : Term V ℒₛₑₜ) : Source V ⊢ ∼memTerm t t := by
  have hm : (⌜irreflexiveSentence⌝ : V)∈seedTheory.Δ₁Class :=
    Δ₁Class.mem_iff.mpr (Or.inl (Or.inr (by simp)))
  have h : Source V ⊢! (⌜(Rewriting.emb irreflexiveSentence : SetTheoryProposition)⌝ : Formula V ℒₛₑₜ) :=
    TProof.byAxm hm
  have hv : (fun i : Fin 2 => (⌜(![#0,#0] i : SyntacticSemiterm ℒₛₑₜ 1)⌝ :
      Semiterm V ℒₛₑₜ 1)) = ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.bvar 0] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  have h' : Source V ⊢! ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0)
    (Bootstrapping.Semiterm.bvar 0) 🡒 ⊥) := by
    simpa [irreflexiveSentence,FirstOrder.Semiformula.Operator.mem_def,
      memTerm,FirstOrder.Semiformula.quote_def,hv] using h
  have ht : Source V ⊢ memTerm t t 🡒 ⊥ := by
    simpa [memTerm] using (show Source V ⊢ _ from ⟨TProof.specialize h' t⟩)
  cl_prover [ht]

@[simp] theorem emptyAt_shift (t : Term V ℒₛₑₜ) :
    (emptyAt t).shift=emptyAt t.shift := by
  simp [emptyAt,memTerm,←Bootstrapping.Semiterm.bShift_shift_comm]

theorem empty_spec (t z : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∼memTerm z t := by
  apply deduct'!
  have h : [emptyAt t] ⊢[Source V] emptyAt t := by_axm₀!
  unfold emptyAt at h
  have hz : [emptyAt t] ⊢[Source V] memTerm z t 🡒 ⊥ := by
    simpa [emptyAt,memTerm] using TProof.specialize_with_ctx! h z
  cl_prover [hz]

theorem empty_subset (t a : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 subsetTerm t a := by
  apply deduct'!
  unfold subsetTerm
  apply TProof.generalize!
  have he := FiniteContext.of'! (Γ := [emptyAt t].map Bootstrapping.Semiformula.shift)
    (empty_spec t.shift (Bootstrapping.Semiterm.fvar 0))
  have hh : [emptyAt t].map Bootstrapping.Semiformula.shift ⊢[Source V] emptyAt t.shift := by
    simp only [List.map_cons,List.map_nil,emptyAt_shift]
    exact by_axm₀!
  simpa [memTerm,Bootstrapping.Semiformula.free,←Bootstrapping.Semiterm.bShift_shift_comm] using
    (show [emptyAt t].map Bootstrapping.Semiformula.shift ⊢[Source V]
      memTerm (Bootstrapping.Semiterm.fvar 0) t.shift 🡒
        memTerm (Bootstrapping.Semiterm.fvar 0) a.shift from by cl_prover [he,hh])

theorem singleton_ne_empty (t r z : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 singletonAt r z 🡒 ∼eqTerm r t := by
  have hm := singleton_mem r z
  have hx := source_mem_right z r t
  have he := empty_spec t z
  cl_prover [hm,hx,he]

def supportCore (K : Semiformula V ℒₛₑₜ 2) (z : Term V ℒₛₑₜ) :
    Semiformula V ℒₛₑₜ 1 := K.subst ![z.bShift,Bootstrapping.Semiterm.bvar 0]
@[simp] theorem supportCore_free (K : Semiformula V ℒₛₑₜ 2) (z : Term V ℒₛₑₜ) :
    (supportCore K z).free=K.shift.subst ![z.shift,Bootstrapping.Semiterm.fvar 0] := by
  rcases term_is_fvar z with ⟨z,rfl⟩
  simp [supportCore,Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs,Matrix.vecHead,Matrix.vecTail]

theorem hit_member (K : Semiformula V ℒₛₑₜ 2) (p c z : Term V ℒₛₑₜ)
    (H : Formula V ℒₛₑₜ)
    (h : Source V ⊢ H.shift 🡒
      K.shift.subst ![Bootstrapping.Semiterm.fvar 0,p.shift] 🡒
        eqTerm (Bootstrapping.Semiterm.fvar 0) z.shift) :
    Source V ⊢ H 🡒 (∃⁰ hitBody K p c) 🡒 memTerm z c := by
  have he : Source V ⊢ (∃⁰ hitBody K p c) 🡒 (H 🡒 memTerm z c) := by
    apply exists_elim
    rw [hitBody_free]
    have hm := source_mem_congr (Bootstrapping.Semiterm.fvar 0) z.shift c.shift
    simpa only [Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_rel,
      memTerm,Matrix.map_cons,Matrix.map_nil] using
      (show Source V ⊢
        (K.shift.subst ![Bootstrapping.Semiterm.fvar 0,p.shift] ⋏
          memTerm (Bootstrapping.Semiterm.fvar 0) c.shift) 🡒
        (H.shift 🡒 memTerm z.shift c.shift) from by cl_prover [h,hm])
  cl_prover [he]

def rawPairMatrix (t r x y : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 2 :=
  (eqTerm (Bootstrapping.Semiterm.bvar 1) r.bShift.bShift ⋏
    eqTerm (Bootstrapping.Semiterm.bvar 0) x.bShift.bShift) ⋎
  (eqTerm (Bootstrapping.Semiterm.bvar 1) t.bShift.bShift ⋏
    eqTerm (Bootstrapping.Semiterm.bvar 0) y.bShift.bShift)
def rawPairBody (x y : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡘
    (eqTerm (Bootstrapping.Semiterm.bvar 0) x.bShift.bShift ⋎
      eqTerm (Bootstrapping.Semiterm.bvar 0) y.bShift.bShift))
def rawPairAt (x y c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (rawPairBody x y).subst ![c]

@[simp] theorem rawPairMatrix_shift (t r x y : Term V ℒₛₑₜ) :
    (rawPairMatrix t r x y).shift=rawPairMatrix t.shift r.shift x.shift y.shift := by
  simp [rawPairMatrix,eqTerm,←Bootstrapping.Semiterm.bShift_shift_comm]
@[simp] theorem rawPairBody_shift (x y : Term V ℒₛₑₜ) :
    (rawPairBody x y).shift=rawPairBody x.shift y.shift := by
  simp [rawPairBody,memTerm,eqTerm,←Bootstrapping.Semiterm.bShift_shift_comm]
@[simp] theorem rawPairAt_shift (x y c : Term V ℒₛₑₜ) :
    (rawPairAt x y c).shift=rawPairAt x.shift y.shift c.shift := by
  simp [rawPairAt,Bootstrapping.Semiformula.shift_substs,Matrix.vecHead,Matrix.vecTail]
@[simp] theorem rawPairBody_free (x y : Term V ℒₛₑₜ) :
    (rawPairBody x y).free=rawPairAt x.shift y.shift (Bootstrapping.Semiterm.fvar 0) := by
  simp [Bootstrapping.Semiformula.free,rawPairAt]
@[simp] theorem rawPairMatrix_subst (t r x y z p : Term V ℒₛₑₜ) :
    (rawPairMatrix t r x y).subst ![z,p]=
      ((eqTerm p r ⋏ eqTerm z x) ⋎ (eqTerm p t ⋏ eqTerm z y)) := by
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar r with ⟨r,rfl⟩
  rcases term_is_fvar x with ⟨x,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  simp [rawPairMatrix,eqTerm]

theorem rawPairAt_spec (x y c z : Term V ℒₛₑₜ) :
    Source V ⊢ rawPairAt x y c 🡒 (memTerm z c 🡘 (eqTerm z x ⋎ eqTerm z y)) := by
  rcases term_is_fvar x with ⟨x,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  apply deduct'!
  have h : [rawPairAt (Bootstrapping.Semiterm.fvar x) (Bootstrapping.Semiterm.fvar y) (Bootstrapping.Semiterm.fvar c)] ⊢[Source V] rawPairAt (Bootstrapping.Semiterm.fvar x) (Bootstrapping.Semiterm.fvar y) (Bootstrapping.Semiterm.fvar c) := by_axm₀!
  simp only [rawPairAt,rawPairBody,Bootstrapping.Semiformula.substs_all] at h
  simpa [rawPairAt,rawPairBody,eqTerm,memTerm,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using TProof.specialize_with_ctx! h z

attribute [local irreducible] rawPairMatrix rawPairBody rawPairAt supportCore

private theorem pair_first (t r x y c : Term V ℒₛₑₜ) :
    Source V ⊢ ∼eqTerm r t 🡒 pairAt (rawPairMatrix t r x y) r c 🡒 memTerm x c := by
  have hh := hit_member (rawPairMatrix t r x y) r c x (∼eqTerm r t) (by
    rw [rawPairMatrix_shift,rawPairMatrix_subst]
    simp only [eqTerm,Bootstrapping.Semiformula.shift_neg,Bootstrapping.Semiformula.shift_rel,
      Matrix.map_cons,Matrix.map_nil]
    cl_prover)
  have hr := pair_request (rawPairMatrix t r x y) r c x
  have hk : Source V ⊢ (rawPairMatrix t r x y).subst ![x,r] := by
    rw [rawPairMatrix_subst]
    have hx : Source V ⊢ eqTerm x x := ⟨source_refl x⟩
    have ha : Source V ⊢ eqTerm r r := ⟨source_refl r⟩
    cl_prover [hx,ha]
  have hr' : Source V ⊢ pairAt (rawPairMatrix t r x y) r c 🡒
      (rawPairMatrix t r x y).subst ![x,r] 🡒 ∃⁰ hitBody (rawPairMatrix t r x y) r c := by simpa only [hitBody] using hr
  cl_prover [hh,hr',hk]

private theorem pair_second (t r x y c : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∼eqTerm r t 🡒 pairAt (rawPairMatrix t r x y) r c 🡒 memTerm y c := by
  have hh := hit_member (rawPairMatrix t r x y) t c y (∼eqTerm r t) (by
    rw [rawPairMatrix_shift,rawPairMatrix_subst]
    have hs := source_symm t.shift r.shift
    simpa [eqTerm,Bootstrapping.Semiformula.shift_neg] using
      (show Source V ⊢ ∼eqTerm r.shift t.shift 🡒
        ((eqTerm t.shift r.shift ⋏ eqTerm (Bootstrapping.Semiterm.fvar 0) x.shift) ⋎
          (eqTerm t.shift t.shift ⋏ eqTerm (Bootstrapping.Semiterm.fvar 0) y.shift)) 🡒
        eqTerm (Bootstrapping.Semiterm.fvar 0) y.shift from by cl_prover [hs]))
  have hf := pair_first t r x y c
  have hc := pair_closure (rawPairMatrix t r x y) r c x
  have he := empty_subset t x
  have hstep := closure_step (rawPairMatrix t r x y) c x t y
  have hk : Source V ⊢ (rawPairMatrix t r x y).subst ![y,t] := by
    rw [rawPairMatrix_subst]
    have ht : Source V ⊢ eqTerm t t := ⟨source_refl t⟩
    have hy : Source V ⊢ eqTerm y y := ⟨source_refl y⟩
    cl_prover [ht,hy]
  have hcl : Source V ⊢ ∼eqTerm r t 🡒 pairAt (rawPairMatrix t r x y) r c 🡒
      closureTerm (rawPairMatrix t r x y) c x := by cl_prover [hf,hc]
  have hh' : Source V ⊢ emptyAt t 🡒 ∼eqTerm r t 🡒
      pairAt (rawPairMatrix t r x y) r c 🡒 ∃⁰ hitBody (rawPairMatrix t r x y) t c := by
    cl_prover 80 [hcl,he,hstep,hk]
  cl_prover [hh',hh]

private theorem pair_cover (t r x y c z : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt (rawPairMatrix t r x y) r c 🡒 memTerm z c 🡒
      (eqTerm z x ⋎ eqTerm z y) := by
  have he : Source V ⊢ (∃⁰ supportCore (rawPairMatrix t r x y) z) 🡒
      (eqTerm z x ⋎ eqTerm z y) := by
    apply exists_elim
    rw [supportCore_free,rawPairMatrix_shift,rawPairMatrix_subst]
    simp only [eqTerm,Bootstrapping.Semiformula.shift_or,Bootstrapping.Semiformula.shift_rel,
      Matrix.map_cons,Matrix.map_nil]
    cl_prover
  have hs : Source V ⊢ pairAt (rawPairMatrix t r x y) r c 🡒 memTerm z c 🡒
      ∃⁰ supportCore (rawPairMatrix t r x y) z := by
    simpa only [supportCore] using pair_support (rawPairMatrix t r x y) r c z
  cl_prover [he,hs]

private theorem rawPairAt_eq_all (x y c : Term V ℒₛₑₜ) :
    rawPairAt x y c=∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift 🡘
      (eqTerm (Bootstrapping.Semiterm.bvar 0) x.bShift ⋎
        eqTerm (Bootstrapping.Semiterm.bvar 0) y.bShift)) := by
  rcases term_is_fvar x with ⟨x,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  simp [rawPairAt,rawPairBody,eqTerm,memTerm,SemitermVec.q,Matrix.vecHead,Matrix.vecTail]

private theorem pair_exact (t r x y c : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∼eqTerm r t 🡒
      pairAt (rawPairMatrix t r x y) r c 🡒 rawPairAt x y c := by
  apply deduct'!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  rw [rawPairAt_eq_all]
  apply TProof.generalize!
  let Γ := [pairAt (rawPairMatrix t r x y) r c,∼eqTerm r t,emptyAt t].map Bootstrapping.Semiformula.shift
  let z : Term V ℒₛₑₜ := Bootstrapping.Semiterm.fvar 0
  have hp : Γ ⊢[Source V] pairAt (rawPairMatrix t.shift r.shift x.shift y.shift) r.shift c.shift := by
    simp only [Γ,List.map_cons,List.map_nil,pairAt_shift,rawPairMatrix_shift]
    exact by_axm₀!
  have ht : Γ ⊢[Source V] emptyAt t.shift := by
    simp only [Γ,List.map_cons,List.map_nil,emptyAt_shift]
    exact by_axm!
  have hn : Γ ⊢[Source V] ∼eqTerm r.shift t.shift := by
    simp only [Γ,List.map_cons,List.map_nil,eqTerm,Bootstrapping.Semiformula.shift_neg,
      Bootstrapping.Semiformula.shift_rel,Matrix.map_cons,Matrix.map_nil]
    exact by_axm!
  have h1 := FiniteContext.of'! (Γ := Γ) (pair_first t.shift r.shift x.shift y.shift c.shift)
  have h2 := FiniteContext.of'! (Γ := Γ) (pair_second t.shift r.shift x.shift y.shift c.shift)
  have hf := FiniteContext.of'! (Γ := Γ) (pair_cover t.shift r.shift x.shift y.shift c.shift z)
  have hx : Γ ⊢[Source V] memTerm x.shift c.shift := by cl_prover [h1,hn,hp]
  have hy : Γ ⊢[Source V] memTerm y.shift c.shift := by cl_prover [h2,ht,hn,hp]
  have hsx := FiniteContext.of'! (Γ := Γ) (source_symm z x.shift)
  have hsy := FiniteContext.of'! (Γ := Γ) (source_symm z y.shift)
  have hmx := FiniteContext.of'! (Γ := Γ) (source_mem_congr x.shift z c.shift)
  have hmy := FiniteContext.of'! (Γ := Γ) (source_mem_congr y.shift z c.shift)
  have hx' : Γ ⊢[Source V] eqTerm z x.shift 🡒 memTerm z c.shift := by cl_prover [hx,hsx,hmx]
  have hy' : Γ ⊢[Source V] eqTerm z y.shift 🡒 memTerm z c.shift := by cl_prover [hy,hsy,hmy]
  have h : Γ ⊢[Source V] memTerm z c.shift 🡘 (eqTerm z x.shift ⋎ eqTerm z y.shift) := by
    cl_prover [hf,hp,hx',hy']
  simpa [Γ,z,eqTerm,memTerm,Bootstrapping.Semiformula.free,
    ←Bootstrapping.Semiterm.bShift_shift_comm] using h

private theorem pair_of_roots (t r x y : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∼eqTerm r t 🡒 ∃⁰ rawPairBody x y := by
  apply deduct'!
  apply FiniteContext.deduct!
  let Γ := [∼eqTerm r t,emptyAt t]
  have h : Γ ⊢[Source V] (∃⁰ pairExists (rawPairMatrix t r x y) r) 🡒 ∃⁰ rawPairBody x y := by
    apply TProof.exs_imp_exs!
    rw [pairExists_free,rawPairBody_free,rawPairMatrix_shift]
    have hp := FiniteContext.of'! (Γ := Γ.map Bootstrapping.Semiformula.shift)
      (pair_exact t.shift r.shift x.shift y.shift (Bootstrapping.Semiterm.fvar 0))
    have he : Γ.map Bootstrapping.Semiformula.shift ⊢[Source V] emptyAt t.shift := by
      simp only [Γ,List.map_cons,List.map_nil,emptyAt_shift]; exact by_axm!
    have hn : Γ.map Bootstrapping.Semiformula.shift ⊢[Source V] ∼eqTerm r.shift t.shift := by
      simp only [Γ,List.map_cons,List.map_nil,eqTerm,Bootstrapping.Semiformula.shift_neg,
        Bootstrapping.Semiformula.shift_rel,Matrix.map_cons,Matrix.map_nil]; exact by_axm₀!
    cl_prover [hp,he,hn]
  have hx := FiniteContext.of'! (Γ := Γ) (pair_exists (rawPairMatrix t r x y) r)
  exact ⟨h.get ⨀ hx.get⟩

theorem raw_pair_of_empty (t x y : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∃⁰ rawPairBody x y := by
  have h : Source V ⊢ (∃⁰ singletonBody t) 🡒 (emptyAt t 🡒 ∃⁰ rawPairBody x y) := by
    apply exists_elim
    rw [singletonBody_free']
    have hn := singleton_ne_empty t.shift (Bootstrapping.Semiterm.fvar 0) t.shift
    have hp := pair_of_roots t.shift (Bootstrapping.Semiterm.fvar 0) x.shift y.shift
    simpa only [Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_exs,
      emptyAt_shift,rawPairBody_shift] using
      (show Source V ⊢ singletonAt (Bootstrapping.Semiterm.fvar 0) t.shift 🡒
        emptyAt t.shift 🡒 ∃⁰ rawPairBody x.shift y.shift from by cl_prover [hn,hp])
  exact ⟨h.get ⨀ (singleton_object t).get⟩

theorem raw_pair (x y : Term V ℒₛₑₜ) : Source V ⊢ ∃⁰ rawPairBody x y := by
  have h : Source V ⊢ (∃⁰ emptyBody) 🡒 ∃⁰ rawPairBody x y := by
    apply exists_elim
    simpa only [emptyBody_free,Bootstrapping.Semiformula.shift_exs,rawPairBody_shift] using
      raw_pair_of_empty (Bootstrapping.Semiterm.fvar 0) x.shift y.shift
  exact ⟨h.get ⨀ empty_object.get⟩

def twoRootMatrix (θ : Semiformula V ℒₛₑₜ 1) (B t r : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 2 :=
  (eqTerm (Bootstrapping.Semiterm.bvar 1) r.bShift.bShift ⋏
    eqTerm (Bootstrapping.Semiterm.bvar 0) B.bShift.bShift) ⋎
  ((eqTerm (Bootstrapping.Semiterm.bvar 1) t.bShift.bShift ⋏
    eqTerm (Bootstrapping.Semiterm.bvar 0) t.bShift.bShift) ⋎
  (singTerm (Bootstrapping.Semiterm.bvar 1) (Bootstrapping.Semiterm.bvar 0) ⋏
    (memTerm (Bootstrapping.Semiterm.bvar 0) B.bShift.bShift ⋏
      θ.subst ![Bootstrapping.Semiterm.bvar 0])))
def twoRootBody (θ : Semiformula V ℒₛₑₜ 1) (B t : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  ∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡘
    (eqTerm (Bootstrapping.Semiterm.bvar 0) B.bShift.bShift ⋎
      (eqTerm (Bootstrapping.Semiterm.bvar 0) t.bShift.bShift ⋎
        (memTerm (Bootstrapping.Semiterm.bvar 0) B.bShift.bShift ⋏
          θ.subst ![Bootstrapping.Semiterm.bvar 0]))))
def twoRootAt (θ : Semiformula V ℒₛₑₜ 1) (B t c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (twoRootBody θ B t).subst ![c]
def rootCondition (B t r : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  emptyAt t ⋏ (∼eqTerm B t ⋏ rawPairAt B t r)

@[simp] theorem twoRootMatrix_shift (θ : Semiformula V ℒₛₑₜ 1) (B t r : Term V ℒₛₑₜ) :
    (twoRootMatrix θ B t r).shift=twoRootMatrix θ.shift B.shift t.shift r.shift := by
  simp [twoRootMatrix,singTerm,eqTerm,memTerm,Bootstrapping.Semiformula.shift_substs,
    ←Bootstrapping.Semiterm.bShift_shift_comm,Matrix.vecHead,Matrix.vecTail]
@[simp] theorem twoRootBody_shift (θ : Semiformula V ℒₛₑₜ 1) (B t : Term V ℒₛₑₜ) :
    (twoRootBody θ B t).shift=twoRootBody θ.shift B.shift t.shift := by
  simp [twoRootBody,memTerm,eqTerm,Bootstrapping.Semiformula.shift_substs,
    ←Bootstrapping.Semiterm.bShift_shift_comm,Matrix.vecHead,Matrix.vecTail]
@[simp] theorem twoRootAt_shift (θ : Semiformula V ℒₛₑₜ 1) (B t c : Term V ℒₛₑₜ) :
    (twoRootAt θ B t c).shift=twoRootAt θ.shift B.shift t.shift c.shift := by
  simp [twoRootAt,Bootstrapping.Semiformula.shift_substs,Matrix.vecHead,Matrix.vecTail]
@[simp] theorem twoRootBody_free (θ : Semiformula V ℒₛₑₜ 1) (B t : Term V ℒₛₑₜ) :
    (twoRootBody θ B t).free=twoRootAt θ.shift B.shift t.shift (Bootstrapping.Semiterm.fvar 0) := by
  simp [Bootstrapping.Semiformula.free,twoRootAt]
@[simp] theorem rootCondition_shift (B t r : Term V ℒₛₑₜ) :
    (rootCondition B t r).shift=rootCondition B.shift t.shift r.shift := by
  simp [rootCondition,eqTerm]
@[simp] theorem twoRootMatrix_subst (θ : Semiformula V ℒₛₑₜ 1) (B t r z p : Term V ℒₛₑₜ) :
    (twoRootMatrix θ B t r).subst ![z,p]=
      ((eqTerm p r ⋏ eqTerm z B) ⋎ ((eqTerm p t ⋏ eqTerm z t) ⋎
        (singletonAt p z ⋏ (memTerm z B ⋏ θ.subst ![z])))) := by
  rcases term_is_fvar B with ⟨B,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar r with ⟨r,rfl⟩
  rcases term_is_fvar z with ⟨z,rfl⟩
  rcases term_is_fvar p with ⟨p,rfl⟩
  simp [twoRootMatrix,singTerm,singletonAt,eqTerm,memTerm,
    Bootstrapping.Semiformula.substs_substs,SemitermVec.q,Matrix.vecHead,Matrix.vecTail]

attribute [local irreducible] twoRootMatrix twoRootBody twoRootAt rootCondition

theorem root_ne_empty (B t r : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition B t r 🡒 ∼eqTerm r t := by
  have hs := rawPairAt_spec B t r B
  have hb : Source V ⊢ eqTerm B B := ⟨source_refl B⟩
  have hm := source_mem_right B r t
  have he := empty_spec t B
  unfold rootCondition
  cl_prover [hs,hb,hm,he]

theorem root_not_singleton (B t r p z : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition B t r 🡒 singletonAt p z 🡒 ∼eqTerm p r := by
  have hB := rawPairAt_spec B t r B
  have ht := rawPairAt_spec B t r t
  have hBB : Source V ⊢ eqTerm B B := ⟨source_refl B⟩
  have htt : Source V ⊢ eqTerm t t := ⟨source_refl t⟩
  have hs := source_symm p r
  have hmB := source_mem_right B r p
  have hmt := source_mem_right t r p
  have hzB := singleton_spec p z B
  have hzt := singleton_spec p z t
  have hsz := source_symm t z
  have htr := source_trans B z t
  have hpB : Source V ⊢ rawPairAt B t r 🡒 eqTerm p r 🡒 memTerm B p := by
    cl_prover [hB,hBB,hs,hmB]
  have hpt : Source V ⊢ rawPairAt B t r 🡒 eqTerm p r 🡒 memTerm t p := by
    cl_prover [ht,htt,hs,hmt]
  have hBz : Source V ⊢ rawPairAt B t r 🡒 eqTerm p r 🡒 singletonAt p z 🡒 eqTerm B z := by
    cl_prover [hpB,hzB]
  have htz : Source V ⊢ rawPairAt B t r 🡒 eqTerm p r 🡒 singletonAt p z 🡒 eqTerm t z := by
    cl_prover [hpt,hzt]
  unfold rootCondition
  cl_prover 48 [hBz,htz,hsz,htr]

theorem empty_not_singleton (t z : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∼singletonAt t z := by
  cl_prover [empty_spec t z,singleton_mem t z]

private theorem two_root_value (θ : Semiformula V ℒₛₑₜ 1) (B t r z : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition B t r 🡒 (twoRootMatrix θ B t r).subst ![z,r] 🡒 eqTerm z B := by
  rw [twoRootMatrix_subst]
  have hn := root_ne_empty B t r
  have hs := root_not_singleton B t r r z
  have hr : Source V ⊢ eqTerm r r := ⟨source_refl r⟩
  cl_prover 80 [hn,hs,hr]

private theorem two_empty_value (θ : Semiformula V ℒₛₑₜ 1) (B t r z : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition B t r 🡒 (twoRootMatrix θ B t r).subst ![z,t] 🡒 eqTerm z t := by
  rw [twoRootMatrix_subst]
  have hn := root_ne_empty B t r
  have hs := source_symm t r
  have he := empty_not_singleton t z
  have he' : Source V ⊢ rootCondition B t r 🡒 ∼singletonAt t z := by
    unfold rootCondition; cl_prover [he]
  cl_prover [hn,hs,he']

private theorem two_singleton_value (θ : Semiformula V ℒₛₑₜ 1) (B t r p v z : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition B t r 🡒 singletonAt p v 🡒
      (twoRootMatrix θ B t r).subst ![z,p] 🡒 eqTerm z v := by
  rw [twoRootMatrix_subst]
  have hr := root_not_singleton B t r p v
  have he := singleton_ne_empty t p v
  have he' : Source V ⊢ rootCondition B t r 🡒 singletonAt p v 🡒 ∼eqTerm p t := by
    unfold rootCondition; cl_prover [he]
  have hu := singleton_unique p p z v
  have hp : Source V ⊢ eqTerm p p := ⟨source_refl p⟩
  have hu' : Source V ⊢ singletonAt p v 🡒 singletonAt p z 🡒 eqTerm z v := by
    cl_prover [hu,hp]
  cl_prover 48 [hr,he',hu']

private theorem two_first (θ : Semiformula V ℒₛₑₜ 1) (B t r c : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition B t r 🡒 pairAt (twoRootMatrix θ B t r) r c 🡒 memTerm B c := by
  have hh := hit_member (twoRootMatrix θ B t r) r c B (rootCondition B t r) (by
    simpa only [rootCondition_shift,twoRootMatrix_shift] using
      two_root_value θ.shift B.shift t.shift r.shift (Bootstrapping.Semiterm.fvar 0))
  have hr : Source V ⊢ pairAt (twoRootMatrix θ B t r) r c 🡒
      (twoRootMatrix θ B t r).subst ![B,r] 🡒 ∃⁰ hitBody (twoRootMatrix θ B t r) r c :=
    by simpa only [hitBody] using pair_request (twoRootMatrix θ B t r) r c B
  have hk : Source V ⊢ (twoRootMatrix θ B t r).subst ![B,r] := by
    rw [twoRootMatrix_subst]
    have hB : Source V ⊢ eqTerm B B := ⟨source_refl B⟩
    have hR : Source V ⊢ eqTerm r r := ⟨source_refl r⟩
    cl_prover [hB,hR]
  cl_prover [hh,hr,hk]

private theorem two_second (θ : Semiformula V ℒₛₑₜ 1) (B t r c : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition B t r 🡒 pairAt (twoRootMatrix θ B t r) r c 🡒 memTerm t c := by
  have hh := hit_member (twoRootMatrix θ B t r) t c t (rootCondition B t r) (by
    simpa only [rootCondition_shift,twoRootMatrix_shift] using
      two_empty_value θ.shift B.shift t.shift r.shift (Bootstrapping.Semiterm.fvar 0))
  have hc := pair_closure (twoRootMatrix θ B t r) r c B
  have hf := two_first θ B t r c
  have hstep := closure_step (twoRootMatrix θ B t r) c B t t
  have he : Source V ⊢ rootCondition B t r 🡒 subsetTerm t B := by
    have h := empty_subset t B
    unfold rootCondition; cl_prover [h]
  have hk : Source V ⊢ (twoRootMatrix θ B t r).subst ![t,t] := by
    rw [twoRootMatrix_subst]
    have ht : Source V ⊢ eqTerm t t := ⟨source_refl t⟩
    cl_prover [ht]
  have hcl : Source V ⊢ rootCondition B t r 🡒 pairAt (twoRootMatrix θ B t r) r c 🡒
      closureTerm (twoRootMatrix θ B t r) c B := by cl_prover [hc,hf]
  have hh' : Source V ⊢ rootCondition B t r 🡒 pairAt (twoRootMatrix θ B t r) r c 🡒
      ∃⁰ hitBody (twoRootMatrix θ B t r) t c := by cl_prover 80 [hcl,he,hstep,hk]
  cl_prover [hh',hh]

private def twoProperty (θ : Semiformula V ℒₛₑₜ 1) (B t z : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  eqTerm z B ⋎ (eqTerm z t ⋎ (memTerm z B ⋏ θ.subst ![z]))
@[simp] private theorem twoProperty_shift (θ : Semiformula V ℒₛₑₜ 1) (B t z : Term V ℒₛₑₜ) :
    (twoProperty θ B t z).shift=twoProperty θ.shift B.shift t.shift z.shift := by
  simp [twoProperty,eqTerm,memTerm,Bootstrapping.Semiformula.shift_substs,Matrix.vecHead,Matrix.vecTail]
attribute [local irreducible] twoProperty

private theorem two_cover (θ : Semiformula V ℒₛₑₜ 1) (B t r c z : Term V ℒₛₑₜ) :
    Source V ⊢ pairAt (twoRootMatrix θ B t r) r c 🡒 memTerm z c 🡒 twoProperty θ B t z := by
  have he : Source V ⊢ (∃⁰ supportCore (twoRootMatrix θ B t r) z) 🡒 twoProperty θ B t z := by
    apply exists_elim
    rw [supportCore_free,twoRootMatrix_shift,twoRootMatrix_subst,twoProperty_shift]
    unfold twoProperty
    cl_prover
  have hs : Source V ⊢ pairAt (twoRootMatrix θ B t r) r c 🡒 memTerm z c 🡒
      ∃⁰ supportCore (twoRootMatrix θ B t r) z := by
    simpa only [supportCore] using pair_support (twoRootMatrix θ B t r) r c z
  cl_prover [he,hs]

private theorem two_selected (θ : Semiformula V ℒₛₑₜ 1) (B t r c z : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition B t r 🡒 pairAt (twoRootMatrix θ B t r) r c 🡒
      memTerm z B 🡒 θ.subst ![z] 🡒 memTerm z c := by
  have he : Source V ⊢ (∃⁰ singletonBody z) 🡒
      (rootCondition B t r 🡒 pairAt (twoRootMatrix θ B t r) r c 🡒
        memTerm z B 🡒 θ.subst ![z] 🡒 memTerm z c) := by
    apply exists_elim
    rw [singletonBody_free']
    let p : Term V ℒₛₑₜ := Bootstrapping.Semiterm.fvar 0
    have hh := hit_member (twoRootMatrix θ.shift B.shift t.shift r.shift) p c.shift z.shift
      (rootCondition B.shift t.shift r.shift ⋏ singletonAt p z.shift) (by
        have hv := two_singleton_value θ.shift.shift B.shift.shift t.shift.shift r.shift.shift
          p.shift z.shift.shift (Bootstrapping.Semiterm.fvar 0)
        simpa only [Bootstrapping.Semiformula.shift_and,rootCondition_shift,
          singletonAt_shift,twoRootMatrix_shift] using
          (show Source V ⊢ (rootCondition B.shift.shift t.shift.shift r.shift.shift ⋏
            singletonAt p.shift z.shift.shift) 🡒
            (twoRootMatrix θ.shift.shift B.shift.shift t.shift.shift r.shift.shift).subst
              ![Bootstrapping.Semiterm.fvar 0,p.shift] 🡒
            eqTerm (Bootstrapping.Semiterm.fvar 0) z.shift.shift from by cl_prover [hv]))
    have hf := two_first θ.shift B.shift t.shift r.shift c.shift
    have hc := pair_closure (twoRootMatrix θ.shift B.shift t.shift r.shift) r.shift c.shift B.shift
    have hs := singleton_subset p z.shift B.shift
    have hstep := closure_step (twoRootMatrix θ.shift B.shift t.shift r.shift) c.shift B.shift p z.shift
    have hk : Source V ⊢ singletonAt p z.shift 🡒 memTerm z.shift B.shift 🡒
        θ.shift.subst ![z.shift] 🡒
        (twoRootMatrix θ.shift B.shift t.shift r.shift).subst ![z.shift,p] := by
      rw [twoRootMatrix_subst]; cl_prover
    have hcl : Source V ⊢ rootCondition B.shift t.shift r.shift 🡒
        pairAt (twoRootMatrix θ.shift B.shift t.shift r.shift) r.shift c.shift 🡒
        closureTerm (twoRootMatrix θ.shift B.shift t.shift r.shift) c.shift B.shift := by
      cl_prover [hf,hc]
    have hhit : Source V ⊢ singletonAt p z.shift 🡒 memTerm z.shift B.shift 🡒
        θ.shift.subst ![z.shift] 🡒
        closureTerm (twoRootMatrix θ.shift B.shift t.shift r.shift) c.shift B.shift 🡒
        ∃⁰ hitBody (twoRootMatrix θ.shift B.shift t.shift r.shift) p c.shift := by
      cl_prover [hs,hk,hstep]
    have h : Source V ⊢ singletonAt p z.shift 🡒 rootCondition B.shift t.shift r.shift 🡒
        pairAt (twoRootMatrix θ.shift B.shift t.shift r.shift) r.shift c.shift 🡒
        memTerm z.shift B.shift 🡒 θ.shift.subst ![z.shift] 🡒 memTerm z.shift c.shift := by
      cl_prover 64 [hcl,hhit,hh]
    simpa [p,Bootstrapping.Semiformula.shift_imp,rootCondition_shift,pairAt_shift,
      twoRootMatrix_shift,memTerm,Bootstrapping.Semiformula.shift_substs,
      Matrix.vecHead,Matrix.vecTail] using h
  exact ⟨he.get ⨀ (singleton_object z).get⟩

private theorem twoRootAt_eq_all (θ : Semiformula V ℒₛₑₜ 1) (B t c : Term V ℒₛₑₜ) :
    twoRootAt θ B t c=∀⁰ (memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift 🡘
      (eqTerm (Bootstrapping.Semiterm.bvar 0) B.bShift ⋎
        (eqTerm (Bootstrapping.Semiterm.bvar 0) t.bShift ⋎
          (memTerm (Bootstrapping.Semiterm.bvar 0) B.bShift ⋏
            θ.subst ![Bootstrapping.Semiterm.bvar 0])))) := by
  rcases term_is_fvar B with ⟨B,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  simp [twoRootAt,twoRootBody,eqTerm,memTerm,SemitermVec.q,
    Bootstrapping.Semiformula.substs_substs,Matrix.vecHead,Matrix.vecTail]

private theorem twoRootAt_spec (θ : Semiformula V ℒₛₑₜ 1) (B t c z : Term V ℒₛₑₜ) :
    Source V ⊢ twoRootAt θ B t c 🡒 (memTerm z c 🡘 twoProperty θ B t z) := by
  apply deduct'!
  have h : [twoRootAt θ B t c] ⊢[Source V] twoRootAt θ B t c := by_axm₀!
  rw [twoRootAt_eq_all] at h
  simpa [twoRootAt_eq_all,twoProperty,memTerm,eqTerm,Bootstrapping.Semiformula.substs_substs,
    Matrix.vecHead,Matrix.vecTail] using TProof.specialize_with_ctx! h z

private theorem two_exact (θ : Semiformula V ℒₛₑₜ 1) (B t r c : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition B t r 🡒 pairAt (twoRootMatrix θ B t r) r c 🡒 twoRootAt θ B t c := by
  apply deduct'!
  apply FiniteContext.deduct!
  rw [twoRootAt_eq_all]
  apply TProof.generalize!
  let Γ := [pairAt (twoRootMatrix θ B t r) r c,rootCondition B t r].map Bootstrapping.Semiformula.shift
  let z : Term V ℒₛₑₜ := Bootstrapping.Semiterm.fvar 0
  have hp : Γ ⊢[Source V] pairAt (twoRootMatrix θ.shift B.shift t.shift r.shift) r.shift c.shift := by
    simp only [Γ,List.map_cons,List.map_nil,pairAt_shift,twoRootMatrix_shift]; exact by_axm₀!
  have hr : Γ ⊢[Source V] rootCondition B.shift t.shift r.shift := by
    simp only [Γ,List.map_cons,List.map_nil,rootCondition_shift]; exact by_axm!
  have h1 := FiniteContext.of'! (Γ := Γ) (two_first θ.shift B.shift t.shift r.shift c.shift)
  have h2 := FiniteContext.of'! (Γ := Γ) (two_second θ.shift B.shift t.shift r.shift c.shift)
  have h3 := FiniteContext.of'! (Γ := Γ) (two_selected θ.shift B.shift t.shift r.shift c.shift z)
  have hc := FiniteContext.of'! (Γ := Γ) (two_cover θ.shift B.shift t.shift r.shift c.shift z)
  have hB : Γ ⊢[Source V] memTerm B.shift c.shift := by cl_prover [hr,hp,h1]
  have ht : Γ ⊢[Source V] memTerm t.shift c.shift := by cl_prover [hr,hp,h2]
  have heB := FiniteContext.of'! (Γ := Γ) (source_symm z B.shift)
  have het := FiniteContext.of'! (Γ := Γ) (source_symm z t.shift)
  have hmB := FiniteContext.of'! (Γ := Γ) (source_mem_congr B.shift z c.shift)
  have hmt := FiniteContext.of'! (Γ := Γ) (source_mem_congr t.shift z c.shift)
  have hb : Γ ⊢[Source V] eqTerm z B.shift 🡒 memTerm z c.shift := by cl_prover [hB,heB,hmB]
  have ht' : Γ ⊢[Source V] eqTerm z t.shift 🡒 memTerm z c.shift := by cl_prover [ht,het,hmt]
  have hs : Γ ⊢[Source V] memTerm z B.shift 🡒 θ.shift.subst ![z] 🡒 memTerm z c.shift := by
    cl_prover [hr,hp,h3]
  have hc' : Γ ⊢[Source V] memTerm z c.shift 🡒 twoProperty θ.shift B.shift t.shift z := by
    cl_prover [hc,hp]
  have hback : Γ ⊢[Source V]
      (eqTerm z B.shift ⋎ (eqTerm z t.shift ⋎ (memTerm z B.shift ⋏ θ.shift.subst ![z]))) 🡒
        memTerm z c.shift :=
    left_A!_intro hb (left_A!_intro ht' (CK!_iff_CC!.mpr hs))
  have h : Γ ⊢[Source V] memTerm z c.shift 🡘
      (eqTerm z B.shift ⋎ (eqTerm z t.shift ⋎ (memTerm z B.shift ⋏ θ.shift.subst ![z]))) := by
    apply E!_intro
    · simpa only [twoProperty] using hc'
    · exact hback
  simpa [Γ,z,eqTerm,memTerm,Bootstrapping.Semiformula.free,
    Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail,←Bootstrapping.Semiterm.bShift_shift_comm] using h

private theorem two_of_pair (θ : Semiformula V ℒₛₑₜ 1) (B t r : Term V ℒₛₑₜ) :
    Source V ⊢ rootCondition B t r 🡒 ∃⁰ twoRootBody θ B t := by
  apply deduct'!
  have h : [rootCondition B t r] ⊢[Source V]
      (∃⁰ pairExists (twoRootMatrix θ B t r) r) 🡒 ∃⁰ twoRootBody θ B t := by
    apply TProof.exs_imp_exs!
    rw [pairExists_free,twoRootBody_free,twoRootMatrix_shift]
    have hp := FiniteContext.of'! (Γ := [rootCondition B t r].map Bootstrapping.Semiformula.shift)
      (two_exact θ.shift B.shift t.shift r.shift (Bootstrapping.Semiterm.fvar 0))
    have hr : [rootCondition B t r].map Bootstrapping.Semiformula.shift ⊢[Source V]
        rootCondition B.shift t.shift r.shift := by
      simp only [List.map_cons,List.map_nil,rootCondition_shift]; exact by_axm₀!
    cl_prover [hp,hr]
  have hx := FiniteContext.of'! (Γ := [rootCondition B t r]) (pair_exists (twoRootMatrix θ B t r) r)
  exact ⟨h.get ⨀ hx.get⟩

theorem raw_two_root (θ : Semiformula V ℒₛₑₜ 1) (B t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∼eqTerm B t 🡒 ∃⁰ twoRootBody θ B t := by
  have h : Source V ⊢ (∃⁰ rawPairBody B t) 🡒
      (emptyAt t 🡒 ∼eqTerm B t 🡒 ∃⁰ twoRootBody θ B t) := by
    apply exists_elim
    rw [rawPairBody_free]
    have hp := two_of_pair θ.shift B.shift t.shift (Bootstrapping.Semiterm.fvar 0)
    unfold rootCondition at hp
    simpa [Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_exs,
      emptyAt_shift,eqTerm,twoRootBody_shift] using
      (show Source V ⊢ rawPairAt B.shift t.shift (Bootstrapping.Semiterm.fvar 0) 🡒
        emptyAt t.shift 🡒 ∼eqTerm B.shift t.shift 🡒 ∃⁰ twoRootBody θ.shift B.shift t.shift from by
          cl_prover [hp])
  exact ⟨h.get ⨀ (raw_pair B t).get⟩

def tagMatrix (t : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  memTerm t.bShift (Bootstrapping.Semiterm.bvar 0)
def selectedMatrix (θ : Semiformula V ℒₛₑₜ 1) (U : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  memTerm (Bootstrapping.Semiterm.bvar 0) U.bShift ⋏ θ
def guardedBody (θ : Semiformula V ℒₛₑₜ 1) (U t : Term V ℒₛₑₜ) : Semiformula V ℒₛₑₜ 1 :=
  memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) ⋏
    (∀⁰ (memTerm t.bShift.bShift (Bootstrapping.Semiterm.bvar 0) 🡒
      (memTerm (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡘
        (memTerm (Bootstrapping.Semiterm.bvar 0) U.bShift.bShift ⋏
          θ.subst ![Bootstrapping.Semiterm.bvar 0]))))
def guardedAt (θ : Semiformula V ℒₛₑₜ 1) (U t c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  (guardedBody θ U t).subst ![c]
private def guardedAll (θ : Semiformula V ℒₛₑₜ 1) (U t c : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  ∀⁰ (memTerm t.bShift (Bootstrapping.Semiterm.bvar 0) 🡒
    (memTerm (Bootstrapping.Semiterm.bvar 0) c.bShift 🡘
      (memTerm (Bootstrapping.Semiterm.bvar 0) U.bShift ⋏
        θ.subst ![Bootstrapping.Semiterm.bvar 0])))
private def envelopeCondition (U t E : Term V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  emptyAt t ⋏ (∼eqTerm U t ⋏ rawAugAt (tagMatrix t) U E)

@[simp] theorem tagMatrix_shift (t : Term V ℒₛₑₜ) :
    (tagMatrix t).shift=tagMatrix t.shift := by
  simp [tagMatrix,memTerm,←Bootstrapping.Semiterm.bShift_shift_comm]
@[simp] theorem selectedMatrix_shift (θ : Semiformula V ℒₛₑₜ 1) (U : Term V ℒₛₑₜ) :
    (selectedMatrix θ U).shift=selectedMatrix θ.shift U.shift := by
  simp [selectedMatrix,memTerm,←Bootstrapping.Semiterm.bShift_shift_comm]
@[simp] theorem guardedBody_shift (θ : Semiformula V ℒₛₑₜ 1) (U t : Term V ℒₛₑₜ) :
    (guardedBody θ U t).shift=guardedBody θ.shift U.shift t.shift := by
  simp [guardedBody,memTerm,Bootstrapping.Semiformula.shift_substs,
    ←Bootstrapping.Semiterm.bShift_shift_comm,Matrix.vecHead,Matrix.vecTail]
@[simp] theorem guardedAt_shift (θ : Semiformula V ℒₛₑₜ 1) (U t c : Term V ℒₛₑₜ) :
    (guardedAt θ U t c).shift=guardedAt θ.shift U.shift t.shift c.shift := by
  simp [guardedAt,Bootstrapping.Semiformula.shift_substs,Matrix.vecHead,Matrix.vecTail]
@[simp] theorem guardedBody_free (θ : Semiformula V ℒₛₑₜ 1) (U t : Term V ℒₛₑₜ) :
    (guardedBody θ U t).free=guardedAt θ.shift U.shift t.shift (Bootstrapping.Semiterm.fvar 0) := by
  simp [Bootstrapping.Semiformula.free,guardedAt]
@[simp] theorem rawAugAt_shift' (θ : Semiformula V ℒₛₑₜ 1) (a c : Term V ℒₛₑₜ) :
    (rawAugAt θ a c).shift=rawAugAt θ.shift a.shift c.shift := by
  simp [rawAugAt,Bootstrapping.Semiformula.shift_substs,Matrix.vecHead,Matrix.vecTail]
@[simp] private theorem envelopeCondition_shift (U t E : Term V ℒₛₑₜ) :
    (envelopeCondition U t E).shift=envelopeCondition U.shift t.shift E.shift := by
  simp [envelopeCondition,eqTerm]

private theorem guardedAt_eq (θ : Semiformula V ℒₛₑₜ 1) (U t c : Term V ℒₛₑₜ) :
    guardedAt θ U t c=(memTerm t c ⋏ guardedAll θ U t c) := by
  rcases term_is_fvar U with ⟨U,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar c with ⟨c,rfl⟩
  simp [guardedAt,guardedBody,guardedAll,memTerm,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail]

theorem aug_spec (θ : Semiformula V ℒₛₑₜ 1) (U E z : Term V ℒₛₑₜ) :
    Source V ⊢ rawAugAt θ U E 🡒 (memTerm z E 🡘 (eqTerm z U ⋎ (memTerm z U ⋏ θ.subst ![z]))) := by
  rcases term_is_fvar U with ⟨U,rfl⟩
  rcases term_is_fvar E with ⟨E,rfl⟩
  apply deduct'!
  have h : [rawAugAt θ (Bootstrapping.Semiterm.fvar U) (Bootstrapping.Semiterm.fvar E)] ⊢[Source V] rawAugAt θ (Bootstrapping.Semiterm.fvar U) (Bootstrapping.Semiterm.fvar E) := by_axm₀!
  simp only [rawAugAt,rawAugBody,Bootstrapping.Semiformula.substs_all] at h
  simpa [rawAugAt,rawAugBody,memTerm,eqTerm,Bootstrapping.Semiformula.substs_substs,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using TProof.specialize_with_ctx! h z

private theorem envelope_ne (U t E : Term V ℒₛₑₜ) :
    Source V ⊢ envelopeCondition U t E 🡒 ∼eqTerm E t := by
  have hs := aug_spec (tagMatrix t) U E U
  have hr : Source V ⊢ eqTerm U U := ⟨source_refl U⟩
  have hm := source_mem_right U E t
  have he := empty_spec t U
  unfold envelopeCondition
  cl_prover [hs,hr,hm,he]

private theorem envelope_untagged (U t E : Term V ℒₛₑₜ) :
    Source V ⊢ envelopeCondition U t E 🡒 ∼memTerm t E := by
  have hs := aug_spec (tagMatrix t) U E t
  have he := source_symm t U
  have hi := source_irrefl t
  have hs' : Source V ⊢ rawAugAt (tagMatrix t) U E 🡒
      (memTerm t E 🡘 (eqTerm t U ⋎ (memTerm t U ⋏ memTerm t t))) := by
    simpa [tagMatrix,memTerm] using hs
  unfold envelopeCondition
  cl_prover 80 [hs',he,hi]

attribute [local irreducible] tagMatrix selectedMatrix guardedBody guardedAt guardedAll envelopeCondition

private theorem guarded_empty_point (θ : Semiformula V ℒₛₑₜ 1) (U t c z : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 eqTerm U t 🡒 singletonAt c t 🡒 memTerm t z 🡒
      (memTerm z c 🡘 (memTerm z U ⋏ θ.subst ![z])) := by
  have hs := singleton_spec c t z
  have hz := source_mem_right t z t
  have hi := source_irrefl t
  have hu := source_mem_right z U t
  have he := empty_spec t z
  have hnC : Source V ⊢ singletonAt c t 🡒 memTerm t z 🡒 ∼memTerm z c := by
    cl_prover [hs,hz,hi]
  have hnU : Source V ⊢ emptyAt t 🡒 eqTerm U t 🡒 ∼memTerm z U := by
    cl_prover [hu,he]
  cl_prover [hnC,hnU]

private theorem guarded_empty_at (θ : Semiformula V ℒₛₑₜ 1) (U t c : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 eqTerm U t 🡒 singletonAt c t 🡒 guardedAt θ U t c := by
  have hall : Source V ⊢ emptyAt t 🡒 eqTerm U t 🡒 singletonAt c t 🡒 guardedAll θ U t c := by
    apply deduct'!
    apply FiniteContext.deduct!
    apply FiniteContext.deduct!
    unfold guardedAll
    apply TProof.generalize!
    let Γ := [singletonAt c t,eqTerm U t,emptyAt t].map Bootstrapping.Semiformula.shift
    let z : Term V ℒₛₑₜ := Bootstrapping.Semiterm.fvar 0
    have he : Γ ⊢[Source V] emptyAt t.shift := by
      simp only [Γ,List.map_cons,List.map_nil,emptyAt_shift]; exact by_axm!
    have hu : Γ ⊢[Source V] eqTerm U.shift t.shift := by
      simp only [Γ,List.map_cons,List.map_nil,eqTerm,Bootstrapping.Semiformula.shift_rel,
        Matrix.map_cons,Matrix.map_nil]; exact by_axm!
    have hc : Γ ⊢[Source V] singletonAt c.shift t.shift := by
      simp only [Γ,List.map_cons,List.map_nil,singletonAt_shift]; exact by_axm₀!
    have hp := FiniteContext.of'! (Γ := Γ) (guarded_empty_point θ.shift U.shift t.shift c.shift z)
    have h : Γ ⊢[Source V] memTerm t.shift z 🡒
        (memTerm z c.shift 🡘 (memTerm z U.shift ⋏ θ.shift.subst ![z])) := by cl_prover 96 [hp,he,hu,hc]
    simpa [Γ,z,memTerm,Bootstrapping.Semiformula.free,
      Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
      Matrix.vecHead,Matrix.vecTail,←Bootstrapping.Semiterm.bShift_shift_comm] using h
  rw [guardedAt_eq]
  have hm := singleton_mem c t
  cl_prover [hall,hm]

private theorem guarded_empty_bound (θ : Semiformula V ℒₛₑₜ 1) (U t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 eqTerm U t 🡒 ∃⁰ guardedBody θ U t := by
  apply deduct'!
  apply FiniteContext.deduct!
  let Γ := [eqTerm U t,emptyAt t]
  have h : Γ ⊢[Source V] (∃⁰ singletonBody t) 🡒 ∃⁰ guardedBody θ U t := by
    apply TProof.exs_imp_exs!
    rw [singletonBody_free',guardedBody_free]
    have hp := FiniteContext.of'! (Γ := Γ.map Bootstrapping.Semiformula.shift)
      (guarded_empty_at θ.shift U.shift t.shift (Bootstrapping.Semiterm.fvar 0))
    have he : Γ.map Bootstrapping.Semiformula.shift ⊢[Source V] emptyAt t.shift := by
      simp only [Γ,List.map_cons,List.map_nil,emptyAt_shift]; exact by_axm!
    have hu : Γ.map Bootstrapping.Semiformula.shift ⊢[Source V] eqTerm U.shift t.shift := by
      simp only [Γ,List.map_cons,List.map_nil,eqTerm,Bootstrapping.Semiformula.shift_rel,
        Matrix.map_cons,Matrix.map_nil]; exact by_axm₀!
    cl_prover [hp,he,hu]
  have hs := FiniteContext.of'! (Γ := Γ) (singleton_object t)
  exact ⟨h.get ⨀ hs.get⟩

private theorem guarded_other_point (θ : Semiformula V ℒₛₑₜ 1) (U t E c z : Term V ℒₛₑₜ) :
    Source V ⊢ envelopeCondition U t E 🡒 twoRootAt (selectedMatrix θ U) E t c 🡒
      memTerm t z 🡒 (memTerm z c 🡘 (memTerm z U ⋏ θ.subst ![z])) := by
  have he := envelope_untagged U t E
  have hmE := source_mem_right t z E
  have hmt := source_mem_right t z t
  have hi := source_irrefl t
  have hnE : Source V ⊢ envelopeCondition U t E 🡒 memTerm t z 🡒 ∼eqTerm z E := by
    cl_prover [he,hmE]
  have hnt : Source V ⊢ memTerm t z 🡒 ∼eqTerm z t := by cl_prover [hi,hmt]
  have hs := twoRootAt_spec (selectedMatrix θ U) E t c z
  have hs' : Source V ⊢ twoRootAt (selectedMatrix θ U) E t c 🡒
      (memTerm z c 🡘 (eqTerm z E ⋎ (eqTerm z t ⋎
        (memTerm z E ⋏ (memTerm z U ⋏ θ.subst ![z]))))) := by
    simpa [twoProperty,selectedMatrix,memTerm] using hs
  have ha := aug_spec (tagMatrix t) U E z
  have ha' : Source V ⊢ rawAugAt (tagMatrix t) U E 🡒
      (memTerm z E 🡘 (eqTerm z U ⋎ (memTerm z U ⋏ memTerm t z))) := by
    simpa [tagMatrix,memTerm] using ha
  have hEz : Source V ⊢ envelopeCondition U t E 🡒 memTerm t z 🡒 memTerm z U 🡒 memTerm z E := by
    unfold envelopeCondition
    cl_prover [ha']
  have hf : Source V ⊢ envelopeCondition U t E 🡒 twoRootAt (selectedMatrix θ U) E t c 🡒
      memTerm t z 🡒 memTerm z c 🡒 (memTerm z U ⋏ θ.subst ![z]) := by
    cl_prover 96 [hnE,hnt,hs']
  have hb : Source V ⊢ envelopeCondition U t E 🡒 twoRootAt (selectedMatrix θ U) E t c 🡒
      memTerm t z 🡒 (memTerm z U ⋏ θ.subst ![z]) 🡒 memTerm z c := by
    cl_prover 96 [hEz,hs']
  cl_prover 80 [hf,hb]

private theorem guarded_other_at (θ : Semiformula V ℒₛₑₜ 1) (U t E c : Term V ℒₛₑₜ) :
    Source V ⊢ envelopeCondition U t E 🡒 twoRootAt (selectedMatrix θ U) E t c 🡒 guardedAt θ U t c := by
  have hall : Source V ⊢ envelopeCondition U t E 🡒 twoRootAt (selectedMatrix θ U) E t c 🡒
      guardedAll θ U t c := by
    apply deduct'!
    apply FiniteContext.deduct!
    unfold guardedAll
    apply TProof.generalize!
    let Γ := [twoRootAt (selectedMatrix θ U) E t c,envelopeCondition U t E].map Bootstrapping.Semiformula.shift
    let z : Term V ℒₛₑₜ := Bootstrapping.Semiterm.fvar 0
    have he : Γ ⊢[Source V] envelopeCondition U.shift t.shift E.shift := by
      simp only [Γ,List.map_cons,List.map_nil,envelopeCondition_shift]; exact by_axm!
    have hc : Γ ⊢[Source V] twoRootAt (selectedMatrix θ.shift U.shift) E.shift t.shift c.shift := by
      simp only [Γ,List.map_cons,List.map_nil,twoRootAt_shift,selectedMatrix_shift]; exact by_axm₀!
    have hp := FiniteContext.of'! (Γ := Γ) (guarded_other_point θ.shift U.shift t.shift E.shift c.shift z)
    have h : Γ ⊢[Source V] memTerm t.shift z 🡒
        (memTerm z c.shift 🡘 (memTerm z U.shift ⋏ θ.shift.subst ![z])) := by cl_prover 80 [hp,he,hc]
    simpa [Γ,z,memTerm,Bootstrapping.Semiformula.free,
      Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
      Matrix.vecHead,Matrix.vecTail,←Bootstrapping.Semiterm.bShift_shift_comm] using h
  have hs := twoRootAt_spec (selectedMatrix θ U) E t c t
  have ht : Source V ⊢ eqTerm t t := ⟨source_refl t⟩
  have hm : Source V ⊢ twoRootAt (selectedMatrix θ U) E t c 🡒 memTerm t c := by
    unfold twoProperty at hs
    cl_prover [hs,ht]
  rw [guardedAt_eq]
  cl_prover [hall,hm]

private theorem guarded_of_envelope (θ : Semiformula V ℒₛₑₜ 1) (U t E : Term V ℒₛₑₜ) :
    Source V ⊢ envelopeCondition U t E 🡒 ∃⁰ guardedBody θ U t := by
  apply deduct'!
  have h : [envelopeCondition U t E] ⊢[Source V]
      (∃⁰ twoRootBody (selectedMatrix θ U) E t) 🡒 ∃⁰ guardedBody θ U t := by
    apply TProof.exs_imp_exs!
    rw [twoRootBody_free,guardedBody_free,selectedMatrix_shift]
    have hp := FiniteContext.of'! (Γ := [envelopeCondition U t E].map Bootstrapping.Semiformula.shift)
      (guarded_other_at θ.shift U.shift t.shift E.shift (Bootstrapping.Semiterm.fvar 0))
    have he : [envelopeCondition U t E].map Bootstrapping.Semiformula.shift ⊢[Source V]
        envelopeCondition U.shift t.shift E.shift := by
      simp only [List.map_cons,List.map_nil,envelopeCondition_shift]; exact by_axm₀!
    cl_prover [hp,he]
  have hx := raw_two_root (selectedMatrix θ U) E t
  have hn := envelope_ne U t E
  have hx' : Source V ⊢ envelopeCondition U t E 🡒 ∃⁰ twoRootBody (selectedMatrix θ U) E t := by
    unfold envelopeCondition at hn ⊢
    cl_prover [hx,hn]
  have hxctx := FiniteContext.of'! (Γ := [envelopeCondition U t E]) hx'
  have he : [envelopeCondition U t E] ⊢[Source V] envelopeCondition U t E := by_axm₀!
  have hp : [envelopeCondition U t E] ⊢[Source V] ∃⁰ twoRootBody (selectedMatrix θ U) E t := by
    cl_prover [hxctx,he]
  exact ⟨h.get ⨀ hp.get⟩

private theorem guarded_other_bound (θ : Semiformula V ℒₛₑₜ 1) (U t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∼eqTerm U t 🡒 ∃⁰ guardedBody θ U t := by
  have h : Source V ⊢ (∃⁰ rawAugBody (tagMatrix t) U) 🡒
      (emptyAt t 🡒 ∼eqTerm U t 🡒 ∃⁰ guardedBody θ U t) := by
    apply exists_elim
    rw [rawAugBody_free,tagMatrix_shift]
    have hp := guarded_of_envelope θ.shift U.shift t.shift (Bootstrapping.Semiterm.fvar 0)
    unfold envelopeCondition at hp
    simpa [Bootstrapping.Semiformula.shift_imp,Bootstrapping.Semiformula.shift_exs,
      emptyAt_shift,eqTerm,guardedBody_shift] using
      (show Source V ⊢ rawAugAt (tagMatrix t.shift) U.shift (Bootstrapping.Semiterm.fvar 0) 🡒
        emptyAt t.shift 🡒 ∼eqTerm U.shift t.shift 🡒 ∃⁰ guardedBody θ.shift U.shift t.shift from by
          cl_prover [hp])
  exact ⟨h.get ⨀ (raw_augmented (tagMatrix t) U).get⟩

/-- No disequality restriction on U: the source-equality U=t branch is retained. -/
theorem guarded_comprehension (θ : Semiformula V ℒₛₑₜ 1) (U t : Term V ℒₛₑₜ) :
    Source V ⊢ emptyAt t 🡒 ∃⁰ guardedBody θ U t := by
  cl_prover [guarded_empty_bound θ U t,guarded_other_bound θ U t]

def rawPairEmptyProof (t x y : Term V ℒₛₑₜ) :
    Source V ⊢! emptyAt t 🡒 ∃⁰ rawPairBody x y := (raw_pair_of_empty t x y).get
def rawPairProof (x y : Term V ℒₛₑₜ) :
    Source V ⊢! ∃⁰ rawPairBody x y := (raw_pair x y).get
def twoRootProof (θ : Semiformula V ℒₛₑₜ 1) (B t : Term V ℒₛₑₜ) :
    Source V ⊢! emptyAt t 🡒 ∼eqTerm B t 🡒 ∃⁰ twoRootBody θ B t := (raw_two_root θ B t).get
def guardedProof (θ : Semiformula V ℒₛₑₜ 1) (U t : Term V ℒₛₑₜ) :
    Source V ⊢! emptyAt t 🡒 ∃⁰ guardedBody θ U t := (guarded_comprehension θ U t).get

theorem rawPairEmptyProof_isProof (t x y : Term V ℒₛₑₜ) :
    Proof seedTheory (rawPairEmptyProof t x y).val (emptyAt t 🡒 ∃⁰ rawPairBody x y).val := by
  simpa only [Source,Theory.internalize,Proof,Sequent.val_insert,Sequent.val_empty,singleton_eq_insert]
    using (rawPairEmptyProof t x y).derivationOf
theorem rawPairProof_isProof (x y : Term V ℒₛₑₜ) :
    Proof seedTheory (rawPairProof x y).val (∃⁰ rawPairBody x y).val := by
  simpa only [Source,Theory.internalize,Proof,Sequent.val_insert,Sequent.val_empty,singleton_eq_insert]
    using (rawPairProof x y).derivationOf
theorem twoRootProof_isProof (θ : Semiformula V ℒₛₑₜ 1) (B t : Term V ℒₛₑₜ) :
    Proof seedTheory (twoRootProof θ B t).val (emptyAt t 🡒 ∼eqTerm B t 🡒 ∃⁰ twoRootBody θ B t).val := by
  simpa only [Source,Theory.internalize,Proof,Sequent.val_insert,Sequent.val_empty,singleton_eq_insert]
    using (twoRootProof θ B t).derivationOf
theorem guardedProof_isProof (θ : Semiformula V ℒₛₑₜ 1) (U t : Term V ℒₛₑₜ) :
    Proof seedTheory (guardedProof θ U t).val (emptyAt t 🡒 ∃⁰ guardedBody θ U t).val := by
  simpa only [Source,Theory.internalize,Proof,Sequent.val_insert,Sequent.val_empty,singleton_eq_insert]
    using (guardedProof θ U t).derivationOf


/-! Fixed total raw syntax graphs. No whole proof-search graph is asserted. -/
/-- Ambient arguments are raw term codes, never bare free-variable labels. -/
def rawPairMatrixCode (t r x y : V) : V :=
  (at2Code b1Code r eqCode ^⋏ at2Code b0Code x eqCode) ^⋎
    (at2Code b1Code t eqCode ^⋏ at2Code b0Code y eqCode)
def rawPairBodyCode (x y : V) : V :=
  ^∀ (Bootstrapping.iff ℒₛₑₜ (memCode : V)
    (at2Code b0Code x eqCode ^⋎ at2Code b0Code y eqCode))
def twoRootMatrixCode (k B t r : V) : V :=
  (at2Code b1Code r eqCode ^⋏ at2Code b0Code B eqCode) ^⋎
    ((at2Code b1Code t eqCode ^⋏ at2Code b0Code t eqCode) ^⋎
      ((singCode : V) ^⋏ (at2Code b0Code B memCode ^⋏ at1Code b0Code k)))
def twoRootBodyCode (k B t : V) : V :=
  ^∀ (Bootstrapping.iff ℒₛₑₜ (memCode : V)
    (at2Code b0Code B eqCode ^⋎
      (at2Code b0Code t eqCode ^⋎ (at2Code b0Code B memCode ^⋏ at1Code b0Code k))))
def guardedBodyCode (k U t : V) : V :=
  at2Code t b0Code memCode ^⋏
    ^∀ (Bootstrapping.imp ℒₛₑₜ (at2Code t b0Code memCode)
      (Bootstrapping.iff ℒₛₑₜ (memCode : V) (at2Code b0Code U memCode ^⋏ at1Code b0Code k)))

def rawPairMatrixGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out t r x y. ∃ er ex et ey left right,
    !at2Graph er ↑b1Code r ↑eqCode ∧ !at2Graph ex ↑b0Code x ↑eqCode ∧
    !at2Graph et ↑b1Code t ↑eqCode ∧ !at2Graph ey ↑b0Code y ↑eqCode ∧
    !qqAndDef left er ex ∧ !qqAndDef right et ey ∧ !qqOrDef out left right”
def rawPairBodyGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out x y. ∃ ex ey right body,
    !at2Graph ex ↑b0Code x ↑eqCode ∧ !at2Graph ey ↑b0Code y ↑eqCode ∧
    !qqOrDef right ex ey ∧ !(Bootstrapping.iffGraph ℒₛₑₜ) body ↑memCode right ∧ !qqAllDef out body”
def twoRootMatrixGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out k B t r. ∃ er eB et et' mB th root empty tail chosen right,
    !at2Graph er ↑b1Code r ↑eqCode ∧ !at2Graph eB ↑b0Code B ↑eqCode ∧
    !at2Graph et ↑b1Code t ↑eqCode ∧ !at2Graph et' ↑b0Code t ↑eqCode ∧
    !at2Graph mB ↑b0Code B ↑memCode ∧ !at1Graph th ↑b0Code k ∧
    !qqAndDef root er eB ∧ !qqAndDef empty et et' ∧ !qqAndDef tail mB th ∧
    !qqAndDef chosen ↑singCode tail ∧ !qqOrDef right empty chosen ∧ !qqOrDef out root right”
def twoRootBodyGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out k B t. ∃ eB et mB th tail right' right body,
    !at2Graph eB ↑b0Code B ↑eqCode ∧ !at2Graph et ↑b0Code t ↑eqCode ∧
    !at2Graph mB ↑b0Code B ↑memCode ∧ !at1Graph th ↑b0Code k ∧
    !qqAndDef tail mB th ∧ !qqOrDef right' et tail ∧ !qqOrDef right eB right' ∧
    !(Bootstrapping.iffGraph ℒₛₑₜ) body ↑memCode right ∧ !qqAllDef out body”
def guardedBodyGraph : 𝚺₁.Semisentence 4 := .mkSigma
  “out k U t. ∃ tag mU th chosen iffbody impbody allbody,
    !at2Graph tag t ↑b0Code ↑memCode ∧ !at2Graph mU ↑b0Code U ↑memCode ∧
    !at1Graph th ↑b0Code k ∧ !qqAndDef chosen mU th ∧
    !(Bootstrapping.iffGraph ℒₛₑₜ) iffbody ↑memCode chosen ∧
    !(Bootstrapping.impGraph ℒₛₑₜ) impbody tag iffbody ∧
    !qqAllDef allbody impbody ∧ !qqAndDef out tag allbody”

instance rawPairMatrix_defined : 𝚺₁-Function₄[V] rawPairMatrixCode via rawPairMatrixGraph :=
  .mk fun v => by simp [rawPairMatrixGraph,rawPairMatrixCode,numeral_eq_natCast]
instance rawPairBody_defined : 𝚺₁-Function₂[V] rawPairBodyCode via rawPairBodyGraph :=
  .mk fun v => by simp [rawPairBodyGraph,rawPairBodyCode,numeral_eq_natCast]
instance twoRootMatrix_defined : 𝚺₁-Function₄[V] twoRootMatrixCode via twoRootMatrixGraph :=
  .mk fun v => by simp [twoRootMatrixGraph,twoRootMatrixCode,numeral_eq_natCast]
instance twoRootBody_defined : 𝚺₁-Function₃[V] twoRootBodyCode via twoRootBodyGraph :=
  .mk fun v => by simp [twoRootBodyGraph,twoRootBodyCode,numeral_eq_natCast]
instance guardedBody_defined : 𝚺₁-Function₃[V] guardedBodyCode via guardedBodyGraph :=
  .mk fun v => by simp [guardedBodyGraph,guardedBodyCode,numeral_eq_natCast]

theorem rawPairMatrixCode_eq (t r x y : Term V ℒₛₑₜ) :
    rawPairMatrixCode t.val r.val x.val y.val=(rawPairMatrix t r x y).val := by
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar r with ⟨r,rfl⟩
  rcases term_is_fvar x with ⟨x,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  have hr := at2_eq (Bootstrapping.Semiterm.bvar (1 : Fin 2)) (Bootstrapping.Semiterm.fvar r)
  have ht := at2_eq (Bootstrapping.Semiterm.bvar (1 : Fin 2)) (Bootstrapping.Semiterm.fvar t)
  have hx := at2_eq (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar x)
  have hy := at2_eq (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar y)
  simp [Bootstrapping.Semiterm.bvar,Bootstrapping.Semiterm.fvar,eqTerm] at hr ht hx hy
  simp only [rawPairMatrixCode,b0_cast,b1_cast,Bootstrapping.Semiterm.fvar,hr,ht,hx,hy]
  simp [rawPairMatrix,eqTerm]

theorem rawPairBodyCode_eq (x y : Term V ℒₛₑₜ) :
    rawPairBodyCode x.val y.val=(rawPairBody x y).val := by
  rcases term_is_fvar x with ⟨x,rfl⟩
  rcases term_is_fvar y with ⟨y,rfl⟩
  have hx := at2_eq (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar x)
  have hy := at2_eq (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar y)
  simp [Bootstrapping.Semiterm.bvar,Bootstrapping.Semiterm.fvar,eqTerm] at hx hy
  simp only [rawPairBodyCode,b0_cast,Bootstrapping.Semiterm.fvar,hx,hy]
  simp [rawPairBody,mem_cast,seedMem,eqTerm,memTerm,
    FirstOrder.Semiformula.quote_def,Matrix.vecHead,Matrix.vecTail,Bootstrapping.iff]

theorem twoRootMatrixCode_eq (θ : Semiformula V ℒₛₑₜ 1) (B t r : Term V ℒₛₑₜ) :
    twoRootMatrixCode θ.val B.val t.val r.val=(twoRootMatrix θ B t r).val := by
  rcases term_is_fvar B with ⟨B,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  rcases term_is_fvar r with ⟨r,rfl⟩
  have heB := at2_eq (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar B)
  have hmB := at2_mem (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar B)
  have het0 := at2_eq (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar t)
  have het1 := at2_eq (Bootstrapping.Semiterm.bvar (1 : Fin 2)) (Bootstrapping.Semiterm.fvar t)
  have her := at2_eq (Bootstrapping.Semiterm.bvar (1 : Fin 2)) (Bootstrapping.Semiterm.fvar r)
  simp [Bootstrapping.Semiterm.bvar,Bootstrapping.Semiterm.fvar,eqTerm,memTerm] at heB hmB het0 het1 her
  simp only [twoRootMatrixCode,b0_cast,b1_cast,Bootstrapping.Semiterm.fvar,heB,hmB,het0,het1,her]
  simp [twoRootMatrix,at1Code,sing_cast,singMeta,seedMem,singTerm,eqTerm,memTerm,
    FirstOrder.Semiformula.quote_def,Matrix.vecHead,Matrix.vecTail]

theorem twoRootBodyCode_eq (θ : Semiformula V ℒₛₑₜ 1) (B t : Term V ℒₛₑₜ) :
    twoRootBodyCode θ.val B.val t.val=(twoRootBody θ B t).val := by
  rcases term_is_fvar B with ⟨B,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  have heB := at2_eq (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar B)
  have hmB := at2_mem (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar B)
  have het := at2_eq (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar t)
  simp [Bootstrapping.Semiterm.bvar,Bootstrapping.Semiterm.fvar,eqTerm,memTerm] at heB hmB het
  simp only [twoRootBodyCode,b0_cast,Bootstrapping.Semiterm.fvar,heB,hmB,het]
  simp [twoRootBody,at1Code,mem_cast,seedMem,eqTerm,memTerm,
    FirstOrder.Semiformula.quote_def,Matrix.vecHead,Matrix.vecTail,Bootstrapping.iff]

theorem guardedBodyCode_eq (θ : Semiformula V ℒₛₑₜ 1) (U t : Term V ℒₛₑₜ) :
    guardedBodyCode θ.val U.val t.val=(guardedBody θ U t).val := by
  rcases term_is_fvar U with ⟨U,rfl⟩
  rcases term_is_fvar t with ⟨t,rfl⟩
  have hmU := at2_mem (Bootstrapping.Semiterm.bvar (0 : Fin 2)) (Bootstrapping.Semiterm.fvar U)
  have hmt := at2_mem (Bootstrapping.Semiterm.fvar t) (Bootstrapping.Semiterm.bvar (0 : Fin 2))
  simp [Bootstrapping.Semiterm.bvar,Bootstrapping.Semiterm.fvar,memTerm] at hmU hmt
  simp only [guardedBodyCode,b0_cast,Bootstrapping.Semiterm.fvar,hmU,hmt]
  simp [guardedBody,at1Code,mem_cast,seedMem,memTerm,
    FirstOrder.Semiformula.quote_def,Matrix.vecHead,Matrix.vecTail,Bootstrapping.iff,Bootstrapping.imp]

end LeanProofs.ZFCinPA.ValidatorSeedGuardedComprehension222

