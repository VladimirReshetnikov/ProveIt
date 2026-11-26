import IPRADerivations.Analysis.Polynomials.RationalPolynomialMonicCompanionGaussianEmbedding
import IPRADerivations.Analysis.Polynomials.GaussianPolynomialConstantInjection

/-!
# Original rational constant-Y coefficient injection

The actual rational row buffer adds the normalized and X-padded original
coefficient polynomial only at the last descending Y row. Stored shape and
bounded coefficient transport to the existing Gaussian injection are derived
from actual rational operations; no output law or outer-code identity is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPolynomialConstantInjectionGaussianEmbedding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open RationalGaussianEmbedding (embed)
open RationalPolynomialGaussianEmbedding (embed_congr)
open RationalPolynomialBuffersGaussianEmbedding (zeros zeros_length leftPad pad_length added added_length added_lookup embeddedEntries)
open RationalPolynomialMonicCompanionGaussianEmbedding
  (normalizedRow normalized_length rowsEmbedded row_embedded_at embedded_at embedded_congr normalized_entries pad_transport)
open GaussianPolynomialMonicCompanion (rowShape row_shape_at)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def constantRow (C m a d r : PTm n) : PTm n := sel (eqb (succ r) m)
  (leftPad (normalizedRow C) d) (zeros (succ (a+d)))
def injectedRow (G C m a d r : PTm n) : PTm n := added (entry G r) (constantRow C m a d r) (succ (a+d))
def data (G C m a d : PTm n) : PTm n := pairT G (pairT C (pairT m (pairT a d)))
def fields (p : PTm n) : Fin 5 → PTm n :=
  ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),fstT (sndT (sndT (sndT p))),sndT (sndT (sndT (sndT p)))]
def rowBody : PTm 2 := injectedRow (fields (var 1) 0) (fields (var 1) 1) (fields (var 1) 2) (fields (var 1) 3) (fields (var 1) 4) (var 0)
def inject (G C m a d : PTm n) : PTm n := sequence rowBody m (data G C m a d)

@[simp] theorem subst_constantRow {k : ℕ} (σ : Fin n → PTm k) (C m a d r : PTm n) :
    Syn.subst σ (constantRow C m a d r) = constantRow (Syn.subst σ C) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ r) := by simp [constantRow,sel]
@[simp] theorem subst_injectedRow {k : ℕ} (σ : Fin n → PTm k) (G C m a d r : PTm n) :
    Syn.subst σ (injectedRow G C m a d r) = injectedRow (Syn.subst σ G) (Syn.subst σ C) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) (Syn.subst σ r) := by simp [injectedRow]
@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (G C m a d : PTm n) :
    Syn.subst σ (data G C m a d) = data (Syn.subst σ G) (Syn.subst σ C) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [data]
@[simp] theorem subst_fields {k : ℕ} (σ : Fin n → PTm k) (p : PTm n) (i : Fin 5) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
@[simp] theorem subst_inject {k : ℕ} (σ : Fin n → PTm k) (G C m a d : PTm n) :
    Syn.subst σ (inject G C m a d) = inject (Syn.subst σ G) (Syn.subst σ C) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [inject]

theorem constant_last (C m a d r : PTm n) (h : Γ ⊢[PRAAx] succ r ≐ m) : Γ ⊢[PRAAx]
    constantRow C m a d r ≐ leftPad (normalizedRow C) d := sel_one (eqb_of_eq h)
theorem constant_other (C m a d r : PTm n) (h : Γ ⊢[PRAAx] neg (succ r ≐ m)) : Γ ⊢[PRAAx]
    constantRow C m a d r ≐ zeros (succ (a+d)) := sel_zero (eqb_of_ne h)
theorem constant_length (C m a d r : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ a) : Γ ⊢[PRAAx]
    length (constantRow C m a d r) ≐ succ (a+d) := by
  refine .orE (eq_or_ne (succ r) m) ?_ ?_
  · exact (congrFst (constant_last _ _ _ _ _ Prf.hyp0)).eqTrans
      ((pad_length _ _).eqTrans ((congrAdd (.eqRefl _) ((normalized_length C).eqTrans hC.wk)).eqTrans (by ipra_ring)))
  · exact (congrFst (constant_other _ _ _ _ _ Prf.hyp0)).eqTrans (zeros_length _)
theorem row_length (G C m a d r : PTm n) : Γ ⊢[PRAAx] length (injectedRow G C m a d r) ≐ succ (a+d) := added_length _ _ _

theorem fields_at (G C m a d : PTm n) (i : Fin 5) : Γ ⊢[PRAAx] fields (data G C m a d) i ≐ ![G,C,m,a,d] i := by
  have e0 := snd_pair (Γ := Γ) G (pairT C (pairT m (pairT a d)))
  have e1 := (congrSnd e0).eqTrans (snd_pair C (pairT m (pairT a d)))
  have e2 := (congrSnd e1).eqTrans (snd_pair m (pairT a d))
  fin_cases i
  · exact fst_pair _ _
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact (congrSnd e2).eqTrans (snd_pair _ _)
theorem tuple_six_last {α : Type} (a b c d e f : α) : ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

theorem row_congr {G G' C C' m m' a a' d d' r r' : PTm n} (hG : Γ ⊢[PRAAx] G ≐ G') (hC : Γ ⊢[PRAAx] C ≐ C')
    (hm : Γ ⊢[PRAAx] m ≐ m') (ha : Γ ⊢[PRAAx] a ≐ a') (hd : Γ ⊢[PRAAx] d ≐ d') (hr : Γ ⊢[PRAAx] r ≐ r') : Γ ⊢[PRAAx]
    injectedRow G C m a d r ≐ injectedRow G' C' m' a' d' r' := by
  simpa only [subst_injectedRow,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,tuple_six_last,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (injectedRow (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
      (σ := ![G,C,m,a,d,r]) (σ' := ![G',C',m',a',d',r'])
      (fun i => by fin_cases i <;> simp only [Matrix.cons_val_succ',Matrix.cons_val_zero']; exact hG; exact hC; exact hm; exact ha; exact hd; exact hr)
theorem row_body_at (G C m a d r : PTm n) : Γ ⊢[PRAAx] inst2 rowBody r (data G C m a d) ≐ injectedRow G C m a d r := by
  simp only [rowBody,inst2,subst_injectedRow,subst_fields,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact row_congr (fields_at _ _ _ _ _ 0) (fields_at _ _ _ _ _ 1) (fields_at _ _ _ _ _ 2)
    (fields_at _ _ _ _ _ 3) (fields_at _ _ _ _ _ 4) (.eqRefl _)
theorem inject_length (G C m a d : PTm n) : Γ ⊢[PRAAx] length (inject G C m a d) ≐ m := sequence_length _ _ _
theorem inject_lookup (G C m a d r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (inject G C m a d) r ≐ injectedRow G C m a d r := (sequence_decode rowBody hr).eqTrans (row_body_at _ _ _ _ _ _)
theorem coefficient_lookup (G C m a d r s : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s (a+d)) : Γ ⊢[PRAAx]
    entry (entry (inject G C m a d) r) s ≐ RationalArithmetic.add (entry (entry G r) s) (entry (constantRow C m a d r) s) :=
  (entry_congr (inject_lookup _ _ _ _ _ _ hr) (.eqRefl _)).eqTrans
    (added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hs))

theorem inject_shape (G C m a d : PTm n) : Γ ⊢[PRAAx] rowShape (inject G C m a d) m (a+d) := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_inject,PTm.subst_add,length] using
    (congrFst (inject_lookup (Syn.shift G) (Syn.shift C) (Syn.shift m) (Syn.shift a) (Syn.shift d) (var 0) Prf.hyp0)).eqTrans
      (row_length _ _ _ _ _ _)

theorem constant_entry_transport (C C' m a d r s : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ a) (hC' : Γ ⊢[PRAAx] length C' ≐ succ a)
    (he : Γ ⊢[PRAAx] embeddedEntries C C' (succ a)) (hs : Γ ⊢[PRAAx] le s (a+d)) : Γ ⊢[PRAAx]
    embed (entry (constantRow C m a d r) s) ≐ entry (GaussianPolynomialConstantInjection.constantRow C' m a d r) s := by
  refine .orE (eq_or_ne (succ r) m) ?_ ?_
  · let Δ := (succ r ≐ m) :: Γ
    have hN : Δ ⊢[PRAAx] embeddedEntries (normalizedRow C) (GaussianPolynomialMonicCompanion.normalizedRow C') (succ a) :=
      normalized_entries C C' (succ a) hC.wk hC'.wk he.wk
    have e := pad_transport (normalizedRow C) (GaussianPolynomialMonicCompanion.normalizedRow C') (succ a) d s
      ((normalized_length C).eqTrans hC).wk
      ((GaussianPolynomialMonicCompanion.normalized_length C').eqTrans hC').wk hN
      (lt_congr (.eqRefl _) (by ipra_ring) ((succ_monus_succ _ _).eqTrans hs.wk))
    exact (embed_congr (entry_congr (constant_last _ _ _ _ _ Prf.hyp0) (.eqRefl _))).eqTrans
      (e.eqTrans (entry_congr (GaussianPolynomialConstantInjection.constant_last _ _ _ _ _ Prf.hyp0) (.eqRefl _)).eqSymm)
  · exact (embed_congr (entry_congr (constant_other _ _ _ _ _ Prf.hyp0) (.eqRefl _))).eqTrans
      ((RationalPolynomialBuffersGaussianEmbedding.zeros_embedding _ _ ((succ_monus_succ _ _).eqTrans hs.wk)).eqTrans
        (entry_congr (GaussianPolynomialConstantInjection.constant_other _ _ _ _ _ Prf.hyp0) (.eqRefl _)).eqSymm)

theorem injected_entry_transport (G G' C C' m a d r s : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ a) (hC' : Γ ⊢[PRAAx] length C' ≐ succ a)
    (hG : Γ ⊢[PRAAx] rowsEmbedded G G' m (a+d)) (he : Γ ⊢[PRAAx] embeddedEntries C C' (succ a))
    (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s (a+d)) : Γ ⊢[PRAAx]
    embed (entry (entry (inject G C m a d) r) s) ≐
      entry (entry (GaussianPolynomialConstantInjection.inject G' C' m a d) r) s :=
  (embed_congr (coefficient_lookup _ _ _ _ _ _ _ hr hs)).eqTrans
    ((RationalGaussianEmbedding.embed_add _ _).eqTrans
      ((GaussianRationalSyntheticDivision.qadd_congr
        (embedded_at _ _ _ _ (row_embedded_at _ _ _ _ _ hG hr) ((succ_monus_succ _ _).eqTrans hs))
        (constant_entry_transport _ _ _ _ _ _ _ hC hC' he hs)).eqTrans
          (GaussianPolynomialConstantInjection.coefficient_lookup _ _ _ _ _ _ _ hr hs).eqSymm))

theorem injected_row_entries (G G' C C' m a d r : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ a) (hC' : Γ ⊢[PRAAx] length C' ≐ succ a)
    (hG : Γ ⊢[PRAAx] rowsEmbedded G G' m (a+d)) (he : Γ ⊢[PRAAx] embeddedEntries C C' (succ a))
    (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    embeddedEntries (entry (inject G C m a d) r) (entry (GaussianPolynomialConstantInjection.inject G' C' m a d) r) (succ (a+d)) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hC.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C') ≐ succ (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hC'.shift
  have gs : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift G) (Syn.shift G') (Syn.shift m) (Syn.shift a+Syn.shift d) := by simpa [Fm.shift,Syn.shift] using hG.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] embeddedEntries (Syn.shift C) (Syn.shift C') (succ (Syn.shift a)) := by simpa [Fm.shift,Syn.shift] using he.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa [Fm.shift,Syn.shift] using hr.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift a+Syn.shift d)) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] le (var 0) (Syn.shift a+Syn.shift d) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (succ (Syn.shift a+Syn.shift d)))
  simpa only [Δ,Syn.shift,subst_inject,GaussianPolynomialConstantInjection.subst_inject,subst_entry,ConciseIPRA.PTm.subst_succ,PTm.subst_add] using
    injected_entry_transport (Syn.shift G) (Syn.shift G') (Syn.shift C) (Syn.shift C') (Syn.shift m)
      (Syn.shift a) (Syn.shift d) (Syn.shift r) (var 0) cs.wk ds.wk gs.wk es.wk rs.wk
      hs

theorem inject_rows_embedded (G G' C C' m a d : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ a) (hC' : Γ ⊢[PRAAx] length C' ≐ succ a)
    (hG : Γ ⊢[PRAAx] rowsEmbedded G G' m (a+d)) (he : Γ ⊢[PRAAx] embeddedEntries C C' (succ a)) : Γ ⊢[PRAAx]
    rowsEmbedded (inject G C m a d) (GaussianPolynomialConstantInjection.inject G' C' m a d) m (a+d) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hC.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C') ≐ succ (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using hC'.shift
  have gs : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift G) (Syn.shift G') (Syn.shift m) (Syn.shift a+Syn.shift d) := by simpa [Fm.shift,Syn.shift] using hG.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] embeddedEntries (Syn.shift C) (Syn.shift C') (succ (Syn.shift a)) := by simpa [Fm.shift,Syn.shift] using he.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_inject,GaussianPolynomialConstantInjection.subst_inject,subst_entry,ConciseIPRA.PTm.subst_succ,PTm.subst_add] using
    injected_row_entries (Syn.shift G) (Syn.shift G') (Syn.shift C) (Syn.shift C') (Syn.shift m)
      (Syn.shift a) (Syn.shift d) (var 0) cs.wk ds.wk gs.wk es.wk Prf.hyp0

/- The same local coefficient relation transports both genuine Horner folds. -/
theorem values_transport (P P' R b x : PTm n)
    (hP : Γ ⊢[PRAAx] rowShape P R b) (hP' : Γ ⊢[PRAAx] rowShape P' R b)
    (he : Γ ⊢[PRAAx] rowsEmbedded P P' R b) : Γ ⊢[PRAAx]
    embeddedEntries (RationalBivariateGaussianEmbedding.values P R x)
      (GaussianPolynomialMonicCompanion.values P' R (embed x)) R := by
  have ps : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift P) (Syn.shift R) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hP.shift
  have qs : Γ.map Fm.shift ⊢[PRAAx] rowShape (Syn.shift P') (Syn.shift R) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hP'.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] rowsEmbedded (Syn.shift P) (Syn.shift P') (Syn.shift R) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using he.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift R) :: Γ.map Fm.shift
  have e := (embed_congr (RationalBivariateGaussianEmbedding.values_lookup (Γ := Δ) (Syn.shift P) (Syn.shift R) (Syn.shift x) (var 0) Prf.hyp0)).eqTrans
    ((RationalPolynomialBuffersGaussianEmbedding.evaluation_transport _ _ _ _
      (row_shape_at _ _ _ _ ps.wk Prf.hyp0) (row_shape_at _ _ _ _ qs.wk Prf.hyp0)
      (row_embedded_at _ _ _ _ _ es.wk Prf.hyp0)).eqTrans
        (GaussianPolynomialMonicCompanion.values_lookup _ _ _ _ Prf.hyp0).eqSymm)
  simpa only [Δ,Syn.shift,RationalBivariateGaussianEmbedding.subst_values,GaussianPolynomialMonicCompanion.subst_values,RationalGaussianEmbedding.subst_embed] using e

theorem bivariate_transport (P P' R b x y : PTm n)
    (hP : Γ ⊢[PRAAx] rowShape P R b) (hP' : Γ ⊢[PRAAx] rowShape P' R b)
    (he : Γ ⊢[PRAAx] rowsEmbedded P P' R b) : Γ ⊢[PRAAx]
    embed (RationalBivariateGaussianEmbedding.bivariate P R x y) ≐
      GaussianRationalHorner.evaluate (GaussianPolynomialMonicCompanion.values P' R (embed x)) (embed y) :=
  RationalPolynomialBuffersGaussianEmbedding.evaluation_transport _ _ _ _
    (RationalBivariateGaussianEmbedding.values_length _ _ _) (GaussianPolynomialMonicCompanion.values_length _ _ _)
    (values_transport _ _ _ _ _ hP hP' he)


def transportInput (G G' C C' m a d : PTm n) : Fm PTm n :=
  length C ≐ succ a ⋏ (length C' ≐ succ a ⋏ (rowsEmbedded G G' m (a+d) ⋏ embeddedEntries C C' (succ a)))
@[simp] theorem subst_transportInput {l : ℕ} (σ : Fin n → PTm l) (G G' C C' m a d : PTm n) :
    (transportInput G G' C C' m a d).subst σ = transportInput (Syn.subst σ G) (Syn.subst σ G')
      (Syn.subst σ C) (Syn.subst σ C') (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by simp [transportInput]
theorem injection_transport (G G' C C' m a d : PTm n) (h : Γ ⊢[PRAAx] transportInput G G' C C' m a d) : Γ ⊢[PRAAx]
    rowsEmbedded (inject G C m a d) (GaussianPolynomialConstantInjection.inject G' C' m a d) m (a+d) :=
  inject_rows_embedded _ _ _ _ _ _ _ (.andE₁ h) (.andE₁ (.andE₂ h)) (.andE₁ (.andE₂ (.andE₂ h))) (.andE₂ (.andE₂ (.andE₂ h)))

def injectF : PR 5 := PTm.toPR (inject (var 0) (var 1) (var 2) (var 3) (var 4))
def run (G C m a d : PTm n) : PTm n := app injectF ![G,C,m,a,d]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (G C m a d : PTm n) :
    Syn.subst σ (run G C m a d) = run (Syn.subst σ G) (Syn.subst σ C) (Syn.subst σ m) (Syn.subst σ a) (Syn.subst σ d) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (G C m a d : PTm n) : Γ ⊢[PRAAx] run G C m a d ≐ inject G C m a d := by
  simpa [run,injectF] using toPR_eq (Γ := Γ) (inject (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![G,C,m,a,d]
theorem returned_coefficient (G G' C C' m a d r s : PTm n)
    (h : Γ ⊢[PRAAx] transportInput G G' C C' m a d) (hr : Γ ⊢[PRAAx] lt r m) (hs : Γ ⊢[PRAAx] le s (a+d)) : Γ ⊢[PRAAx]
    embed (entry (entry (run G C m a d) r) s) ≐ entry (entry (GaussianPolynomialConstantInjection.inject G' C' m a d) r) s :=
  (embed_congr (entry_congr (entry_congr (program_at _ _ _ _ _) (.eqRefl _)) (.eqRefl _))).eqTrans
    (injected_entry_transport _ _ _ _ _ _ _ _ _ (.andE₁ h) (.andE₁ (.andE₂ h))
      (.andE₁ (.andE₂ (.andE₂ h))) (.andE₂ (.andE₂ (.andE₂ h))) hr hs)

theorem actual_rational_constant_branch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (succ (var 4) ≐ var 1 ⟶ constantRow (var 0) (var 1) (var 2) (var 3) (var 4) ≐ leftPad (normalizedRow (var 0)) (var 3)) :=
  closeUniv 5 (.impI (constant_last _ _ _ _ _ Prf.hyp0))
theorem actual_rational_other_branch_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (neg (succ (var 4) ≐ var 1) ⟶ constantRow (var 0) (var 1) (var 2) (var 3) (var 4) ≐ zeros (succ (var 2+var 3))) :=
  closeUniv 5 (.impI (constant_other _ _ _ _ _ Prf.hyp0))
theorem actual_rational_injection_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (inject (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ var 2 ⋏
      rowShape (inject (var 0) (var 1) (var 2) (var 3) (var 4)) (var 2) (var 3+var 4)) :=
  closeUniv 5 (.andI (inject_length _ _ _ _ _) (inject_shape _ _ _ _ _))
theorem actual_rational_injection_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (transportInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      rowsEmbedded (inject (var 0) (var 2) (var 4) (var 5) (var 6))
        (GaussianPolynomialConstantInjection.inject (var 1) (var 3) (var 4) (var 5) (var 6)) (var 4) (var 5+var 6)) :=
  closeUniv 7 (.impI (injection_transport _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_rational_bivariate_local_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (rowShape (var 0) (var 2) (var 3) ⟶ rowShape (var 1) (var 2) (var 3) ⟶ rowsEmbedded (var 0) (var 1) (var 2) (var 3) ⟶
      embed (RationalBivariateGaussianEmbedding.bivariate (var 0) (var 2) (var 4) (var 5)) ≐
        GaussianRationalHorner.evaluate (GaussianPolynomialMonicCompanion.values (var 1) (var 2) (embed (var 4))) (embed (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (bivariate_transport _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_rational_injection_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ inject (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem actual_rational_returned_injection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (transportInput (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ lt (var 7) (var 4) ⟶ le (var 8) (var 5+var 6) ⟶
      embed (entry (entry (run (var 0) (var 2) (var 4) (var 5) (var 6)) (var 7)) (var 8)) ≐
        entry (entry (GaussianPolynomialConstantInjection.inject (var 1) (var 3) (var 4) (var 5) (var 6)) (var 7)) (var 8)) :=
  closeUniv 9 (.impI (.impI (.impI (returned_coefficient _ _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalPolynomialConstantInjectionGaussianEmbedding
