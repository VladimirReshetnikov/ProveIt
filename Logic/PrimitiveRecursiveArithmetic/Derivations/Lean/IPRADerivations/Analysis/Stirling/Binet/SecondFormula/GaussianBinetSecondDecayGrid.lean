import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondDecayPointwise

/-!
# The actual finite time grid for a second Binet row

Each entry observes the original arctangent and the original
frozen-exponent decay at physical time T*i/N. A second packed body
provides the positive scalar envelope on exactly the same mesh.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayGrid

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetSecondDecayPointwise (row rowEnvelope fullDecay)
open GaussianCompactRiemannName
  (sampleData field0 field1 field2 field3 field4 field5
    field0_at field1_at field2_at field3_at field4_at field5_at
    subst_field0 subst_field1 subst_field2 subst_field3 subst_field4 subst_field5)
open GaussianRationalHorner (qmul)
open GaussianRationalRiemannRefinement (leftSum)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem val_five {α : Type} {k : ℕ} (x : α) (u : Fin (k+5) → α) :
    Matrix.vecCons x u 5 = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))) := rfl
private theorem val_six {α : Type} {k : ℕ} (x : α) (u : Fin (k+6) → α) :
    Matrix.vecCons x u 6 = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u))))) := rfl
private theorem val_seven {α : Type} {k : ℕ} (x : α) (u : Fin (k+7) → α) :
    Matrix.vecCons x u 7 = Matrix.vecHead (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail (Matrix.vecTail u)))))) := rfl

private def packed (f : PTm 8) : PTm 2 := Syn.subst
  ![var 0,field0 (var 1),field1 (var 1),field2 (var 1),field3 (var 1),field4 (var 1),
    fstT (field5 (var 1)),sndT (field5 (var 1))] f

private theorem packed_at (f : PTm 8) (i p N T H J a b : PTm n) :
    Γ ⊢[PRAAx] inst2 (packed f) i (sampleData p N T H J (pairT a b)) ≐ Syn.subst ![i,p,N,T,H,J,a,b] f := by
  let d := sampleData p N T H J (pairT a b)
  have decode : inst2 (packed f) i d =
      Syn.subst ![i,field0 d,field1 d,field2 d,field3 d,field4 d,fstT (field5 d),sndT (field5 d)] f := by
    simp only [packed,inst2,Syn.subst_subst]
    congr 1
    funext k
    fin_cases k <;> simp
  rw [decode]
  exact Prf.eqCongr (Γ := Γ) (Ax := PRAAx) f
    (σ := ![i,field0 d,field1 d,field2 d,field3 d,field4 d,fstT (field5 d),sndT (field5 d)])
    (σ' := ![i,p,N,T,H,J,a,b]) (fun k => by
      fin_cases k
      exact .eqRefl _
      exact field0_at _ _ _ _ _ _
      exact field1_at _ _ _ _ _ _
      exact field2_at _ _ _ _ _ _
      exact field3_at _ _ _ _ _ _
      exact field4_at _ _ _ _ _ _
      exact (congrFst (field5_at _ _ _ _ _ _)).eqTrans (fst_pair _ _)
      exact (congrSnd (field5_at _ _ _ _ _ _)).eqTrans (snd_pair _ _))

private def rowTerm (i p N T H J C x : PTm n) : PTm n :=
  qmul (ap2 GaussianBinetArctangentQuadrature.nameF p (GaussianCompactRiemannName.data (N+zero) (T*i) N C (T*i) x))
    (fullDecay p (T*i) N H J)

@[simp] private theorem subst_rowTerm {k : ℕ} (σ : Fin n → PTm k) (i p N T H J C x : PTm n) :
    Syn.subst σ (rowTerm i p N T H J C x) = rowTerm (Syn.subst σ i) (Syn.subst σ p) (Syn.subst σ N)
      (Syn.subst σ T) (Syn.subst σ H) (Syn.subst σ J) (Syn.subst σ C) (Syn.subst σ x) := by
  simp [rowTerm,fullDecay,two]

private def envelopeTerm (i p N T H J m K : PTm n) : PTm n := rowEnvelope p m K T (T*i) N H J

@[simp] private theorem subst_envelopeTerm {k : ℕ} (σ : Fin n → PTm k) (i p N T H J m K : PTm n) :
    Syn.subst σ (envelopeTerm i p N T H J m K) = envelopeTerm (Syn.subst σ i) (Syn.subst σ p) (Syn.subst σ N)
      (Syn.subst σ T) (Syn.subst σ H) (Syn.subst σ J) (Syn.subst σ m) (Syn.subst σ K) := by
  simp [envelopeTerm]

def rowBody : PTm 2 := packed (rowTerm (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def envelopeBody : PTm 2 := packed (envelopeTerm (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))

def rowData (p N T H J X Y D sign : PTm n) : PTm n :=
  sampleData p N T H J (pairT (D*D) (GaussianBinetArctangentQuadrature.fixedData X Y D sign))
def envelopeData (p N T H J m K : PTm n) : PTm n := sampleData p N T H J (pairT m K)
def value (p N T H J X Y D sign : PTm n) : PTm n := leftSum rowBody N (rowData p N T H J X Y D sign) T one

@[simp] theorem subst_rowData {k : ℕ} (σ : Fin n → PTm k) (p N T H J X Y D sign : PTm n) :
    Syn.subst σ (rowData p N T H J X Y D sign) = rowData (Syn.subst σ p) (Syn.subst σ N)
      (Syn.subst σ T) (Syn.subst σ H) (Syn.subst σ J) (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) := by
  simp [rowData]

@[simp] theorem subst_envelopeData {k : ℕ} (σ : Fin n → PTm k) (p N T H J m K : PTm n) :
    Syn.subst σ (envelopeData p N T H J m K) = envelopeData (Syn.subst σ p) (Syn.subst σ N)
      (Syn.subst σ T) (Syn.subst σ H) (Syn.subst σ J) (Syn.subst σ m) (Syn.subst σ K) := by
  simp [envelopeData]

@[simp] theorem subst_value {k : ℕ} (σ : Fin n → PTm k) (p N T H J X Y D sign : PTm n) :
    Syn.subst σ (value p N T H J X Y D sign) = value (Syn.subst σ p) (Syn.subst σ N)
      (Syn.subst σ T) (Syn.subst σ H) (Syn.subst σ J) (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) := by
  simp [value,one]

theorem row_at (i p N T H J X Y D sign : PTm n) :
    Γ ⊢[PRAAx] inst2 rowBody i (rowData p N T H J X Y D sign) ≐ row p X Y D sign (T*i) N H J := by
  change Γ ⊢[PRAAx] inst2 rowBody i (rowData p N T H J X Y D sign) ≐
    rowTerm i p N T H J (D*D) (GaussianBinetArctangentQuadrature.fixedData X Y D sign)
  simpa only [rowBody,rowData,subst_rowTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,val_five,val_six,val_seven,Matrix.head_cons,Matrix.tail_cons] using
    packed_at (Γ := Γ) (rowTerm (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
      i p N T H J (D*D) (GaussianBinetArctangentQuadrature.fixedData X Y D sign)

theorem envelope_at (i p N T H J m K : PTm n) :
    Γ ⊢[PRAAx] inst2 envelopeBody i (envelopeData p N T H J m K) ≐ rowEnvelope p m K T (T*i) N H J := by
  change Γ ⊢[PRAAx] inst2 envelopeBody i (envelopeData p N T H J m K) ≐ envelopeTerm i p N T H J m K
  simpa only [envelopeBody,envelopeData,subst_envelopeTerm,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,val_five,val_six,val_seven,Matrix.head_cons,Matrix.tail_cons] using
    packed_at (Γ := Γ) (envelopeTerm (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
      i p N T H J m K

end LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayGrid
