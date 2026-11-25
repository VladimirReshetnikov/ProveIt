import IPRADerivations.Analysis.GaussianArctangentPartialQuadrature

/-!
# Matched-grid arctangent chord comparison

For a prefix of length J in a mesh M with J ≤ M, each row is
compared with the same row on the full mesh J. After clearing the
row denominators, the comparison has slack (M²−J²)(J²−k²).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentChordComparison

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open BaselQuadrature (Qb uq inst_Qb u_eq)
open GaussianArctangentCayleyValues (denominator denominator_positive)
open GaussianArctangentExponentialPrefix (total subst_total)
open Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.FiniteHausdorff (sum_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem cleared_row (k J M : PTm n) (hk : Γ ⊢[PRAAx] le k J) (hJ : Γ ⊢[PRAAx] le J M) :
    Γ ⊢[PRAAx] le ((M*M+J*J)*denominator J k) (two*(J*J)*denominator M k) := by
  have u := natEq (eq_add_of_le (le_mul_mono hJ hJ))
  have v := natEq (eq_add_of_le (le_mul_mono hk hk))
  refine le_of_eq_add (d := monus (M*M) (J*J)*monus (J*J) (k*k)) ?_
  apply deriveNat
  unfold denominator
  simp only [Q.mk_add,Q.mk_mul,map_add,map_mul] at u v
  ipra_simps
  rw [u,v]
  ring

private theorem quotient_exact (k M L : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (hL : Γ ⊢[PRAAx] le (two*(M*M)) L) (hk : Γ ⊢[PRAAx] lt k M) :
    Γ ⊢[PRAAx] fact L ≐ denominator M k*uq k M L := by
  have h := RationalIntegerNormalization.positive_form hM
  have m := congrMul h h
  have d := congrAdd m (.eqRefl (k*k))
  have q := congrAp2 quoF (.eqRefl (fact L)) d
  exact (u_eq (lt_congr (.eqRefl _) h hk) (le_congr (congrMul (.eqRefl two) m) (.eqRefl _) hL)).eqTrans
    (congrMul d q).eqSymm

private theorem matched_row (k J M L : PTm n) (hJ : Γ ⊢[PRAAx] le J M)
    (hL : Γ ⊢[PRAAx] le (two*(M*M)) L) (hk : Γ ⊢[PRAAx] lt k J) :
    Γ ⊢[PRAAx] le ((M*M+J*J)*(M*uq k M L)) ((two*M*J)*(J*uq k J L)) := by
  let d := denominator M k
  let e := denominator J k
  have hJp : Γ ⊢[PRAAx] le one J := le_trans (zero_lt_succ k) hk
  have hMp := le_trans hJp hJ
  have hkM : Γ ⊢[PRAAx] lt k M := le_trans hk hJ
  have hd := denominator_positive M k hMp
  have he := denominator_positive J k hJp
  have hLJ := le_trans (le_mul_mono (le_refl two) (le_mul_mono hJ hJ)) hL
  have u := natEq (quotient_exact k M L hMp hL hkM)
  have v := natEq (quotient_exact k J L hJp hLJ hk)
  have base := le_mul_mono (le_refl (M*fact L)) (cleared_row k J M (le_of_lt hk) hJ)
  refine RationalValueBounds.positive_cancel (GaussianRationalHorner.positive_product d e hd he)
    (le_congr ?_ ?_ base)
  · apply deriveNat
    ipra_simps
    linear_combination 𝔞(M)*𝔞(e)*(𝔞(M)*𝔞(M)+𝔞(J)*𝔞(J))*u
  · apply deriveNat
    ipra_simps
    linear_combination 2*𝔞(M)*𝔞(d)*𝔞(J)*𝔞(J)*v

private theorem total_succ (j M L : PTm n) :
    Γ ⊢[PRAAx] total (succ j) M L ≐ total j M L+M*uq j M L :=
  (sum_succ Qb j (pairT M L)).eqTrans (congrAdd (.eqRefl _) (inst_Qb j M L))

private def prefixComparison (j J M L : PTm n) : Fm PTm n :=
  le ((M*M+J*J)*total j M L) ((two*M*J)*total j J L)

private theorem step (j J M L : PTm n) (hJ : Γ ⊢[PRAAx] le J M)
    (hL : Γ ⊢[PRAAx] le (two*(M*M)) L) (hj : Γ ⊢[PRAAx] lt j J)
    (ih : Γ ⊢[PRAAx] prefixComparison j J M L) :
    Γ ⊢[PRAAx] prefixComparison (succ j) J M L := by
  unfold prefixComparison at ih ⊢
  have c := sum_mono ih (matched_row j J M L hJ hL hj)
  have a : Γ ⊢[PRAAx] (M*M+J*J)*total (succ j) M L ≐
      (M*M+J*J)*total j M L+(M*M+J*J)*(M*uq j M L) :=
    (congrMul (.eqRefl _) (total_succ j M L)).eqTrans (by ipra_ring)
  have b : Γ ⊢[PRAAx] (two*M*J)*total (succ j) J L ≐
      (two*M*J)*total j J L+(two*M*J)*(J*uq j J L) :=
    (congrMul (.eqRefl _) (total_succ j J L)).eqTrans (by ipra_ring)
  exact le_congr a.eqSymm b.eqSymm c

private theorem prefix_zero (J M L : PTm n) :
    Γ ⊢[PRAAx] prefixComparison zero J M L := by
  refine le_congr ?_ ?_ (le_refl zero)
  · exact ((congrMul (.eqRefl _) (sum_zero Qb (pairT M L))).eqTrans (mul_zero _)).eqSymm
  · exact ((congrMul (.eqRefl _) (sum_zero Qb (pairT J L))).eqTrans (mul_zero _)).eqSymm

@[simp] private theorem subst_prefixComparison {m : ℕ} (σ : Fin n → PTm m) (j J M L : PTm n) :
    (prefixComparison j J M L).subst σ = prefixComparison (Syn.subst σ j) (Syn.subst σ J) (Syn.subst σ M) (Syn.subst σ L) := by
  simp [prefixComparison]

theorem matched_prefix_bound (j J M L : PTm n)
    (hJ : Γ ⊢[PRAAx] le J M) (hL : Γ ⊢[PRAAx] le (two*(M*M)) L) (hj : Γ ⊢[PRAAx] le j J) :
    Γ ⊢[PRAAx] le ((M*M+J*J)*total j M L) ((two*M*J)*total j J L) := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift J) ⟶
      prefixComparison (var 0) (Syn.shift J) (Syn.shift M) (Syn.shift L)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp,subst_le,subst_prefixComparison,
        Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact .impI (prefix_zero J M L).wk
    · simp only [Fm.subst_imp,subst_le,subst_prefixComparison,
        Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      refine .impI ?_
      let i : PTm (n+1) := var 0
      let K := Syn.shift J
      let T := Syn.shift M
      let D := Syn.shift L
      let Δ := le (succ i) K :: (le i K ⟶ prefixComparison i K T D) :: Γ.map Fm.shift
      have h : Γ.map Fm.shift ⊢[PRAAx] le K T := by
        simpa only [Fm.shift,subst_le,Syn.shift,K,T] using hJ.shift
      have hl : Γ.map Fm.shift ⊢[PRAAx] le (two*(T*T)) D := by
        simpa only [Fm.shift,subst_le,PTm.subst_mul,PTm.subst_succ,PTm.subst_zero,Syn.shift,T,D] using hL.shift
      have hi : Δ ⊢[PRAAx] lt i K := Prf.hyp0
      have prev : Δ ⊢[PRAAx] prefixComparison i K T D := .impE Prf.hyp1 (le_of_lt hi)
      exact step i K T D h.wk.wk hl.wk.wk hi prev
  have inst : Γ ⊢[PRAAx] le j J ⟶ prefixComparison j J M L := by
    simpa only [Fm.subst_imp,subst_le,subst_prefixComparison,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE j
  exact .impE inst hj

theorem actual_arctangent_matched_prefix_chord_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 0) (var 1) ⟶ le (two*(var 1*var 1)) (var 2) ⟶
      le ((var 1*var 1+var 0*var 0)*total (var 0) (var 1) (var 2))
        ((two*var 1*var 0)*total (var 0) (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (matched_prefix_bound _ _ _ _ Prf.hyp1 Prf.hyp0 (le_refl _))))

end LeanProofs.IPRA.Analysis.GaussianArctangentChordComparison
