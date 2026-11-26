import IPRADerivations.Combinatorics.Bell
import IPRADerivations.Combinatorics.BinomialIdentities
import IPRADerivations.Probability.Independence
import IPRADerivations.AnalyticNumberTheory.Mobius

/-!
# Actual Bell coefficients for the local logarithmic exponential

Packet `analysis/gamma_ipra`, Section 2, the finite coefficient algebra in
(C4). The signed coefficients below are computed by a course-of-values
complete-Bell convolution, with the actual logarithmic derivative kernel
`g_k = (-1)^k k!`. The convolution is the formal-exponential definition;
the specialized two-term differential recurrence is a derived theorem.
Its output is the signed rational coefficient `f_n=B_n/n!`, with a proved
positive denominator. All indices, finite sum lengths and stored-history
lookups are internal. The program has `f_0=f_1=1` and `f_n=0` for `n≥2`.

Identification with a separately evaluated literal finite sum
`Σ H(w)^k/k!`, analytic exponential/logarithm names, and their error/limit
bridges remain separate obligations. No analytic identity is asserted.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.LogarithmExponentialCoefficients

open_ipra
open LeanProofs.IPRA.Combinatorics.Bell (nth iS iS_zero nth_pair_zero nth_pair_succ)
open LeanProofs.IPRA.Combinatorics.Binomial (binom pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq mul_cancel)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.Probability.Independence (sum_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def value (c : PTm n) : ZT n := ⟨fstT c,sndT c⟩
def code (a : ZT n) : PTm n := pairT a.pos a.neg

ipra_subst value [ZT.subst]
ipra_subst code [ZT.subst]

theorem eval_value_code (a : ZT n) : ZT.toZ Γ (value (code a)) = ZT.toZ Γ a := by
  change 𝔞(fstT (pairT a.pos a.neg)) - 𝔞(sndT (pairT a.pos a.neg)) = _
  rw [natEq (fst_pair a.pos a.neg), natEq (snd_pair a.pos a.neg)]
  rfl

theorem eval_value_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    ZT.toZ Γ (value a) = ZT.toZ Γ (value b) := by
  change 𝔞(fstT a)-𝔞(sndT a) = 𝔞(fstT b)-𝔞(sndT b)
  rw [natEq (congrFst h), natEq (congrSnd h)]

/-! ## The actual factorial-cleared local logarithmic derivative -/

def kernelStep : PTm 2 := pairT (succ (var 0)*sndT (var 1)) (succ (var 0)*fstT (var 1))
def kernelF : PR 1 := rec1 (pairT one zero) kernelStep
def kernelCode (k : PTm n) : PTm n := ap1 kernelF k
def kernel (k : PTm n) : ZT n := value (kernelCode k)

ipra_subst kernelCode
ipra_subst kernel

theorem kernel_zero : Γ ⊢[PRAAx] kernelCode (zero : PTm n) ≐ pairT one zero := by
  simpa [kernelCode, kernelF] using rec1_zero (Γ := Γ) (pairT one zero) kernelStep

theorem kernel_succ (k : PTm n) : Γ ⊢[PRAAx] kernelCode (succ k) ≐
    pairT (succ k*sndT (kernelCode k)) (succ k*fstT (kernelCode k)) := by
  simpa [kernelCode, kernelF, kernelStep] using rec1_succ (Γ := Γ) (pairT one zero) kernelStep k

theorem kernel_pos_succ (k : PTm n) :
    Γ ⊢[PRAAx] (kernel (succ k)).pos ≐ succ k*(kernel k).neg :=
  (kernel_succ k).fstE
theorem kernel_neg_succ (k : PTm n) :
    Γ ⊢[PRAAx] (kernel (succ k)).neg ≐ succ k*(kernel k).pos :=
  (kernel_succ k).sndE

theorem kernel_differential (k : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (kernel (succ k) + ZT.ofNat (succ k)*kernel k) (ZT.natLit 0) := by
  have p := natEq (kernel_pos_succ (Γ := Γ) k)
  have q := natEq (kernel_neg_succ (Γ := Γ) k)
  apply ZT.derive
  rw [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat, ZT.toZ_natLit]
  simp only [ZT.toZ]
  ipra_simps
  linear_combination p-q

/-! ## Computed complete-Bell convolution and its stored history -/

def termP (j N L : PTm n) : PTm n :=
  binom N j * ((kernel (monus N j)).pos*(value (nth L (monus N j))).pos +
    (kernel (monus N j)).neg*(value (nth L (monus N j))).neg)
def termM (j N L : PTm n) : PTm n :=
  binom N j * ((kernel (monus N j)).pos*(value (nth L (monus N j))).neg +
    (kernel (monus N j)).neg*(value (nth L (monus N j))).pos)

ipra_subst termP [kernel, value, nth]
ipra_subst termM [kernel, value, nth]

def posBody : PTm 2 := termP (var 0) (fstT (var 1)) (sndT (var 1))
def negBody : PTm 2 := termM (var 0) (fstT (var 1)) (sndT (var 1))
def sumP (r N L : PTm n) : PTm n := ap2 (sumF posBody) r (pairT N L)
def sumM (r N L : PTm n) : PTm n := ap2 (sumF negBody) r (pairT N L)
def convolution (N L : PTm n) : ZT n := ⟨sumP (succ N) N L,sumM (succ N) N L⟩
def tableStep : PTm 2 := pairT (code (convolution (var 0) (var 1))) (var 1)
def tableF : PR 1 := rec1 (pairT (pairT one zero) zero) tableStep
def table (N : PTm n) : PTm n := ap1 tableF N
def coefficientCode (N : PTm n) : PTm n := fstT (table N)
def coefficient (N : PTm n) : ZT n := value (coefficientCode N)

ipra_subst sumP
ipra_subst sumM
ipra_subst convolution [ZT.subst]
ipra_subst table
ipra_subst coefficientCode
ipra_subst coefficient

theorem table_zero : Γ ⊢[PRAAx] table (zero : PTm n) ≐ pairT (pairT one zero) zero := by
  simpa [table, tableF] using rec1_zero (Γ := Γ) (pairT (pairT one zero) zero) tableStep

theorem table_succ (N : PTm n) : Γ ⊢[PRAAx] table (succ N) ≐
    pairT (code (convolution N (table N))) (table N) := by
  simpa [table, tableF, tableStep] using rec1_succ (Γ := Γ) (pairT (pairT one zero) zero) tableStep N

theorem coefficientCode_zero : Γ ⊢[PRAAx] coefficientCode (zero : PTm n) ≐ pairT one zero :=
  table_zero.fstE
theorem coefficientCode_succ (N : PTm n) :
    Γ ⊢[PRAAx] coefficientCode (succ N) ≐ code (convolution N (table N)) :=
  (table_succ N).fstE

theorem coefficient_zero : Γ ⊢[PRAAx] ZT.eq (coefficient (zero : PTm n)) (ZT.natLit 1) := by
  apply ZT.derive
  exact (eval_value_congr coefficientCode_zero).trans (eval_value_code (ZT.natLit 1))

theorem coefficient_succ (N : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (coefficient (succ N)) (convolution N (table N)) := by
  apply ZT.derive
  exact (eval_value_congr (coefficientCode_succ N)).trans (eval_value_code _)

theorem history_succ (N j : PTm n) :
    Γ ⊢[PRAAx] nth (table (succ N)) (succ j) ≐ nth (table N) j :=
  (congrFst (congrAp2 iS (.eqRefl _) (table_succ N))).eqTrans (nth_pair_succ _ _ _)

theorem termP_congr {j j' N N' L L' : PTm n}
    (hj : Γ ⊢[PRAAx] j ≐ j') (hN : Γ ⊢[PRAAx] N ≐ N') (hL : Γ ⊢[PRAAx] L ≐ L') :
    Γ ⊢[PRAAx] termP j N L ≐ termP j' N' L' := by
  have h := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (termP (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![j,N,L]) (σ' := ![j',N',L']) (fun i => by fin_cases i <;> assumption)
  simpa using h
theorem termM_congr {j j' N N' L L' : PTm n}
    (hj : Γ ⊢[PRAAx] j ≐ j') (hN : Γ ⊢[PRAAx] N ≐ N') (hL : Γ ⊢[PRAAx] L ≐ L') :
    Γ ⊢[PRAAx] termM j N L ≐ termM j' N' L' := by
  have h := Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (termM (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![j,N,L]) (σ' := ![j',N',L']) (fun i => by fin_cases i <;> assumption)
  simpa using h

theorem pos_at (j N L : PTm n) : Γ ⊢[PRAAx] inst2 posBody j (pairT N L) ≐ termP j N L := by
  have h : inst2 posBody j (pairT N L) = termP j (fstT (pairT N L)) (sndT (pairT N L)) := by simp [inst2, posBody]
  rw [h]
  exact termP_congr (.eqRefl _) (fst_pair _ _) (snd_pair _ _)
theorem neg_at (j N L : PTm n) : Γ ⊢[PRAAx] inst2 negBody j (pairT N L) ≐ termM j N L := by
  have h : inst2 negBody j (pairT N L) = termM j (fstT (pairT N L)) (sndT (pairT N L)) := by simp [inst2, negBody]
  rw [h]
  exact termM_congr (.eqRefl _) (fst_pair _ _) (snd_pair _ _)

alias monus_succ_le := Common.monus_succ_of_le

/-- The actual binomial coefficient identity used in multiplying the
factorial-cleared derivative by `1+w`. -/
theorem binomial_weight (N j : PTm n) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] binom (succ N) j * succ (monus N j) ≐ succ N*binom N j := by
  have next := natEq (binom_eq (Γ := Γ) (le_trans hj (le_succ_self N)))
  have current := natEq (binom_eq (Γ := Γ) hj)
  have denominator := natEq (congrAp2 factF (monus_succ_le hj) (.eqRefl zero))
  have fstep := natEq (fact_succ (Γ := Γ) (monus N j) zero)
  have nstep := natEq (fact_succ (Γ := Γ) N zero)
  refine mul_cancel (D := fact j*fact (monus N j)) (pos_mul (fact_pos j) (fact_pos _)) ?_
  apply deriveNat
  ipra_simps
  rw [denominator] at next
  linear_combination -next + nstep + (𝔞(N)+1)*current - 𝔞(fact j)*𝔞(binom (succ N) j)*fstep

theorem history_step (N j : PTm n) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] nth (table (succ N)) (monus (succ N) j) ≐ nth (table N) (monus N j) :=
  (congrFst (congrAp2 iS (monus_succ_le hj) (.eqRefl _))).eqTrans (history_succ N _)

theorem termP_step (N j : PTm n) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] termP j (succ N) (table (succ N)) ≐ succ N*termM j N (table N) := by
  have p := natEq ((congrFst (congrAp1 kernelF (monus_succ_le hj))).eqTrans (kernel_pos_succ (monus N j)))
  have q := natEq ((congrSnd (congrAp1 kernelF (monus_succ_le hj))).eqTrans (kernel_neg_succ (monus N j)))
  have a := natEq (congrFst (history_step N j hj))
  have b := natEq (congrSnd (history_step N j hj))
  have weight := natEq (binomial_weight N j hj)
  change 𝔞((kernel (monus (succ N) j)).pos) = 𝔞(succ (monus N j)*(kernel (monus N j)).neg) at p
  change 𝔞((kernel (monus (succ N) j)).neg) = 𝔞(succ (monus N j)*(kernel (monus N j)).pos) at q
  change 𝔞((value (nth (table (succ N)) (monus (succ N) j))).pos) = 𝔞((value (nth (table N) (monus N j))).pos) at a
  change 𝔞((value (nth (table (succ N)) (monus (succ N) j))).neg) = 𝔞((value (nth (table N) (monus N j))).neg) at b
  apply deriveNat
  unfold termP termM
  ipra_simps
  rw [p,q,a,b]
  linear_combination
    (𝔞((kernel (monus N j)).neg)*𝔞((value (nth (table N) (monus N j))).pos)+
      𝔞((kernel (monus N j)).pos)*𝔞((value (nth (table N) (monus N j))).neg))*weight

theorem termM_step (N j : PTm n) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] termM j (succ N) (table (succ N)) ≐ succ N*termP j N (table N) := by
  have p := natEq ((congrFst (congrAp1 kernelF (monus_succ_le hj))).eqTrans (kernel_pos_succ (monus N j)))
  have q := natEq ((congrSnd (congrAp1 kernelF (monus_succ_le hj))).eqTrans (kernel_neg_succ (monus N j)))
  have a := natEq (congrFst (history_step N j hj))
  have b := natEq (congrSnd (history_step N j hj))
  have weight := natEq (binomial_weight N j hj)
  change 𝔞((kernel (monus (succ N) j)).pos) = 𝔞(succ (monus N j)*(kernel (monus N j)).neg) at p
  change 𝔞((kernel (monus (succ N) j)).neg) = 𝔞(succ (monus N j)*(kernel (monus N j)).pos) at q
  change 𝔞((value (nth (table (succ N)) (monus (succ N) j))).pos) = 𝔞((value (nth (table N) (monus N j))).pos) at a
  change 𝔞((value (nth (table (succ N)) (monus (succ N) j))).neg) = 𝔞((value (nth (table N) (monus N j))).neg) at b
  apply deriveNat
  unfold termP termM
  ipra_simps
  rw [p,q,a,b]
  linear_combination
    (𝔞((kernel (monus N j)).neg)*𝔞((value (nth (table N) (monus N j))).neg)+
      𝔞((kernel (monus N j)).pos)*𝔞((value (nth (table N) (monus N j))).pos))*weight

theorem termP_endpoint (N : PTm n) :
    Γ ⊢[PRAAx] termP N N (table N) ≐ (coefficient N).pos := by
  have kernel0 := (congrAp1 kernelF (Γ := Γ) (monus_self N)).eqTrans kernel_zero
  have p := natEq ((congrFst kernel0).eqTrans (fst_pair _ _))
  have q := natEq ((congrSnd kernel0).eqTrans (snd_pair _ _))
  have hist := (congrFst (congrAp2 iS (Γ := Γ) (monus_self N) (.eqRefl (table N)))).eqTrans (congrFst (iS_zero _))
  have a := natEq (congrFst hist)
  have b := natEq (congrSnd hist)
  have c := natEq (Combinatorics.BinomialIdentities.binom_self' (Γ := Γ) N)
  change 𝔞((kernel (monus N N)).pos) = 𝔞(one) at p
  change 𝔞((kernel (monus N N)).neg) = 𝔞(zero) at q
  change 𝔞((value (nth (table N) (monus N N))).pos) = 𝔞((coefficient N).pos) at a
  change 𝔞((value (nth (table N) (monus N N))).neg) = 𝔞((coefficient N).neg) at b
  apply deriveNat
  unfold termP
  ipra_simps
  rw [p,q,a,b,c]
  ring

theorem termM_endpoint (N : PTm n) :
    Γ ⊢[PRAAx] termM N N (table N) ≐ (coefficient N).neg := by
  have kernel0 := (congrAp1 kernelF (Γ := Γ) (monus_self N)).eqTrans kernel_zero
  have p := natEq ((congrFst kernel0).eqTrans (fst_pair _ _))
  have q := natEq ((congrSnd kernel0).eqTrans (snd_pair _ _))
  have hist := (congrFst (congrAp2 iS (Γ := Γ) (monus_self N) (.eqRefl (table N)))).eqTrans (congrFst (iS_zero _))
  have a := natEq (congrFst hist)
  have b := natEq (congrSnd hist)
  have c := natEq (Combinatorics.BinomialIdentities.binom_self' (Γ := Γ) N)
  change 𝔞((kernel (monus N N)).pos) = 𝔞(one) at p
  change 𝔞((kernel (monus N N)).neg) = 𝔞(zero) at q
  change 𝔞((value (nth (table N) (monus N N))).pos) = 𝔞((coefficient N).pos) at a
  change 𝔞((value (nth (table N) (monus N N))).neg) = 𝔞((coefficient N).neg) at b
  apply deriveNat
  unfold termM
  ipra_simps
  rw [p,q,a,b,c]
  ring

/-! ## Finite multiplication by `1+w` and the derived coefficient ODE -/

theorem prefixP (N : PTm n) : Γ ⊢[PRAAx] sumP (succ N) (succ N) (table (succ N)) ≐
    succ N*sumM (succ N) N (table N) := by
  refine sum_scale posBody negBody (succ N) (succ N) (pairT N (table N))
    (pairT (succ N) (table (succ N))) (.allI (.impI ?_))
  simp only [Syn.shift, subst_pairT, subst_table, ConciseIPRA.PTm.subst_succ]
  have h : (lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
    (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  exact (pos_at _ _ _).eqTrans ((termP_step _ _ h).eqTrans (congrMul (.eqRefl _) (neg_at _ _ _).eqSymm))

theorem prefixM (N : PTm n) : Γ ⊢[PRAAx] sumM (succ N) (succ N) (table (succ N)) ≐
    succ N*sumP (succ N) N (table N) := by
  refine sum_scale negBody posBody (succ N) (succ N) (pairT N (table N))
    (pairT (succ N) (table (succ N))) (.allI (.impI ?_))
  simp only [Syn.shift, subst_pairT, subst_table, ConciseIPRA.PTm.subst_succ]
  have h : (lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
    (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  exact (neg_at _ _ _).eqTrans ((termM_step _ _ h).eqTrans (congrMul (.eqRefl _) (pos_at _ _ _).eqSymm))

theorem coefficient_pos_succ (N : PTm n) :
    Γ ⊢[PRAAx] (coefficient (succ N)).pos ≐ sumP (succ N) N (table N) :=
  (coefficientCode_succ N).fstE
theorem coefficient_neg_succ (N : PTm n) :
    Γ ⊢[PRAAx] (coefficient (succ N)).neg ≐ sumM (succ N) N (table N) :=
  (coefficientCode_succ N).sndE

theorem coefficient_split_pos (N : PTm n) :
    Γ ⊢[PRAAx] (coefficient (succ N)).pos ≐ sumP N N (table N)+(coefficient N).pos :=
  (coefficient_pos_succ N).eqTrans ((sum_succ' posBody N (pairT N (table N))).eqTrans
    (congrAdd (.eqRefl _) ((pos_at _ _ _).eqTrans (termP_endpoint N))))
theorem coefficient_split_neg (N : PTm n) :
    Γ ⊢[PRAAx] (coefficient (succ N)).neg ≐ sumM N N (table N)+(coefficient N).neg :=
  (coefficient_neg_succ N).eqTrans ((sum_succ' negBody N (pairT N (table N))).eqTrans
    (congrAdd (.eqRefl _) ((neg_at _ _ _).eqTrans (termM_endpoint N))))

/-- Both natural parts of the actual program have the specialized update;
their cancellation is a consequence of the preceding finite convolution. -/
theorem coefficient_second_pos (N : PTm n) :
    Γ ⊢[PRAAx] (coefficient (succ (succ N))).pos ≐ succ N*(coefficient (succ N)).neg+(coefficient (succ N)).pos :=
  (coefficient_split_pos (succ N)).eqTrans
    (congrAdd ((prefixP N).eqTrans (congrMul (.eqRefl _) (coefficient_neg_succ N).eqSymm)) (.eqRefl _))
theorem coefficient_second_neg (N : PTm n) :
    Γ ⊢[PRAAx] (coefficient (succ (succ N))).neg ≐ succ N*(coefficient (succ N)).pos+(coefficient (succ N)).neg :=
  (coefficient_split_neg (succ N)).eqTrans
    (congrAdd ((prefixM N).eqTrans (congrMul (.eqRefl _) (coefficient_pos_succ N).eqSymm)) (.eqRefl _))

def differentialFormula (N : PTm n) : Fm PTm n :=
  ZT.eq (coefficient (succ N)+ZT.ofNat N*coefficient N) (coefficient N)

ipra_subst differentialFormula

theorem coefficient_one : Γ ⊢[PRAAx] ZT.eq (coefficient (one : PTm n)) (ZT.natLit 1) := by
  have p := natEq (coefficient_split_pos (Γ := Γ) zero)
  have q := natEq (coefficient_split_neg (Γ := Γ) zero)
  have p0 := natEq (sum_zero (Γ := Γ) posBody (pairT (zero : PTm n) (table zero)))
  have q0 := natEq (sum_zero (Γ := Γ) negBody (pairT (zero : PTm n) (table zero)))
  have initial := ZT.toZ_eq (coefficient_zero (Γ := Γ) (n := n))
  change 𝔞((coefficient one).pos) = 𝔞(sumP zero zero (table zero)+(coefficient zero).pos) at p
  change 𝔞((coefficient one).neg) = 𝔞(sumM zero zero (table zero)+(coefficient zero).neg) at q
  change 𝔞(sumP zero zero (table zero)) = 𝔞(zero) at p0
  change 𝔞(sumM zero zero (table zero)) = 𝔞(zero) at q0
  apply ZT.derive
  simp only [ZT.toZ] at initial ⊢
  ipra_simps
  linear_combination p-q+p0-q0+initial

/-- Exact finite coefficient form of `(1+w)F'=F`, before dividing `B_n`
by the positive factorial `n!`. -/
theorem differential_succ (N : PTm n) : Γ ⊢[PRAAx] differentialFormula (succ N) := by
  have p := natEq (coefficient_second_pos (Γ := Γ) N)
  have q := natEq (coefficient_second_neg (Γ := Γ) N)
  apply ZT.derive
  rw [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  ipra_simps
  linear_combination p-q

theorem differential_zero : Γ ⊢[PRAAx] differentialFormula (zero : PTm n) := by
  apply ZT.derive
  rw [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat]
  ipra_simps
  linear_combination ZT.toZ_eq (coefficient_one (Γ := Γ) (n := n))-ZT.toZ_eq (coefficient_zero (Γ := Γ) (n := n))

theorem differential_congr {N M : PTm n} (h : Γ ⊢[PRAAx] N ≐ M)
    (d : Γ ⊢[PRAAx] differentialFormula N) : Γ ⊢[PRAAx] differentialFormula M := by
  have hin : Γ ⊢[PRAAx] (differentialFormula (var 0) : Fm PTm 1).subst ![N] := by simpa using d
  have out := Prf.eqSubst (differentialFormula (var 0) : Fm PTm 1) ![N] ![M]
    (fun i => by fin_cases i; exact h) hin
  simpa using out

theorem differential (N : PTm n) : Γ ⊢[PRAAx] differentialFormula N := by
  refine .orE (zero_or_succ N) ?_ ?_
  · exact differential_congr (Prf.hyp0 : ((N ≐ zero) :: Γ) ⊢[PRAAx] _).eqSymm differential_zero
  · exact differential_congr (Prf.hyp0 : ((N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] _).eqSymm (differential_succ _)

/-! ## Internal vanishing and actual signed rational coefficients -/

/-- Every degree at least two vanishes; the degree is an internal variable. -/
theorem coefficient_vanish (N : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (coefficient (succ (succ N))) (ZT.natLit 0) := by
  have all : Γ ⊢[PRAAx] .all (ZT.eq (coefficient (succ (succ (var 0)))) (ZT.natLit 0)) := by
    ipra_qfind [ZT.subst_eq, subst_coefficient, ZT.subst_natLit]
    · have e := ZT.toZ_eq (differential_succ (Γ := Γ) (zero : PTm n))
      apply ZT.derive
      rw [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat] at e
      ipra_simps
      linear_combination e
    · let Δ : List (Fm PTm (n+1)) := ZT.eq (coefficient (succ (succ (var 0)))) (ZT.natLit 0) :: Γ.map Fm.shift
      have h := ZT.toZ_eq (Prf.hyp0 : Δ ⊢[PRAAx] ZT.eq (coefficient (succ (succ (var 0)))) (ZT.natLit 0))
      have e := ZT.toZ_eq (differential_succ (Γ := Δ) (succ (var 0)))
      apply ZT.derive
      rw [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat] at e
      ipra_simps
      linear_combination e-(𝔞(var 0)+1)*h
  simpa only [ZT.subst_eq, subst_coefficient, ZT.subst_natLit,
    ConciseIPRA.PTm.subst_succ, Syn.subst_var, Syn.inst_zero] using Prf.allE N all

theorem coefficient_vanish_above (N : PTm n) (hN : Γ ⊢[PRAAx] le (num 2) N) :
    Γ ⊢[PRAAx] ZT.eq (coefficient N) (ZT.natLit 0) := by
  have degree : Γ ⊢[PRAAx] N ≐ succ (succ (monus N (num 2))) := (eq_add_of_le hN).eqTrans (by ipra_ring)
  apply ZT.derive
  exact (eval_value_congr (congrFst (congrAp1 tableF degree))).trans (ZT.toZ_eq (coefficient_vanish _))

/-- Numerator code `B_n` and positive denominator `n!`, representing the
formal-exponential coefficient `f_n=B_n/n!` without integer division. -/
def rationalCoefficient (N : PTm n) : PTm n := pairT (coefficientCode N) (fact N)
def rationalCoefficientF : PR 1 := PTm.toPR (rationalCoefficient (var 0))

ipra_subst rationalCoefficient [fact]

theorem rationalCoefficient_at (N : PTm n) :
    Γ ⊢[PRAAx] ap1 rationalCoefficientF N ≐ rationalCoefficient N := by
  simpa [rationalCoefficientF, ap1] using toPR_eq (Γ := Γ) (rationalCoefficient (var 0) : PTm 1) ![N]

theorem coefficient_denominator_positive (N : PTm n) :
    Γ ⊢[PRAAx] le one (sndT (rationalCoefficient N)) :=
  le_congr (.eqRefl _) (snd_pair _ _).eqSymm
    (le_of_eq_add (d := pred (fact N)) ((fact_pos N).eqTrans (by ipra_ring)))

/-- Source `(n+1)f_(n+1)=(1-n)f_n`, on the actual signed rational
coefficient program, with both positive factorial denominators cleared. -/
theorem rational_differential (N : PTm n) : Γ ⊢[PRAAx]
    ZT.eq (ZT.ofNat (succ N*fact N)*coefficient (succ N))
      ((ZT.natLit 1-ZT.ofNat N)*ZT.ofNat (fact (succ N))*coefficient N) := by
  have e := ZT.toZ_eq (differential (Γ := Γ) N)
  have fstep := natEq (fact_succ (Γ := Γ) N zero)
  apply ZT.derive
  rw [ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat] at e
  ipra_simps
  linear_combination (𝔞(N)+1)*𝔞(fact N)*e-(1-𝔞(N))*ZT.toZ Γ (coefficient N)*fstep

/-! ## Identification of the computed kernel with the source log coefficients -/

def evenBit (k : PTm n) : PTm n := eqb (rem k two) zero
def oddBit (k : PTm n) : PTm n := eqb (rem k two) one
def kernelParity (k : PTm n) : Fm PTm n :=
  ((kernel k).pos ≐ evenBit k*fact k) ⋏ ((kernel k).neg ≐ oddBit k*fact k)

ipra_subst evenBit [two, one]
ipra_subst oddBit [two, one]
ipra_subst kernelParity [kernel, value, fact, ZT.subst]

theorem evenBit_zero : Γ ⊢[PRAAx] evenBit (zero : PTm n) ≐ one :=
  (AnalyticNumberTheory.Mobius.congrEqb' (rem_zero two) (.eqRefl _)).eqTrans (eqb_of_eq (.eqRefl _))
theorem oddBit_zero : Γ ⊢[PRAAx] oddBit (zero : PTm n) ≐ zero :=
  (AnalyticNumberTheory.Mobius.congrEqb' (rem_zero two) (.eqRefl _)).eqTrans
    (eqb_of_ne AnalyticNumberTheory.Mobius.zero_ne_one')

theorem kernel_parity (k : PTm n) : Γ ⊢[PRAAx] kernelParity k := by
  have all : Γ ⊢[PRAAx] .all (kernelParity (var 0)) := by
    ipra_qfind (⟨trivial,trivial⟩) [subst_kernelParity]
    · exact .andI
        (kernel_zero.fstE.eqTrans
          ((congrMul evenBit_zero (fact_zero zero)).eqTrans (one_mul one)).eqSymm)
        (kernel_zero.sndE.eqTrans
          ((congrMul oddBit_zero (fact_zero zero)).eqTrans (zero_mul one)).eqSymm)
    · let Δ : List (Fm PTm (n+1)) := kernelParity (var 0) :: Γ.map Fm.shift
      have ep : Δ ⊢[PRAAx] evenBit (succ (var 0)) ≐ oddBit (var 0) :=
        Prf.andE₁ (AnalyticNumberTheory.Mobius.par_succ _)
      have op : Δ ⊢[PRAAx] oddBit (succ (var 0)) ≐ evenBit (var 0) :=
        Prf.andE₂ (AnalyticNumberTheory.Mobius.par_succ _)
      refine .andI ?_ ?_
      · ipra_lc natEq (kernel_pos_succ (Γ := Δ) (var 0))+
          (𝔞(var 0)+1)*natEq (Prf.andE₂ (Prf.hyp0 : Δ ⊢[PRAAx] kernelParity (var 0)))-
          (𝔞(var 0)+1)*𝔞(fact (var 0))*natEq ep -𝔞(evenBit (succ (var 0)))*natEq (fact_succ (Γ := Δ) (var 0) zero)
      · ipra_lc natEq (kernel_neg_succ (Γ := Δ) (var 0))+
          (𝔞(var 0)+1)*natEq (Prf.andE₁ (Prf.hyp0 : Δ ⊢[PRAAx] kernelParity (var 0)))-
          (𝔞(var 0)+1)*𝔞(fact (var 0))*natEq op -𝔞(oddBit (succ (var 0)))*natEq (fact_succ (Γ := Δ) (var 0) zero)
  simpa only [subst_kernelParity,Syn.subst_var,Syn.inst_zero] using Prf.allE k all

/-- The actual source coefficient at degree `k+1`: `(-1)^k/(k+1)`.
Its computed numerator/denominator are `g_k/(k+1)!`. -/
def logCoefficient (k : PTm n) : PTm n := pairT (kernelCode k) (fact (succ k))

theorem logarithmic_coefficient (k : PTm n) : Γ ⊢[PRAAx]
    ZT.eq (ZT.ofNat (succ k)*kernel k)
      (ZT.ofNat (fact (succ k))*(⟨evenBit k,oddBit k⟩ : ZT n)) := by
  have p := natEq (Prf.andE₁ (kernel_parity (Γ := Γ) k))
  have q := natEq (Prf.andE₂ (kernel_parity (Γ := Γ) k))
  have fstep := natEq (fact_succ (Γ := Γ) k zero)
  apply ZT.derive
  rw [ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [ZT.toZ]
  ipra_simps
  linear_combination (𝔞(k)+1)*(p-q)-(𝔞(evenBit k)-𝔞(oddBit k))*fstep

/-! ## Correct stored history and closed program certificates -/

@[simp] theorem subst_history {m : ℕ} (σ : Fin n → PTm m) (L j : PTm n) :
    Syn.subst σ (nth L j) = nth (Syn.subst σ L) (Syn.subst σ j) := by simp [nth]

/-- This reads an actual earlier program output, rather than postulating
an already correct course-of-values oracle. -/
theorem history_add (N j : PTm n) :
    Γ ⊢[PRAAx] nth (table (N+j)) j ≐ coefficientCode N := by
  have all : Γ ⊢[PRAAx] .all (nth (table (Syn.shift N+var 0)) (var 0) ≐ coefficientCode (Syn.shift N)) := by
    ipra_qfind [subst_history, subst_table, subst_coefficientCode]
    · exact (congrFst (congrAp2 iS (.eqRefl _) (congrAp1 tableF (add_zero N)))).eqTrans (congrFst (iS_zero _))
    · exact (congrFst (congrAp2 iS (.eqRefl _) (congrAp1 tableF (add_succ _ _)))).eqTrans
        ((history_succ _ _).eqTrans Prf.hyp0)
  simpa only [Fm.subst_eq,subst_history,subst_table,subst_coefficientCode,PTm.subst_add,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using Prf.allE j all

theorem history_at (N j : PTm n) (hj : Γ ⊢[PRAAx] le j N) :
    Γ ⊢[PRAAx] nth (table N) j ≐ coefficientCode (monus N j) :=
  (congrFst (congrAp2 iS (.eqRefl _) (congrAp1 tableF ((eq_add_of_le hj).eqTrans (add_comm _ _))))).eqTrans
    (history_add _ _)

theorem logarithmic_denominator_positive (k : PTm n) :
    Γ ⊢[PRAAx] le one (sndT (logCoefficient k)) :=
  le_congr (.eqRefl _) (snd_pair _ _).eqSymm
    (le_of_eq_add (d := pred (fact (succ k))) ((fact_pos (succ k)).eqTrans (by ipra_ring)))

theorem logarithmic_kernel_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (kernelParity (var 0) ⋏
        (le one (sndT (logCoefficient (var 0))) ⋏
          ZT.eq (ZT.ofNat (succ (var 0))*kernel (var 0))
            (ZT.ofNat (fact (succ (var 0)))*(⟨evenBit (var 0),oddBit (var 0)⟩ : ZT 1)))) :=
  closeUniv 1 (.andI (kernel_parity _) (.andI (logarithmic_denominator_positive _) (logarithmic_coefficient _)))

theorem bell_history_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (nth (table (var 0+var 1)) (var 1) ≐ coefficientCode (var 0)) :=
  closeUniv 2 (history_add _ _)

theorem bell_convolution_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (ZT.eq (coefficient (succ (var 0))) (convolution (var 0) (table (var 0)))) :=
  closeUniv 1 (coefficient_succ _)

theorem bell_initials_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx]
      (ZT.eq (coefficient zero) (ZT.natLit 1) ⋏ ZT.eq (coefficient one) (ZT.natLit 1)) :=
  .andI coefficient_zero coefficient_one

theorem bell_differential_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (differentialFormula (var 0)) :=
  closeUniv 1 (differential _)

theorem bell_vanishing_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (ZT.eq (coefficient (succ (succ (var 0)))) (ZT.natLit 0)) :=
  closeUniv 1 (coefficient_vanish _)

theorem bell_vanishing_above_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (le (num 2) (var 0) ⟶ ZT.eq (coefficient (var 0)) (ZT.natLit 0)) :=
  closeUniv 1 (.impI (coefficient_vanish_above _ Prf.hyp0))

/-- Actual signed numerator/positive factorial denominator metadata. -/
theorem rational_coefficient_program_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      ((ap1 rationalCoefficientF (var 0) ≐ rationalCoefficient (var 0)) ⋏
        ((fstT (rationalCoefficient (var 0)) ≐ coefficientCode (var 0)) ⋏
          ((sndT (rationalCoefficient (var 0)) ≐ fact (var 0)) ⋏
            le one (sndT (rationalCoefficient (var 0)))))) :=
  closeUniv 1 (.andI (rationalCoefficient_at _) (.andI (fst_pair _ _)
    (.andI (snd_pair _ _) (coefficient_denominator_positive _))))

/-- The source rational recurrence, with all degrees and factorials internal. -/
theorem rational_coefficient_recurrence_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (le one (sndT (rationalCoefficient (var 0))) ⋏
        (le one (sndT (rationalCoefficient (succ (var 0)))) ⋏
          ZT.eq (ZT.ofNat (succ (var 0)*fact (var 0))*coefficient (succ (var 0)))
            ((ZT.natLit 1-ZT.ofNat (var 0))*ZT.ofNat (fact (succ (var 0)))*coefficient (var 0)))) :=
  closeUniv 1 (.andI (coefficient_denominator_positive _) (.andI (coefficient_denominator_positive _) (rational_differential _)))

theorem rational_initial_zero : Γ ⊢[PRAAx]
    ZT.eq (coefficient (zero : PTm n)) (ZT.ofNat (fact zero)) := by
  ipra_lc ZT.toZ_eq (coefficient_zero (Γ := Γ) (n := n))-natEq (fact_zero (Γ := Γ) (zero : PTm n))

theorem rational_initial_one : Γ ⊢[PRAAx]
    ZT.eq (coefficient (one : PTm n)) (ZT.ofNat (fact one)) := by
  ipra_lc ZT.toZ_eq (coefficient_one (Γ := Γ) (n := n))-natEq (fact_succ (Γ := Γ) (zero : PTm n) zero)-
    natEq (fact_zero (Γ := Γ) (zero : PTm n))

/-- These are the cleared rational equalities `f_0=f_1=1`; the actual
numerator and denominator fields are linked by the program certificate. -/
theorem rational_initials_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx]
      (ZT.eq (coefficient zero) (ZT.ofNat (fact zero)) ⋏
        ZT.eq (coefficient one) (ZT.ofNat (fact one))) :=
  .andI rational_initial_zero rational_initial_one

#print axioms kernel_differential
#print axioms coefficient_succ
#print axioms binomial_weight
#print axioms termP_step
#print axioms termM_step
#print axioms coefficient_second_pos
#print axioms coefficient_one
#print axioms differential
#print axioms coefficient_vanish
#print axioms coefficient_vanish_above
#print axioms rational_differential
#print axioms kernel_parity
#print axioms logarithmic_coefficient
#print axioms history_at
#print axioms logarithmic_kernel_closed
#print axioms bell_history_closed
#print axioms bell_convolution_closed
#print axioms bell_initials_closed
#print axioms bell_differential_closed
#print axioms bell_vanishing_closed
#print axioms bell_vanishing_above_closed
#print axioms rational_coefficient_program_closed
#print axioms rational_coefficient_recurrence_closed
#print axioms rational_initials_closed

end LeanProofs.IPRA.Analysis.LogarithmExponentialCoefficients
