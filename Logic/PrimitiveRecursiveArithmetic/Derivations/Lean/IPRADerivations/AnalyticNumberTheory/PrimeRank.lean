import IPRADerivations.AnalyticNumberTheory.PrimesModFour
import IPRADerivations.AnalyticNumberTheory.PiTheta
import IPRADerivations.Foundations.IterationFusion
import IPRADerivations.Foundations.CrossingSearch
import IPRADerivations.Core.CertificateTactics
import IPRADerivations.Core.CommonLemmas

/-!
# Rank and inverse rank of the primes

Packet: `analytic-number-theory/prime-counting-ipra`, `sections/foundations.tex`, Theorem "Rank and inverse rank".

`π(x) = ∑_{d ≤ x} [d prime]` is `PiTheta.Pi`; here `pc x = Pi x 0`.

* `pc_zero`, `pc_succ`, `pc_prime`, `pc_step_le`, `pc_mono`: `π(0) = 0`, `π(x + 1) = π(x) + [x + 1 prime]`, the
  jumps are `0` or `1`, and `π` is nondecreasing;
* `ep`, `ep_spec`: Euclid's prime `ℓ(N! + 1)`, a prime `> N` and `≤ N! + 1`; `pc_euclid`: `π(N! + 1) ≥ π(N) + 1`;
* `E`, `E_succ`, `rank`: the uniform bound `E(0) = 1`, `E(k + 1) = E(k)! + 1` of the inverse search, with
  `π(E(k)) ≥ k` by quantifier-free induction;
* `pk`: the `k`-th prime `p_k`, the least `i ≤ E(k)` with `π(i) ≥ k` (a bounded search);
  `pk_spec`: `p_k ≤ E(k)` and `π(p_k) ≥ k`; `pk_min`: `π(j) < k` for `j < p_k`; `pk_le_of`: `p_k ≤ i` whenever
  `π(i) ≥ k`;
* **`pk_rank`**: for `k ≥ 1`, `π(p_k) = k` and `p_k` is prime;
* **`pk_pc_le`**, **`lt_pk_pc`**: `p_{π(x)} ≤ x < p_{π(x)+1}`;
* `pk_strict`: `p_k < p_{k+1}` for `k ≥ 1`;
* `pk_of_prime`, `prime_of_pk`: `p_{π(x)} = x` for prime `x`, and every value `p_k`, `k ≥ 1`, is prime.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PrimeRank

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (prime lpf fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (isP isP_01 prime_of_isP isP_of_prime prime_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorVector (lpf_prime' lpf_dvd')
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (prime_two)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (p_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.PiTheta (piB inst2_piB Pi)
open LeanProofs.IPRA.AnalyticNumberTheory.PrimesModFour (gt_of_dvd)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_le')
open LeanProofs.IPRA.Foundations.BoundedReflection (exB wit ex_intro ex_elim ex_least)
open LeanProofs.IPRA.Foundations.CrossingSearch (wit_le_of)
open LeanProofs.IPRA.Foundations.IterationFusion (iter iter_zero iter_succ app1)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Order helpers -/

alias le_of_lt_succ := Common.le_of_lt_succ

alias succ_le_succ := Common.succ_le_succ

theorem lt_succ_self (a : PTm n) : Γ ⊢[PRAAx] lt a (succ a) := le_refl (succ a)

theorem succ_add_alg {a b d : PTm n} (e : Γ ⊢[PRAAx] b ≐ a + d) : Γ ⊢[PRAAx] succ b ≐ succ a + d := by
  ipra_lc natEq e

theorem alg0 {A B I : PTm n} (e : Γ ⊢[PRAAx] A ≐ B + I) (z : Γ ⊢[PRAAx] I ≐ zero) : Γ ⊢[PRAAx] B ≐ A := by
  ipra_lc -natEq e - natEq z

theorem alg1 {A B I : PTm n} (e : Γ ⊢[PRAAx] A ≐ B + I) (o : Γ ⊢[PRAAx] I ≐ one) : Γ ⊢[PRAAx] A ≐ succ B := by
  ipra_lc natEq e + natEq o

/-! ## The counting function -/

/-- `π(x) = ∑_{d ≤ x} [d prime]`. -/
abbrev pc (x : PTm n) : PTm n := Pi x zero

theorem congrPc {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] pc a ≐ pc b :=
  congrAp2 _ (congrSucc h) (.eqRefl _)

/-- `0` and `1` are not prime. -/
theorem isP_small {q : PTm n} (h : Γ ⊢[PRAAx] le q one) : Γ ⊢[PRAAx] isP q ≐ zero := by
  refine .orE (isP_01 q) Prf.hyp0 ?_
  have hp : ((isP q ≐ one) :: Γ) ⊢[PRAAx] lt one q :=
    prime_two (prime_of_isP (Γ := (isP q ≐ one) :: Γ) Prf.hyp0)
  exact lt_irrefl one _ (lt_of_lt_of_le hp h.wk)

theorem pc_succ (x : PTm n) : Γ ⊢[PRAAx] pc (succ x) ≐ pc x + isP (succ x) := by
  have h := sum_succ' (Γ := Γ) piB (succ x) zero
  rw [inst2_piB] at h
  exact h

theorem pc_zero : Γ ⊢[PRAAx] pc (zero : PTm n) ≐ zero := by
  have h := sum_succ' (Γ := Γ) piB zero zero
  rw [inst2_piB] at h
  have z1 : Γ ⊢[PRAAx] le (zero : PTm n) one := zero_monus one
  exact h.eqTrans ((congrAdd (sum_zero _ _) (isP_small z1)).eqTrans (zero_add zero))

/-- The jump at a prime. -/
theorem pc_prime {x : PTm n} (hp : Γ ⊢[PRAAx] prime (succ x)) : Γ ⊢[PRAAx] pc (succ x) ≐ succ (pc x) :=
  alg1 (pc_succ x) (isP_of_prime hp)

/-- The jumps are at most `1`. -/
theorem pc_step_le (x : PTm n) : Γ ⊢[PRAAx] le (pc (succ x)) (succ (pc x)) := by
  refine .orE (isP_01 (succ x)) ?_ ?_
  · have e := alg0 (pc_succ (Γ := (isP (succ x) ≐ zero) :: Γ) x) Prf.hyp0
    exact le_trans (le_congr e (.eqRefl _) (le_refl _)) (le_of_lt (lt_succ_self _))
  · have e := alg1 (pc_succ (Γ := (isP (succ x) ≐ one) :: Γ) x) Prf.hyp0
    exact le_congr e.eqSymm (.eqRefl _) (le_refl _)

/-- `π` is nondecreasing. -/
theorem pc_mono {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (pc a) (pc b) :=
  le_of_eq_add ((congrAp2 _ (succ_add_alg (eq_add_of_le h)) (.eqRefl _)).eqTrans
    (sum_split piB (succ a) (monus b a) zero))

/-! ## Euclid's prime -/

/-- `N! + 1`, in the form `N! · 1 + 1`. -/
abbrev EN (N : PTm n) : PTm n := fact N * one + one

/-- Euclid's prime `ℓ(N! + 1)`. -/
abbrev ep (N : PTm n) : PTm n := lpf (EN N)

/-- `ℓ(N! + 1)` is a prime `> N` and `≤ N! + 1`. -/
theorem ep_spec (N : PTm n) : Γ ⊢[PRAAx] prime (ep N) ⋏ (lt N (ep N) ⋏ le (ep N) (EN N)) := by
  have fp := natEq (fact_pos (Γ := Γ) N)
  have hT : Γ ⊢[PRAAx] le two (EN N) := by
    ipra_le 𝔞 (pred (fact N)) with fp
  have hp := lpf_prime' hT
  have hd := lpf_dvd' hT
  have hp2 := prime_two hp
  exact .andI hp (.andI (gt_of_dvd hp2 hd) (dvd_le' (p_pos hp2) hd (p_pos hT)))

/-- `π(N! + 1) ≥ π(N) + 1`. -/
theorem pc_euclid (N : PTm n) : Γ ⊢[PRAAx] le (succ (pc N)) (pc (EN N)) := by
  have s := ep_spec (Γ := Γ) N
  have hp := Prf.andE₁ s
  have hgt := Prf.andE₁ (Prf.andE₂ s)
  have hle := Prf.andE₂ (Prf.andE₂ s)
  have hq := p_pos (prime_two hp)
  have hN : Γ ⊢[PRAAx] le N (pred (ep N)) := le_of_lt_succ (lt_congr (.eqRefl _) hq hgt)
  have j : Γ ⊢[PRAAx] pc (succ (pred (ep N))) ≐ succ (pc (pred (ep N))) := pc_prime (prime_congr hq hp)
  have m1 := pc_mono hN
  have m2 : Γ ⊢[PRAAx] le (pc (succ (pred (ep N)))) (pc (EN N)) := pc_mono (le_congr hq (.eqRefl _) hle)
  exact le_trans (le_congr (.eqRefl _) j.eqSymm (succ_le_succ m1)) m2

/-! ## The bound of the inverse search -/

/-- `t ↦ t! + 1`. -/
abbrev stepE : PTm 1 := fact (var 0) * one + one

/-- `E(0) = 1`, `E(k + 1) = E(k)! + 1`. -/
abbrev E (k : PTm n) : PTm n := iter stepE k one

theorem E_zero : Γ ⊢[PRAAx] E (zero : PTm n) ≐ one := iter_zero _ _

theorem E_succ (k : PTm n) : Γ ⊢[PRAAx] E (succ k) ≐ EN (E k) := by
  have h := iter_succ (Γ := Γ) stepE k one
  have e : app1 stepE (E k) = EN (E k) := by simp [app1, subst_ap2, PTm.subst_add, PTm.subst_mul]
  rw [e] at h
  exact h

/-- `k ≤ π(E(k))`; variable `0 = k`. -/
abbrev rankF : Fm PTm 1 := le (var 0) (pc (E (var 0)))

theorem rank_open : ([] : List (Fm PTm 1)) ⊢[PRAAx] rankF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    exact zero_monus _
  · simp only [subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero,
      ConciseIPRA.PTm.subst_succ]
    have ih : [rankF] ⊢[PRAAx] le (var 0) (pc (E (var 0))) := Prf.hyp0
    exact le_trans (succ_le_succ ih)
      (le_congr (.eqRefl _) (congrPc (E_succ (var 0)).eqSymm) (pc_euclid (E (var 0))))

theorem rank (k : PTm n) : Γ ⊢[PRAAx] le k (pc (E k)) := by
  have i := inst (Γ := Γ) rank_open ![k]
  simpa [subst_le, subst_ap2] using i

/-! ## The `k`-th prime -/

/-- The test `k ≤ π(i)` as the value `(π(i) + 1) ∸ k`, over `0 = i`, `1 = k`. -/
abbrev geB : PTm 2 := monus (succ (ap2 (sumF piB) (succ (var 0)) zero)) (var 1)

theorem inst2_geB (i k : PTm n) : inst2 geB i k = monus (succ (pc i)) k := by
  simp [inst2, subst_ap2, PTm.subst_monus]

theorem ge_ne {i k : PTm n} (h : Γ ⊢[PRAAx] le k (pc i)) : Γ ⊢[PRAAx] neg (inst2 geB i k ≐ zero) := by
  rw [inst2_geB]
  refine .impI ?_
  have hl : ((monus (succ (pc i)) k ≐ zero) :: Γ) ⊢[PRAAx] lt (pc i) k := Prf.hyp0
  exact le_lt_absurd _ h.wk hl

theorem ge_of_ne {i k : PTm n} (h : Γ ⊢[PRAAx] neg (inst2 geB i k ≐ zero)) : Γ ⊢[PRAAx] le k (pc i) := by
  rw [inst2_geB] at h
  refine .orE (lt_or_le (pc i) k) ?_ Prf.hyp0
  have hl : (lt (pc i) k :: Γ) ⊢[PRAAx] monus (succ (pc i)) k ≐ zero := Prf.hyp0
  exact .botE _ (.impE h.wk hl)

/-- The `k`-th prime `p_k` (with `p_0 = 0`): the least `i ≤ E(k)` with `π(i) ≥ k`. -/
abbrev pk (k : PTm n) : PTm n := wit geB (succ (E k)) k

/-- `p_k ≤ E(k)` and `π(p_k) ≥ k`. -/
theorem pk_spec (k : PTm n) : Γ ⊢[PRAAx] le (pk k) (E k) ⋏ le k (pc (pk k)) := by
  have ex := ex_intro geB (ge_ne (rank (Γ := Γ) k)) (lt_succ_self (E k))
  have el := ex_elim geB ex
  exact .andI (le_of_lt_succ (Prf.andE₁ el)) (ge_of_ne (Prf.andE₂ el))

/-- Minimality: `π(j) < k` for `j < p_k`. -/
theorem pk_min {j k : PTm n} (h : Γ ⊢[PRAAx] lt j (pk k)) : Γ ⊢[PRAAx] lt (pc j) k := by
  have m := ex_least geB h
  rw [inst2_geB] at m
  exact m

/-- `p_k ≤ i` whenever `π(i) ≥ k`. -/
theorem pk_le_of {i k : PTm n} (h : Γ ⊢[PRAAx] le k (pc i)) : Γ ⊢[PRAAx] le (pk k) i :=
  wit_le_of geB (ge_ne h)

/-- `p_k ≥ 1` for `k ≥ 1`. -/
theorem pk_succ_form (k : PTm n) : Γ ⊢[PRAAx] pk (succ k) ≐ succ (pred (pk (succ k))) := by
  refine .orE (zero_or_succ (pk (succ k))) ?_ Prf.hyp0
  have h0 : ((pk (succ k) ≐ zero) :: Γ) ⊢[PRAAx] pk (succ k) ≐ zero := Prf.hyp0
  have s := Prf.andE₂ (pk_spec (Γ := (pk (succ k) ≐ zero) :: Γ) (succ k))
  have s0 : ((pk (succ k) ≐ zero) :: Γ) ⊢[PRAAx] lt k zero :=
    le_congr (.eqRefl _) ((congrPc h0).eqTrans pc_zero) s
  exact lt_zero_absurd _ s0

/-- **Rank**: `π(p_k) = k` and `p_k` is prime, for `k ≥ 1`. -/
theorem pk_rank (k : PTm n) : Γ ⊢[PRAAx] (pc (pk (succ k)) ≐ succ k) ⋏ prime (pk (succ k)) := by
  have hq := pk_succ_form (Γ := Γ) k
  have s := Prf.andE₂ (pk_spec (Γ := Γ) (succ k))
  have below : Γ ⊢[PRAAx] lt (pred (pk (succ k))) (pk (succ k)) :=
    lt_congr (.eqRefl _) hq.eqSymm (lt_succ_self (pred (pk (succ k))))
  have lo : Γ ⊢[PRAAx] lt (pc (pred (pk (succ k)))) (succ k) := pk_min below
  have e1 : Γ ⊢[PRAAx] pc (pk (succ k)) ≐ pc (pred (pk (succ k))) + isP (succ (pred (pk (succ k)))) :=
    (congrPc hq).eqTrans (pc_succ _)
  refine .orE (isP_01 (succ (pred (pk (succ k))))) ?_ ?_
  · have e := alg0 e1.wk (Prf.hyp0 (Γ := Γ) (φ := isP (succ (pred (pk (succ k)))) ≐ zero))
    exact le_lt_absurd _ s.wk (lt_congr e (.eqRefl _) lo.wk)
  · have e := alg1 e1.wk (Prf.hyp0 (Γ := Γ) (φ := isP (succ (pred (pk (succ k)))) ≐ one))
    have up : ((isP (succ (pred (pk (succ k)))) ≐ one) :: Γ) ⊢[PRAAx] le (pc (pk (succ k))) (succ k) :=
      le_congr e.eqSymm (.eqRefl _) lo.wk
    exact .andI (le_antisymm up s.wk) (prime_congr hq.wk.eqSymm (prime_of_isP Prf.hyp0))

/-- **Inverse rank**, lower half: `p_{π(x)} ≤ x`. -/
theorem pk_pc_le (x : PTm n) : Γ ⊢[PRAAx] le (pk (pc x)) x := pk_le_of (le_refl _)

/-- **Inverse rank**, upper half: `x < p_{π(x)+1}`. -/
theorem lt_pk_pc (x : PTm n) : Γ ⊢[PRAAx] lt x (pk (succ (pc x))) := by
  refine .orE (lt_or_le x (pk (succ (pc x)))) Prf.hyp0 ?_
  have m := pc_mono (Prf.hyp0 (Γ := Γ) (φ := le (pk (succ (pc x))) x))
  have r := Prf.andE₁ (pk_rank (Γ := le (pk (succ (pc x))) x :: Γ) (pc x))
  have c : (le (pk (succ (pc x))) x :: Γ) ⊢[PRAAx] lt (pc x) (pc x) := le_congr r (.eqRefl _) m
  exact lt_irrefl (pc x) _ c

/-- `p_k < p_{k+1}` for `k ≥ 1`. -/
theorem pk_strict (k : PTm n) : Γ ⊢[PRAAx] lt (pk (succ k)) (pk (succ (succ k))) := by
  refine .orE (lt_or_le (pk (succ k)) (pk (succ (succ k)))) Prf.hyp0 ?_
  have m := pc_mono (Prf.hyp0 (Γ := Γ) (φ := le (pk (succ (succ k))) (pk (succ k))))
  have r1 := Prf.andE₁ (pk_rank (Γ := le (pk (succ (succ k))) (pk (succ k)) :: Γ) k)
  have r2 := Prf.andE₁ (pk_rank (Γ := le (pk (succ (succ k))) (pk (succ k)) :: Γ) (succ k))
  have c : (le (pk (succ (succ k))) (pk (succ k)) :: Γ) ⊢[PRAAx] lt (succ k) (succ k) := le_congr r2 r1 m
  exact lt_irrefl (succ k) _ c

/-- `p_{π(x)} = x` for prime `x`. -/
theorem pk_of_prime {x : PTm n} (hp : Γ ⊢[PRAAx] prime x) : Γ ⊢[PRAAx] pk (pc x) ≐ x := by
  have hx := p_pos (prime_two hp)
  have j : Γ ⊢[PRAAx] pc x ≐ succ (pc (pred x)) := (congrPc hx).eqTrans (pc_prime (prime_congr hx hp))
  refine .orE (lt_or_eq_of_le (pk_pc_le x)) ?_ Prf.hyp0
  have hl : (lt (pk (pc x)) x :: Γ) ⊢[PRAAx] lt (pk (pc x)) x := Prf.hyp0
  have h : (lt (pk (pc x)) x :: Γ) ⊢[PRAAx] le (pk (pc x)) (pred x) :=
    le_of_lt_succ (lt_congr (.eqRefl _) hx.wk hl)
  have m := pc_mono h
  have s := Prf.andE₂ (pk_spec (Γ := lt (pk (pc x)) x :: Γ) (pc x))
  have c : (lt (pk (pc x)) x :: Γ) ⊢[PRAAx] lt (pc (pred x)) (pc (pred x)) :=
    le_congr j.wk (.eqRefl _) (le_trans s m)
  exact lt_irrefl (pc (pred x)) _ c

/-- Every value `p_k`, `k ≥ 1`, is prime. -/
theorem prime_of_pk {x k : PTm n} (h : Γ ⊢[PRAAx] pk (succ k) ≐ x) : Γ ⊢[PRAAx] prime x :=
  prime_congr h (Prf.andE₂ (pk_rank k))

end LeanProofs.IPRA.AnalyticNumberTheory.PrimeRank
