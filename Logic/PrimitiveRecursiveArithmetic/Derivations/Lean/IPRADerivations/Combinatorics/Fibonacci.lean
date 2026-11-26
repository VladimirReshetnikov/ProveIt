import IPRADerivations.DiophantineNumberTheory.Recurrences
import IPRADerivations.DiophantineNumberTheory.Coprime

/-!
# Fibonacci and Lucas numbers

Packet: `combinatorics/fibonacci_lucas_ipra`. With `fib n = F_n` and `fibS n = F_{n+1}` (the pair of
`Recurrences`, by simultaneous recursion) and `luc n = L_n = 2F_{n+1} − F_n`, all in natural numbers:

* recurrence: `F_{n+2} = F_{n+1} + F_n`, `F_n ≤ F_{n+1}`;
* `lem:add`: `F_{m+k+1} = F_{m+1}F_{k+1} + F_mF_k`, and the symmetric form
  `F_{m+k} + F_mF_k = F_mF_{k+1} + F_{m+1}F_k`;
* doubling: `F_{2n+1} = F_{n+1}² + F_n²`, `F_{2n} + F_n² = 2F_nF_{n+1}`, `F_{2n} = F_nL_n`;
* Cassini: `F_{n+2}F_n + [n even] = F_{n+1}² + [n odd]`, i.e. `F_{n+2}F_n − F_{n+1}² = (−1)^{n+1}`;
* finite sums: `∑_{k<N} F_k + 1 = F_{N+1}`, `∑_{k≤N} F_k² = F_NF_{N+1}`, `∑_{k<N} F_{2k+1} = F_{2N}`,
  `∑_{k≤N} F_{2k} + 1 = F_{2N+1}`, `∑_{k<N} L_k + 1 = L_{N+1}`;
* Lucas: `L_{n+1} = F_{n+2} + F_n`, `L_{n+2} = L_{n+1} + L_n`, and
  `L_n² + 4[n odd] = 5F_n² + 4[n even]`, i.e. `L_n² − 5F_n² = 4(−1)^n`.

The sign `(−1)^n` is carried by the parity function `par n ∈ {0, 1}` of `Core/Parity`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.Fibonacci

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.Recurrences (fibStep)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The pair `(F_{n+1}, F_n)` -/

/-- `F_{m+1}`. -/
def fibS (m : PTm n) : PTm n := DiophantineNumberTheory.Recurrences.Fs m
/-- `F_m`. -/
def fib (m : PTm n) : PTm n := DiophantineNumberTheory.Recurrences.F m

@[simp] theorem subst_fibS {k : ℕ} (σ : Fin n → PTm k) (m : PTm n) :
    Syn.subst σ (fibS m) = fibS (Syn.subst σ m) := by
  simp only [fibS, DiophantineNumberTheory.Recurrences.Fs, subst_sim₁]
  congr 1; funext i; simp

@[simp] theorem subst_fib {k : ℕ} (σ : Fin n → PTm k) (m : PTm n) :
    Syn.subst σ (fib m) = fib (Syn.subst σ m) := by
  simp only [fib, DiophantineNumberTheory.Recurrences.F, subst_sim₂]
  congr 1; funext i; simp

theorem congrFibS {m m' : PTm n} (h : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] fibS m ≐ fibS m' := by
  unfold fibS DiophantineNumberTheory.Recurrences.Fs sim₁
  exact congrFst (congrApp _ fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h
    · exact .eqRefl _)

theorem congrFib {m m' : PTm n} (h : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] fib m ≐ fib m' := by
  unfold fib DiophantineNumberTheory.Recurrences.F sim₂
  exact congrSnd (congrApp _ fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h
    · exact .eqRefl _)

theorem fibS_zero : Γ ⊢[PRAAx] fibS (zero : PTm n) ≐ one := by
  have h := sim₁_zero (Γ := Γ) one zero fibStep (var 1) (fun _ : Fin 1 => (zero : PTm n))
  unfold fibS; simpa using h

theorem fib_zero : Γ ⊢[PRAAx] fib (zero : PTm n) ≐ zero := by
  have h := sim₂_zero (Γ := Γ) one zero fibStep (var 1) (fun _ : Fin 1 => (zero : PTm n))
  unfold fib; simpa using h

/-- `F_{m+2} = F_{m+1} + F_m`. -/
theorem fibS_succ (m : PTm n) : Γ ⊢[PRAAx] fibS (succ m) ≐ fibS m + fib m := by
  have h := sim₁_succ (Γ := Γ) one zero fibStep (var 1) (fun _ : Fin 1 => (zero : PTm n)) m
  unfold fibS fib; simpa using h

theorem fib_succ (m : PTm n) : Γ ⊢[PRAAx] fib (succ m) ≐ fibS m := by
  have h := sim₂_succ (Γ := Γ) one zero fibStep (var 1) (fun _ : Fin 1 => (zero : PTm n)) m
  unfold fibS fib; simpa using h

/-- `F_m ≤ F_{m+1}`. -/
theorem fib_le (m : PTm n) : Γ ⊢[PRAAx] le (fib m) (fibS m) :=
  .orE (zero_or_succ m)
    (le_congr ((congrFib Prf.hyp0).eqTrans fib_zero).eqSymm (.eqRefl _) (zero_monus _))
    (le_of_eq_add (d := fib (pred m))
      ((congrFibS Prf.hyp0).eqTrans ((fibS_succ _).eqTrans
        (congrAdd ((fib_succ _).eqSymm.eqTrans (congrFib Prf.hyp0).eqSymm) (.eqRefl _)))))

/-! ## The addition law -/

theorem add_step {m k : PTm n}
    (h₁ : Γ ⊢[PRAAx] fibS (m + k) ≐ fibS m * fibS k + fib m * fib k)
    (h₂ : Γ ⊢[PRAAx] fibS (m + succ k) ≐ fibS m * fibS (succ k) + fib m * fibS k) :
    Γ ⊢[PRAAx] fibS (m + succ (succ k)) ≐ fibS m * fibS (succ (succ k)) + fib m * fibS (succ k) := by
  ipra_lc natEq h₁ + natEq h₂ + natEq ((congrFibS (Γ := Γ) (add_succ m (succ k))).eqTrans (fibS_succ (m + succ k))) +
    natEq ((congrFib (Γ := Γ) (add_succ m k)).eqTrans (fib_succ (m + k))) -
    Groth.ι (IPRA.Q.mk Γ (fibS m)) * natEq (fibS_succ (Γ := Γ) (succ k)) -
    Groth.ι (IPRA.Q.mk Γ (fibS m)) * natEq (fib_succ (Γ := Γ) k) -
    Groth.ι (IPRA.Q.mk Γ (fib m)) * natEq (fibS_succ (Γ := Γ) k)

/-- Variables: `0 = k`, `1 = m`. -/
private abbrev addF : Fm PTm 2 :=
  (fibS (var 1 + var 0) ≐ fibS (var 1) * fibS (var 0) + fib (var 1) * fib (var 0)) ⋏
    (fibS (var 1 + succ (var 0)) ≐ fibS (var 1) * fibS (succ (var 0)) + fib (var 1) * fibS (var 0))

private theorem add₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] addF := by
  ipra_ind (⟨trivial, trivial⟩) [subst_fibS, subst_fib]
  · have z₁ := natEq (fibS_zero (Γ := ([] : List (Fm PTm 1)))); have z₂ := natEq (fib_zero (Γ := ([] : List (Fm PTm 1))))
    refine .andI ((congrFibS (add_zero _)).eqTrans ?_) ?_
    · ipra_lc -Groth.ι (IPRA.Q.mk _ (fibS (var 0))) * z₁ - Groth.ι (IPRA.Q.mk _ (fib (var 0))) * z₂
    · refine (congrFibS ((add_succ _ _).eqTrans (congrSucc (add_zero _)))).eqTrans ((fibS_succ _).eqTrans ?_)
      ipra_lc -Groth.ι (IPRA.Q.mk _ (fibS (var 0))) * natEq (fibS_succ (Γ := ([] : List (Fm PTm 1))) zero) -
        Groth.ι (IPRA.Q.mk _ (fibS (var 0))) * z₁ - Groth.ι (IPRA.Q.mk _ (fibS (var 0))) * z₂ -
        Groth.ι (IPRA.Q.mk _ (fib (var 0))) * z₁
  · exact .andI ((Prf.andE₂ Prf.hyp0).eqTrans (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (fib_succ _).eqSymm)))
      (add_step (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0))

/-- `F_{m+k+1} = F_{m+1}F_{k+1} + F_mF_k`. -/
theorem fibS_add (m k : PTm n) : Γ ⊢[PRAAx] fibS (m + k) ≐ fibS m * fibS k + fib m * fib k := by
  have h := inst (Γ := Γ) add₀ (![k, m] : Fin 2 → PTm n)
  simp at h
  exact Prf.andE₁ h

/-- `lem:add`: `F_{m+(k+1)} = F_{m+1}F_{k+1} + F_mF_k`. -/
theorem fib_add (m k : PTm n) : Γ ⊢[PRAAx] fib (m + succ k) ≐ fibS m * fibS k + fib m * fib k :=
  (congrFib (add_succ m k)).eqTrans ((fib_succ _).eqTrans (fibS_add m k))

theorem add_sym_zero {m k : PTm n} (h : Γ ⊢[PRAAx] k ≐ zero) :
    Γ ⊢[PRAAx] fib (m + k) + fib m * fib k ≐ fib m * fibS k + fibS m * fib k := by
  ipra_lc natEq (congrFib (Γ := Γ) ((congrAdd (.eqRefl m) h).eqTrans (add_zero m))) +
    (Groth.ι (IPRA.Q.mk Γ (fib m)) - Groth.ι (IPRA.Q.mk Γ (fibS m))) * natEq ((congrFib h).eqTrans fib_zero) -
    Groth.ι (IPRA.Q.mk Γ (fib m)) * natEq ((congrFibS h).eqTrans fibS_zero)

theorem add_sym_succ {m k : PTm n} (h : Γ ⊢[PRAAx] k ≐ succ (pred k)) :
    Γ ⊢[PRAAx] fib (m + k) + fib m * fib k ≐ fib m * fibS k + fibS m * fib k := by
  ipra_lc natEq ((congrFib (congrAdd (.eqRefl m) h)).eqTrans (fib_add m (pred k))) +
    (Groth.ι (IPRA.Q.mk Γ (fib m)) - Groth.ι (IPRA.Q.mk Γ (fibS m))) * natEq ((congrFib h).eqTrans (fib_succ (pred k))) -
    Groth.ι (IPRA.Q.mk Γ (fib m)) * natEq ((congrFibS h).eqTrans (fibS_succ (pred k)))

/-- `F_{m+k} + F_mF_k = F_mF_{k+1} + F_{m+1}F_k`, i.e. `F_{m+k} = F_mF_{k+1} + F_{m−1}F_k`. -/
theorem fib_add_sym (m k : PTm n) :
    Γ ⊢[PRAAx] fib (m + k) + fib m * fib k ≐ fib m * fibS k + fibS m * fib k :=
  .orE (zero_or_succ k) (add_sym_zero Prf.hyp0) (add_sym_succ Prf.hyp0)

/-- `F_{2k+1} = F_{k+1}² + F_k²`. -/
theorem fibS_double (k : PTm n) : Γ ⊢[PRAAx] fibS (k + k) ≐ fibS k * fibS k + fib k * fib k := fibS_add k k

/-- `F_{2k} + F_k² = 2F_kF_{k+1}`. -/
theorem fib_double (k : PTm n) : Γ ⊢[PRAAx] fib (k + k) + fib k * fib k ≐ two * (fib k * fibS k) := by
  ipra_lc natEq (fib_add_sym (Γ := Γ) k k)

/-! ## Cassini's identity -/

open LeanProofs.IPRA (par par_succ par_cases)

theorem compl_compl (k : PTm n) : Γ ⊢[PRAAx] monus one (monus one (par k)) ≐ par k :=
  .orE (par_cases k)
    ((congrMonus (.eqRefl _) ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans (monus_zero _))).eqTrans
      ((succ_monus_succ _ _).eqTrans ((monus_zero _).eqTrans Prf.hyp0.eqSymm)))
    ((congrMonus (.eqRefl _) ((congrMonus (.eqRefl _) Prf.hyp0).eqTrans
      ((succ_monus_succ _ _).eqTrans (monus_zero _)))).eqTrans ((monus_zero _).eqTrans Prf.hyp0.eqSymm))

theorem cas_step {k : PTm n}
    (ih : Γ ⊢[PRAAx] fibS (succ k) * fib k + monus one (par k) ≐ fibS k * fibS k + par k) :
    Γ ⊢[PRAAx] fibS (succ (succ k)) * fib (succ k) + monus one (par (succ k)) ≐
      fibS (succ k) * fibS (succ k) + par (succ k) := by
  ipra_lc -natEq ih - Groth.ι (IPRA.Q.mk Γ (fibS (succ k))) * natEq (fibS_succ (Γ := Γ) k) +
    natEq ((congrMonus (.eqRefl one) (par_succ (Γ := Γ) k)).eqTrans (compl_compl k)) - natEq (par_succ (Γ := Γ) k) +
    Groth.ι (IPRA.Q.mk Γ (fibS (succ k))) * natEq (fib_succ (Γ := Γ) k) +
    (Groth.ι (IPRA.Q.mk Γ (fib (succ k))) + Groth.ι (IPRA.Q.mk Γ (fibS k))) * natEq (fib_succ (Γ := Γ) k) +
    Groth.ι (IPRA.Q.mk Γ (fib (succ k))) * natEq (fibS_succ (Γ := Γ) (succ k))

private abbrev casF : Fm PTm 1 :=
  fibS (succ (var 0)) * fib (var 0) + monus one (par (var 0)) ≐ fibS (var 0) * fibS (var 0) + par (var 0)

private theorem cas₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] casF := by
  refine ind _ trivial ?_ ?_
  · ipra_lc [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_fibS, subst_fib, subst_ap1, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] Groth.ι (IPRA.Q.mk _ (fibS (succ zero))) * natEq (fib_zero (Γ := ([] : List (Fm PTm 0)))) +
      natEq ((congrMonus (.eqRefl one) (par_zero (Γ := ([] : List (Fm PTm 0))))).eqTrans (monus_zero _)) -
      (Groth.ι (IPRA.Q.mk _ (fibS zero)) + 1) * natEq (fibS_zero (Γ := ([] : List (Fm PTm 0)))) -
      natEq (par_zero (Γ := ([] : List (Fm PTm 0))))
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_fibS, subst_fib, subst_ap1,
      Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact cas_step Prf.hyp0

/-- Cassini: `F_{k+2}F_k + [k even] = F_{k+1}² + [k odd]`. -/
theorem cassini (k : PTm n) :
    Γ ⊢[PRAAx] fibS (succ k) * fib k + monus one (par k) ≐ fibS k * fibS k + par k := by
  have h := inst (Γ := Γ) cas₀ (![k] : Fin 1 → PTm n)
  simpa using h

/-! ## Finite sums -/

abbrev fB : PTm 2 := fib (var 0)
abbrev fsqB : PTm 2 := fib (var 0) * fib (var 0)
/-- `F_{2k+1}`. -/
abbrev foB : PTm 2 := fibS (two * var 0)
/-- `F_{2k}`. -/
abbrev feB : PTm 2 := fib (two * var 0)

theorem inst2_f (k x : PTm n) : inst2 fB k x = fib k := by simp [inst2]
theorem inst2_fsq (k x : PTm n) : inst2 fsqB k x = fib k * fib k := by simp [inst2]
theorem inst2_fo (k x : PTm n) : inst2 foB k x = fibS (two * k) := by simp [inst2]
theorem inst2_fe (k x : PTm n) : inst2 feB k x = fib (two * k) := by simp [inst2]

alias two_succ := Common.two_mul_succ

/-- `F_{2(N+1)} = F_{2N+1} + F_{2N}`. -/
theorem fib_two_succ (N : PTm n) : Γ ⊢[PRAAx] fib (two * succ N) ≐ fibS (two * N) + fib (two * N) :=
  (congrFib (two_succ N)).eqTrans ((fib_succ _).eqTrans (fibS_succ _))

/-- `F_{2(N+1)+1} = (F_{2N+1} + F_{2N}) + F_{2N+1}`. -/
theorem fibS_two_succ (N : PTm n) :
    Γ ⊢[PRAAx] fibS (two * succ N) ≐ fibS (two * N) + fib (two * N) + fibS (two * N) :=
  (congrFibS (two_succ N)).eqTrans ((fibS_succ _).eqTrans (congrAdd (fibS_succ _) (fib_succ _)))

theorem sum_fib_step {N : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF fB) N zero + one ≐ fibS N) :
    Γ ⊢[PRAAx] ap2 (sumF fB) (succ N) zero + one ≐ fibS (succ N) := by
  have e₁ := sum_succ' (Γ := Γ) fB N zero
  rw [inst2_f] at e₁
  ipra_lc natEq e₁ + natEq ih - natEq (fibS_succ (Γ := Γ) N)

theorem sum_sq_step {N : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF fsqB) (succ N) zero ≐ fib N * fibS N) :
    Γ ⊢[PRAAx] ap2 (sumF fsqB) (succ (succ N)) zero ≐ fib (succ N) * fibS (succ N) := by
  have e₁ := sum_succ' (Γ := Γ) fsqB (succ N) zero
  rw [inst2_fsq] at e₁
  ipra_lc natEq e₁ + natEq ih +
    (Groth.ι (IPRA.Q.mk Γ (fib (succ N))) - Groth.ι (IPRA.Q.mk Γ (fib N))) * natEq (fib_succ (Γ := Γ) N) -
    Groth.ι (IPRA.Q.mk Γ (fib (succ N))) * natEq (fibS_succ (Γ := Γ) N)

theorem sum_odd_step {N : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF foB) N zero ≐ fib (two * N)) :
    Γ ⊢[PRAAx] ap2 (sumF foB) (succ N) zero ≐ fib (two * succ N) := by
  have e₁ := sum_succ' (Γ := Γ) foB N zero
  rw [inst2_fo] at e₁
  ipra_lc natEq e₁ + natEq ih - natEq (fib_two_succ (Γ := Γ) N)

theorem sum_even_step {N : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF feB) (succ N) zero + one ≐ fibS (two * N)) :
    Γ ⊢[PRAAx] ap2 (sumF feB) (succ (succ N)) zero + one ≐ fibS (two * succ N) := by
  have e₁ := sum_succ' (Γ := Γ) feB (succ N) zero
  rw [inst2_fe] at e₁
  ipra_lc natEq e₁ + natEq ih + natEq (fib_two_succ (Γ := Γ) N) - natEq (fibS_two_succ (Γ := Γ) N)

/-- Variable `0 = N`: the four sum identities. -/
private abbrev sumsF : Fm PTm 1 :=
  (ap2 (sumF fB) (var 0) zero + one ≐ fibS (var 0)) ⋏
    ((ap2 (sumF fsqB) (succ (var 0)) zero ≐ fib (var 0) * fibS (var 0)) ⋏
      ((ap2 (sumF foB) (var 0) zero ≐ fib (two * var 0)) ⋏
        (ap2 (sumF feB) (succ (var 0)) zero + one ≐ fibS (two * var 0))))

private theorem sums₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] sumsF := by
  ipra_ind (⟨trivial, trivial, trivial, trivial⟩) [subst_ap2, subst_fibS, subst_fib]
  · have z₁ := natEq (fibS_zero (Γ := ([] : List (Fm PTm 0)))); have z₂ := natEq (fib_zero (Γ := ([] : List (Fm PTm 0))))
    have t₀ : ([] : List (Fm PTm 0)) ⊢[PRAAx] (two * zero : PTm 0) ≐ zero := mul_zero _
    have w₁ := natEq ((congrFib t₀).eqTrans (fib_zero (Γ := ([] : List (Fm PTm 0)))))
    have w₂ := natEq ((congrFibS t₀).eqTrans (fibS_zero (Γ := ([] : List (Fm PTm 0)))))
    refine .andI ?_ (.andI ?_ (.andI ?_ ?_))
    · have s := natEq (sum_zero (Γ := ([] : List (Fm PTm 0))) fB zero)
      apply deriveNat; ipra_simps
      linear_combination s - z₁
    · have e := sum_succ' (Γ := ([] : List (Fm PTm 0))) fsqB zero zero
      rw [inst2_fsq] at e
      have a := natEq e; have s := natEq (sum_zero (Γ := ([] : List (Fm PTm 0))) fsqB zero)
      apply deriveNat; ipra_simps
      linear_combination a + s + (Groth.ι (IPRA.Q.mk _ (fib zero)) - Groth.ι (IPRA.Q.mk _ (fibS zero))) * z₂
    · have s := natEq (sum_zero (Γ := ([] : List (Fm PTm 0))) foB zero)
      apply deriveNat; ipra_simps
      linear_combination s - w₁
    · have e := sum_succ' (Γ := ([] : List (Fm PTm 0))) feB zero zero
      rw [inst2_fe] at e
      have a := natEq e; have s := natEq (sum_zero (Γ := ([] : List (Fm PTm 0))) feB zero)
      apply deriveNat; ipra_simps
      linear_combination a + s + w₁ - w₂
  · exact .andI (sum_fib_step (Prf.andE₁ Prf.hyp0))
      (.andI (sum_sq_step (Prf.andE₁ (Prf.andE₂ Prf.hyp0)))
        (.andI (sum_odd_step (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ Prf.hyp0))))
          (sum_even_step (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ Prf.hyp0))))))

/-- `∑_{k<N} F_k + 1 = F_{N+1}`, `∑_{k≤N} F_k² = F_NF_{N+1}`, `∑_{k<N} F_{2k+1} = F_{2N}` and
`∑_{k≤N} F_{2k} + 1 = F_{2N+1}`. -/
theorem fib_sums (N : PTm n) :
    Γ ⊢[PRAAx] (ap2 (sumF fB) N zero + one ≐ fibS N) ⋏
      ((ap2 (sumF fsqB) (succ N) zero ≐ fib N * fibS N) ⋏
        ((ap2 (sumF foB) N zero ≐ fib (two * N)) ⋏ (ap2 (sumF feB) (succ N) zero + one ≐ fibS (two * N)))) := by
  have h := inst (Γ := Γ) sums₀ (![N] : Fin 1 → PTm n)
  simpa using h

/-! ## Lucas numbers -/

/-- `L_m = F_{m+1} + (F_{m+1} − F_m)`. -/
abbrev luc (m : PTm n) : PTm n := fibS m + monus (fibS m) (fib m)

/-- `L_m + F_m = 2F_{m+1}`. -/
theorem luc_eq (m : PTm n) : Γ ⊢[PRAAx] luc m + fib m ≐ two * fibS m := by
  ipra_lc -natEq (eq_add_of_le (fib_le (Γ := Γ) m))

/-- `L_{m+1} = F_{m+2} + F_m`. -/
theorem luc_succ (m : PTm n) : Γ ⊢[PRAAx] luc (succ m) ≐ fibS (succ m) + fib m := by
  ipra_lc natEq (luc_eq (Γ := Γ) (succ m)) - natEq (fib_succ (Γ := Γ) m) + natEq (fibS_succ (Γ := Γ) m)

/-- `L_{m+2} = L_{m+1} + L_m`. -/
theorem luc_rec (m : PTm n) : Γ ⊢[PRAAx] luc (succ (succ m)) ≐ luc (succ m) + luc m := by
  ipra_lc natEq (luc_eq (Γ := Γ) (succ (succ m))) - natEq (luc_eq (Γ := Γ) (succ m)) - natEq (luc_eq (Γ := Γ) m) +
    2 * natEq (fibS_succ (Γ := Γ) (succ m)) - natEq (fib_succ (Γ := Γ) (succ m)) - natEq (fibS_succ (Γ := Γ) m) +
    3 * natEq (fib_succ (Γ := Γ) m)

/-- `F_{2k} = F_kL_k`. -/
theorem fib_double_luc (k : PTm n) : Γ ⊢[PRAAx] fib (k + k) ≐ fib k * luc k := by
  ipra_lc natEq (fib_double (Γ := Γ) k) - Groth.ι (IPRA.Q.mk Γ (fib k)) * natEq (luc_eq (Γ := Γ) k)

/-- `L_k² + 4[k odd] = 5F_k² + 4[k even]`, i.e. `L_k² − 5F_k² = 4(−1)^k`. -/
theorem lucas_norm (k : PTm n) :
    Γ ⊢[PRAAx] luc k * luc k + (two * two) * par k ≐
      (two * two + one) * (fib k * fib k) + (two * two) * monus one (par k) := by
  ipra_lc 4 * (Groth.ι (IPRA.Q.mk Γ (fib k)) * natEq (fibS_succ (Γ := Γ) k) - natEq (cassini (Γ := Γ) k)) +
    (Groth.ι (IPRA.Q.mk Γ (monus (fibS k) (fib k))) + 3 * Groth.ι (IPRA.Q.mk Γ (fibS k)) - Groth.ι (IPRA.Q.mk Γ (fib k))) * natEq (luc_eq (Γ := Γ) k)

abbrev lB : PTm 2 := luc (var 0)

theorem inst2_l (k x : PTm n) : inst2 lB k x = luc k := by simp [inst2]

theorem sum_luc_step {N : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF lB) N zero + one ≐ luc (succ N)) :
    Γ ⊢[PRAAx] ap2 (sumF lB) (succ N) zero + one ≐ luc (succ (succ N)) := by
  have e₁ := sum_succ' (Γ := Γ) lB N zero
  rw [inst2_l] at e₁
  ipra_lc natEq e₁ + natEq ih - natEq (luc_rec (Γ := Γ) N)

private abbrev sumLucF : Fm PTm 1 := ap2 (sumF lB) (var 0) zero + one ≐ luc (succ (var 0))

private theorem sumLuc₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] sumLucF := by
  refine ind _ trivial ?_ ?_
  · ipra_lc [Fm.subst_eq, PTm.subst_add, PTm.subst_monus, subst_ap2, subst_fibS, subst_fib, Syn.subst_var, Syn.inst_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] natEq (sum_zero (Γ := ([] : List (Fm PTm 0))) lB zero) -
      natEq (luc_succ (Γ := ([] : List (Fm PTm 0))) zero) - natEq (fibS_succ (Γ := ([] : List (Fm PTm 0))) zero) -
      natEq (fibS_zero (Γ := ([] : List (Fm PTm 0)))) - 2 * natEq (fib_zero (Γ := ([] : List (Fm PTm 0))))
  · simp only [Fm.subst_eq, PTm.subst_add, PTm.subst_monus, subst_ap2, subst_fibS, subst_fib,
      Syn.subst_var, Syn.repl_zero, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact sum_luc_step Prf.hyp0

/-- `∑_{k<N} L_k + 1 = L_{N+1}`. -/
theorem sum_luc (N : PTm n) : Γ ⊢[PRAAx] ap2 (sumF lB) N zero + one ≐ luc (succ N) := by
  have h := inst (Γ := Γ) sumLuc₀ (![N] : Fin 1 → PTm n)
  simpa using h

/-! ## Closed statements -/

/-- Variables `0 = k`, `1 = m`: the addition law (both forms), doubling, Cassini, the Lucas relations. -/
abbrev fibonacciFormula : Fm PTm 2 :=
  (fib (var 1 + succ (var 0)) ≐ fibS (var 1) * fibS (var 0) + fib (var 1) * fib (var 0)) ⋏
  ((fib (var 1 + var 0) + fib (var 1) * fib (var 0) ≐ fib (var 1) * fibS (var 0) + fibS (var 1) * fib (var 0)) ⋏
  ((fibS (var 0 + var 0) ≐ fibS (var 0) * fibS (var 0) + fib (var 0) * fib (var 0)) ⋏
  ((fib (var 0 + var 0) ≐ fib (var 0) * luc (var 0)) ⋏
  ((fibS (succ (var 0)) * fib (var 0) + monus one (par (var 0)) ≐ fibS (var 0) * fibS (var 0) + par (var 0)) ⋏
  ((luc (succ (succ (var 0))) ≐ luc (succ (var 0)) + luc (var 0)) ⋏
  (luc (var 0) * luc (var 0) + (two * two) * par (var 0) ≐
    (two * two + one) * (fib (var 0) * fib (var 0)) + (two * two) * monus one (par (var 0))))))))

theorem fibonacci_lucas : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 fibonacciFormula :=
  closeUniv 2 (.andI (fib_add _ _) (.andI (fib_add_sym _ _) (.andI (fibS_double _) (.andI (fib_double_luc _)
    (.andI (cassini _) (.andI (luc_rec _) (lucas_norm _)))))))

/-- Variable `0 = N`: the finite sums. -/
abbrev fibSumsFormula : Fm PTm 1 :=
  ((ap2 (sumF fB) (var 0) zero + one ≐ fibS (var 0)) ⋏
    ((ap2 (sumF fsqB) (succ (var 0)) zero ≐ fib (var 0) * fibS (var 0)) ⋏
      ((ap2 (sumF foB) (var 0) zero ≐ fib (two * var 0)) ⋏
        (ap2 (sumF feB) (succ (var 0)) zero + one ≐ fibS (two * var 0))))) ⋏
    (ap2 (sumF lB) (var 0) zero + one ≐ luc (succ (var 0)))

theorem fibonacci_sums : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 fibSumsFormula :=
  closeUniv 1 (.andI (fib_sums _) (sum_luc _))

end LeanProofs.IPRA.Combinatorics.Fibonacci
