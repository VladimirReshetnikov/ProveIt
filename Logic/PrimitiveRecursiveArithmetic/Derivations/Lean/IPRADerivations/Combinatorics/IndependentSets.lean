import IPRADerivations.Combinatorics.FibonacciSeries
import IPRADerivations.Combinatorics.BellPascalInversion

/-!
# Independent sets of a path and tilings by squares and dominoes

Packet: `combinatorics/fibonacci_lucas_ipra` (theorem "Tilings and independent subsets"): with subsets
encoded by bitmasks `b < 2ⁿ`, the number of subsets of `{0, …, n − 1}` with no two adjacent
elements is

  `C(n) = ∑_{b < 2ⁿ} ok(n, b) = F_{n+2}`,

so the tilings of a row of length `n + 1` by squares and dominoes (a tiling is the set of positions
where its dominoes start, a subset of `{0, …, n − 1}` with no two adjacent) number
`T(n + 1) = F_{n+2}`.

* `ok(n, b)` scans the `n` low bits of `b` by primitive recursion on the state `⟨b ≫ i, flag⟩`,
  clearing the flag at an adjacent pair `bit₀ = bit₁ = 1`; `ok_succ`: `ok(n + 1, b) =
  [¬(bit₀ b ∧ bit₁ b)] · ok(n, ⌊b/2⌋)` (the first step moved to the front, `st_front`);
* `sum_pairs`: `∑_{b < 2M} f(b) = ∑_{c < M} (f(2c) + f(2c + 1))`;
* `C_rec`: splitting by the lowest bit, `ok(n + 2, 2c) = ok(n + 1, c)` and
  `ok(n + 2, 2c + 1) = [c even] ok(n + 1, c)`, and splitting again, `C(n + 2) = C(n + 1) + C(n)`;
* `independent_sets`: `C(0) = 1`, `C(1) = 2`, hence `C(n) = F_{n+2}`.

The cycle count `L_n` is not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.IndependentSets

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Fibonacci
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (ev ev_zero)
open LeanProofs.IPRA.DiophantineNumberTheory.Pythagoras (two_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.FermatQuartic (congrPair)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem inst2_sub (d a b : PTm 2) (i z : PTm n) :
    inst2 (Syn.subst ![a, b] d) i z = inst2 d (inst2 a i z) (inst2 b i z) := by
  simp only [inst2, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

/-! ## Halving -/

theorem half_double (c : PTm n) : Γ ⊢[PRAAx] half (two * c) ≐ c := by
  refine mul_cancel two_pos ?_
  have a := natEq (half_par (Γ := Γ) (two * c)); have b := natEq (par_double (Γ := Γ) c)
  apply deriveNat; ipra_simps; linear_combination -a - b

theorem half_double_succ (c : PTm n) : Γ ⊢[PRAAx] half (two * c + one) ≐ c := by
  refine mul_cancel two_pos ?_
  have a := natEq (half_par (Γ := Γ) (two * c + one)); have b := natEq (par_double_succ (Γ := Γ) c)
  apply deriveNat; ipra_simps; linear_combination -a - b

/-! ## The scan -/

/-- `[¬(bit₀ b ∧ bit₁ b)]`. -/
abbrev okp {n : ℕ} (b : PTm n) : PTm n := monus one (par b * par (half b))

/-- The state `⟨b ≫ i, flag⟩`; over `0 = i`, `1 = state`, `2 = b`. -/
abbrev stStep : PTm 3 := pairT (half (fstT (var 1))) (sndT (var 1) * okp (fstT (var 1)))
abbrev stBase : PTm 1 := pairT (var 0) one
abbrev stF : PR 2 := rec2 stBase stStep

abbrev st {n : ℕ} (N b : PTm n) : PTm n := ap2 stF N b
/-- `ok(N, b)`: no two adjacent ones among the low bits of `b`. -/
abbrev ok {n : ℕ} (N b : PTm n) : PTm n := sndT (st N b)

theorem st_zero (b : PTm n) : Γ ⊢[PRAAx] st zero b ≐ pairT b one := by
  simpa using rec2_zero (Γ := Γ) stBase stStep b

theorem st_succ (N b : PTm n) :
    Γ ⊢[PRAAx] st (succ N) b ≐ pairT (half (fstT (st N b))) (sndT (st N b) * okp (fstT (st N b))) := by
  simpa using rec2_succ (Γ := Γ) stBase stStep N b

theorem front_step {N b : PTm n} (ih : Γ ⊢[PRAAx] st (succ N) b ≐ pairT (fstT (st N (half b))) (okp b * sndT (st N (half b)))) :
    Γ ⊢[PRAAx] st (succ (succ N)) b ≐ pairT (fstT (st (succ N) (half b))) (okp b * sndT (st (succ N) (half b))) := by
  have f := (congrFst ih).eqTrans (fst_pair _ _); have s := (congrSnd ih).eqTrans (snd_pair _ _)
  refine (st_succ _ _).eqTrans (.eqTrans ?_ (congrPair ((congrFst (st_succ _ _)).eqTrans (fst_pair _ _))
    (congrMul (.eqRefl _) ((congrSnd (st_succ _ _)).eqTrans (snd_pair _ _)))).eqSymm)
  refine congrPair (congrAp1 halfF f) ?_
  exact (congrMul s (congrMonus (.eqRefl _) (congrMul (congrAp1 parF f) (congrAp1 parF (congrAp1 halfF f))))).eqTrans
    (mul_assoc _ _ _)

theorem front_base (b : PTm n) :
    Γ ⊢[PRAAx] st (succ zero) b ≐ pairT (fstT (st zero (half b))) (okp b * sndT (st zero (half b))) := by
  have z := st_zero (Γ := Γ) b; have z' := st_zero (Γ := Γ) (half b)
  have f := (congrFst z).eqTrans (fst_pair _ _); have s := (congrSnd z).eqTrans (snd_pair _ _)
  refine (st_succ _ _).eqTrans (congrPair ((congrAp1 halfF f).eqTrans ((congrFst z').eqTrans (fst_pair _ _)).eqSymm) ?_)
  refine (congrMul s (congrMonus (.eqRefl _) (congrMul (congrAp1 parF f) (congrAp1 parF (congrAp1 halfF f))))).eqTrans ?_
  exact (one_mul _).eqTrans (((one_mul _).eqSymm.eqTrans (mul_comm _ _)).eqTrans
    (congrMul (.eqRefl _) ((congrSnd z').eqTrans (snd_pair _ _)).eqSymm))

/-- Variables: `0 = N`, `1 = b`. -/
private abbrev frontF : Fm PTm 2 :=
  st (succ (var 0)) (var 1) ≐ pairT (fstT (st (var 0) (half (var 1)))) (okp (var 1) * sndT (st (var 0) (half (var 1))))

private theorem front₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] frontF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, subst_ap1, subst_pairT, subst_fstT, subst_sndT, PTm.subst_mul, PTm.subst_monus, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact front_base _
  · simp only [Fm.subst_eq, subst_ap2, subst_ap1, subst_pairT, subst_fstT, subst_sndT, PTm.subst_mul, PTm.subst_monus, Syn.subst_var,
      Syn.repl_zero, repl_one, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact front_step Prf.hyp0

theorem st_front (N b : PTm n) :
    Γ ⊢[PRAAx] st (succ N) b ≐ pairT (fstT (st N (half b))) (okp b * sndT (st N (half b))) := by
  have h := inst (Γ := Γ) front₀ (![N, b] : Fin 2 → PTm n)
  simpa using h

/-- `ok(N + 1, b) = [¬(bit₀ ∧ bit₁)] · ok(N, ⌊b/2⌋)`. -/
theorem ok_succ (N b : PTm n) : Γ ⊢[PRAAx] ok (succ N) b ≐ okp b * ok N (half b) :=
  (congrSnd (st_front N b)).eqTrans (snd_pair _ _)

theorem ok_zero (b : PTm n) : Γ ⊢[PRAAx] ok zero b ≐ one := (congrSnd (st_zero b)).eqTrans (snd_pair _ _)

theorem okp_even (c : PTm n) : Γ ⊢[PRAAx] okp (two * c) ≐ one :=
  (congrMonus (.eqRefl _) ((congrMul (par_double c) (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (monus_zero _)

theorem okp_odd (c : PTm n) : Γ ⊢[PRAAx] okp (two * c + one) ≐ ev c :=
  congrMonus (.eqRefl _) ((congrMul (par_double_succ c) (congrAp1 parF (half_double_succ c))).eqTrans (one_mul _))

theorem ok_even (N c : PTm n) : Γ ⊢[PRAAx] ok (succ N) (two * c) ≐ ok N c :=
  (ok_succ _ _).eqTrans ((congrMul (okp_even c) (congrSnd (congrAp2 stF (.eqRefl _) (half_double c)))).eqTrans (one_mul _))

theorem ok_odd (N c : PTm n) : Γ ⊢[PRAAx] ok (succ N) (two * c + one) ≐ ev c * ok N c :=
  (ok_succ _ _).eqTrans (congrMul (okp_odd c) (congrSnd (congrAp2 stF (.eqRefl _) (half_double_succ c))))

/-! ## Splitting a sum by the lowest bit -/

/-- `f(2c) + f(2c + 1)`. -/
abbrev pairB (f : PTm 2) : PTm 2 := Syn.subst ![two * var 0, var 1] f + Syn.subst ![two * var 0 + one, var 1] f

theorem inst2_pair (f : PTm 2) (c x : PTm n) : inst2 (pairB f) c x = inst2 f (two * c) x + inst2 f (two * c + one) x := by
  have : inst2 (pairB f) c x = inst2 (Syn.subst ![two * var 0, var 1] f) c x +
      inst2 (Syn.subst ![two * var 0 + one, var 1] f) c x := by simp [inst2]
  rw [this, inst2_sub, inst2_sub]; simp [inst2]

theorem pairs_step (f : PTm 2) {M x : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (sumF f) (two * M) x ≐ ap2 (sumF (pairB f)) M x) :
    Γ ⊢[PRAAx] ap2 (sumF f) (two * succ M) x ≐ ap2 (sumF (pairB f)) (succ M) x := by
  have e : Γ ⊢[PRAAx] two * succ M ≐ succ (two * M + zero) + zero + one := by ipra_ring
  refine (congrAp2 (sumF f) (two_succ M) (.eqRefl _)).eqTrans ?_
  refine (sum_succ' _ _ _).eqTrans ((congrAdd (sum_succ' _ _ _) (.eqRefl _)).eqTrans ?_)
  refine (add_assoc _ _ _).eqTrans ?_
  refine .eqTrans ?_ (sum_succ' _ _ _).eqSymm
  rw [inst2_pair]
  refine congrAdd ih (congrAdd (.eqRefl _) (congrInst2 f (by ipra_ring) (.eqRefl _)))

/-- Variables: `0 = M`, `1 = x`. -/
private abbrev pairsF (f : PTm 2) : Fm PTm 2 := ap2 (sumF f) (two * var 0) (var 1) ≐ ap2 (sumF (pairB f)) (var 0) (var 1)

private theorem pairs₀ (f : PTm 2) : ([] : List (Fm PTm 2)) ⊢[PRAAx] pairsF f := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact (congrAp2 (sumF f) (mul_zero _) (.eqRefl _)).eqTrans ((sum_zero _ _).eqTrans (sum_zero _ _).eqSymm)
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_mul, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact pairs_step f Prf.hyp0

/-- `∑_{b < 2M} f(b) = ∑_{c < M} (f(2c) + f(2c + 1))`. -/
theorem sum_pairs (f : PTm 2) (M x : PTm n) : Γ ⊢[PRAAx] ap2 (sumF f) (two * M) x ≐ ap2 (sumF (pairB f)) M x := by
  have h := inst (Γ := Γ) (pairs₀ f) (![M, x] : Fin 2 → PTm n)
  simpa using h

/-! ## The count -/

/-- `ok(N, b)`, over `0 = b`, `1 = N`. -/
abbrev okB : PTm 2 := ok (var 1) (var 0)
/-- `[b even] ok(N, b)`. -/
abbrev eB : PTm 2 := ev (var 0) * ok (var 1) (var 0)

theorem inst2_ok (b N : PTm n) : inst2 okB b N = ok N b := by simp [inst2]
theorem inst2_e (b N : PTm n) : inst2 eB b N = ev b * ok N b := by simp [inst2]

/-- `C(N) = ∑_{b < 2^N} ok(N, b)`. -/
abbrev C {n : ℕ} (N : PTm n) : PTm n := ap2 (sumF okB) (pw two N) N

theorem pw_two_succ (N : PTm n) : Γ ⊢[PRAAx] pw two (succ N) ≐ two * pw two N := (pw_succ _ _).eqTrans (mul_comm _ _)

/-- `C(N + 2) = C(N + 1) + C(N)`. -/
theorem C_rec (N : PTm n) : Γ ⊢[PRAAx] C (succ (succ N)) ≐ C (succ N) + C N := by
  have h₁ : Γ ⊢[PRAAx] C (succ (succ N)) ≐ ap2 (sumF (addBody okB eB)) (pw two (succ N)) (succ N) := by
    refine (congrAp2 (sumF okB) (pw_two_succ _) (.eqRefl _)).eqTrans ((sum_pairs _ _ _).eqTrans ?_)
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_pair, inst2_addBody, inst2_ok, inst2_ok, inst2_ok, inst2_e]
    have e : Syn.shift (succ (succ N)) = succ (succ (Syn.shift N)) := by simp [Syn.shift]
    have e' : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
    rw [e, e']
    exact congrAdd (ok_even _ _) (ok_odd _ _)
  have h₂ : Γ ⊢[PRAAx] ap2 (sumF eB) (pw two (succ N)) (succ N) ≐ C N := by
    refine (congrAp2 (sumF eB) (pw_two_succ _) (.eqRefl _)).eqTrans ((sum_pairs _ _ _).eqTrans ?_)
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_pair, inst2_e, inst2_e, inst2_ok]
    have e' : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
    rw [e']
    have z : Γ.map Fm.shift ⊢[PRAAx] ev (two * var 0 + one) ≐ zero :=
      (congrMonus (.eqRefl _) (par_double_succ _)).eqTrans (monus_self _)
    have o : Γ.map Fm.shift ⊢[PRAAx] ev (two * var 0) ≐ one :=
      (congrMonus (.eqRefl _) (par_double _)).eqTrans (monus_zero _)
    refine (congrAdd ((congrMul o.wk (.eqRefl _)).eqTrans (one_mul _)) ((congrMul z.wk (.eqRefl _)).eqTrans (zero_mul _))).eqTrans ?_
    exact (add_zero _).eqTrans (ok_even _ _)
  exact h₁.eqTrans ((sum_add _ _ _ _).eqTrans (congrAdd (.eqRefl _) h₂))

theorem C_zero : Γ ⊢[PRAAx] C (zero : PTm n) ≐ one := by
  refine (congrAp2 (sumF okB) (pw_zero two) (.eqRefl _)).eqTrans ((sum_succ' _ _ _).eqTrans ?_)
  rw [inst2_ok]
  exact (congrAdd (sum_zero _ _) (ok_zero _)).eqTrans (zero_add _)

theorem C_one : Γ ⊢[PRAAx] C (succ (zero : PTm n)) ≐ two := by
  have e : Γ ⊢[PRAAx] pw two (succ (zero : PTm n)) ≐ two * succ zero := (pw_two_succ _).eqTrans (congrMul (.eqRefl _) (pw_zero _))
  refine (congrAp2 (sumF okB) e (.eqRefl _)).eqTrans ((sum_pairs _ _ _).eqTrans ?_)
  refine (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) ?_).eqTrans (zero_add _))
  rw [inst2_pair, inst2_ok, inst2_ok]
  have a := natEq ((ok_even (Γ := Γ) zero zero).eqTrans (ok_zero _))
  have b := natEq ((ok_odd (Γ := Γ) zero zero).eqTrans ((congrMul ev_zero (ok_zero _)).eqTrans (one_mul _)))
  apply deriveNat; ipra_simps; linear_combination a + b

/-! ## `C(N) = F_{N+2}` -/

/-- Variable: `0 = N`. -/
private abbrev indF : Fm PTm 1 := pairT (C (var 0)) (C (succ (var 0))) ≐ pairT (fibS (succ (var 0))) (fibS (succ (succ (var 0))))

theorem ind_base : Γ ⊢[PRAAx] pairT (C (zero : PTm n)) (C (succ zero)) ≐ pairT (fibS (succ zero)) (fibS (succ (succ zero))) := by
  have a := natEq (fibS_succ (Γ := Γ) (zero : PTm n)); have b := natEq (fibS_succ (Γ := Γ) (succ (zero : PTm n)))
  have c := natEq (fibS_zero (Γ := Γ) (n := n)); have d := natEq (fib_zero (Γ := Γ) (n := n))
  have e := natEq (fib_succ (Γ := Γ) (zero : PTm n))
  have f := natEq (C_zero (Γ := Γ) (n := n)); have g := natEq (C_one (Γ := Γ) (n := n))
  refine congrPair ?_ ?_
  · apply deriveNat; ipra_simps; linear_combination f - a - c - d
  · apply deriveNat; ipra_simps; linear_combination g - b - a - c - d - e - c

theorem ind_step {N : PTm n} (ih : Γ ⊢[PRAAx] pairT (C N) (C (succ N)) ≐ pairT (fibS (succ N)) (fibS (succ (succ N)))) :
    Γ ⊢[PRAAx] pairT (C (succ N)) (C (succ (succ N))) ≐ pairT (fibS (succ (succ N))) (fibS (succ (succ (succ N)))) := by
  have i₁ := (fst_pair _ _).eqSymm.eqTrans ((congrFst ih).eqTrans (fst_pair _ _))
  have i₂ := (snd_pair _ _).eqSymm.eqTrans ((congrSnd ih).eqTrans (snd_pair _ _))
  refine congrPair i₂ ((C_rec N).eqTrans ((congrAdd i₂ i₁).eqTrans ?_))
  exact ((congrAdd (.eqRefl _) (fib_succ _).eqSymm).eqTrans (fibS_succ _).eqSymm)

private theorem ind₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] indF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, subst_fibS, Syn.subst_var, Syn.inst_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact ind_base
  · simp only [Fm.subst_eq, subst_ap2, subst_pairT, subst_fibS, Syn.subst_var, Syn.repl_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact ind_step Prf.hyp0

/-- The number of subsets of `{0, …, N − 1}` with no two adjacent elements is `F_{N+2}`; equivalently
the tilings of a row of length `N + 1` by squares and dominoes number `F_{N+2}`. -/
theorem independent_sets (N : PTm n) : Γ ⊢[PRAAx] C N ≐ fibS (succ N) := by
  have h := inst (Γ := Γ) ind₀ (![N] : Fin 1 → PTm n)
  have h' : Γ ⊢[PRAAx] pairT (C N) (C (succ N)) ≐ pairT (fibS (succ N)) (fibS (succ (succ N))) := by simpa using h
  exact (fst_pair _ _).eqSymm.eqTrans ((congrFst h').eqTrans (fst_pair _ _))

end LeanProofs.IPRA.Combinatorics.IndependentSets
