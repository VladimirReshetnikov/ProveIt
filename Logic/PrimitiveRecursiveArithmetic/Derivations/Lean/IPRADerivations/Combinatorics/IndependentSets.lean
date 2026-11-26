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

* `ok_ext`: `ok(N + 1, d) = ok(N, d)` for `d < 2^N`, by a violation count over `d < 2^N`;
* `cycle_count`: the subsets of the `n`-cycle with no two adjacent elements (bitmasks `b < 2ⁿ` with
  `ok(n, b)` and not both `bit₀` and `bit_{n−1}`) number `D(n) = C(n − 1) + C(n − 3) = L_n` for
  `n ≥ 3`; the odd `b = 2c + 1` need `c` even and `c < 2^{n−2}`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.IndependentSets

open_ipra
open LeanProofs.IPRA.Combinatorics.Fibonacci
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (ev ev_zero)
open LeanProofs.IPRA.DiophantineNumberTheory.Pythagoras (two_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.FermatQuartic (congrPair)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem inst2_sub (d a b : PTm 2) (i z : PTm n) :
    inst2 (Syn.subst ![a, b] d) i z = inst2 d (inst2 a i z) (inst2 b i z) := by
  simp only [inst2, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

/-! ## Halving -/

theorem half_double (c : PTm n) : Γ ⊢[PRAAx] half (two * c) ≐ c := by
  refine mul_cancel two_pos ?_
  ipra_lc -natEq (half_par (Γ := Γ) (two * c)) - natEq (par_double (Γ := Γ) c)

theorem half_double_succ (c : PTm n) : Γ ⊢[PRAAx] half (two * c + one) ≐ c := by
  refine mul_cancel two_pos ?_
  ipra_lc -natEq (half_par (Γ := Γ) (two * c + one)) - natEq (par_double_succ (Γ := Γ) c)

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
  have f := ih.fstE; have s := ih.sndE
  refine (st_succ _ _).eqTrans (.eqTrans ?_ (congrPair (st_succ _ _).fstE
    (congrMul (.eqRefl _) (st_succ _ _).sndE)).eqSymm)
  refine congrPair (congrAp1 halfF f) ?_
  exact (congrMul s (congrMonus (.eqRefl _) (congrMul (congrAp1 parF f) (congrAp1 parF (congrAp1 halfF f))))).eqTrans
    (mul_assoc _ _ _)

theorem front_base (b : PTm n) :
    Γ ⊢[PRAAx] st (succ zero) b ≐ pairT (fstT (st zero (half b))) (okp b * sndT (st zero (half b))) := by
  have z := st_zero (Γ := Γ) b; have z' := st_zero (Γ := Γ) (half b)
  have f := z.fstE; have s := z.sndE
  refine (st_succ _ _).eqTrans (congrPair ((congrAp1 halfF f).eqTrans z'.fstE.eqSymm) ?_)
  refine (congrMul s (congrMonus (.eqRefl _) (congrMul (congrAp1 parF f) (congrAp1 parF (congrAp1 halfF f))))).eqTrans ?_
  exact (one_mul _).eqTrans (((one_mul _).eqSymm.eqTrans (mul_comm _ _)).eqTrans
    (congrMul (.eqRefl _) z'.sndE.eqSymm))

/-- Variables: `0 = N`, `1 = b`. -/
private abbrev frontF : Fm PTm 2 :=
  st (succ (var 0)) (var 1) ≐ pairT (fstT (st (var 0) (half (var 1)))) (okp (var 1) * sndT (st (var 0) (half (var 1))))

private theorem front₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] frontF := by
  ipra_ind [subst_ap2, subst_ap1, subst_pairT, subst_fstT, subst_sndT]
  · exact front_base _
  · exact front_step Prf.hyp0

theorem st_front (N b : PTm n) :
    Γ ⊢[PRAAx] st (succ N) b ≐ pairT (fstT (st N (half b))) (okp b * sndT (st N (half b))) := by
  have h := inst (Γ := Γ) front₀ (![N, b] : Fin 2 → PTm n)
  simpa using h

/-- `ok(N + 1, b) = [¬(bit₀ ∧ bit₁)] · ok(N, ⌊b/2⌋)`. -/
theorem ok_succ (N b : PTm n) : Γ ⊢[PRAAx] ok (succ N) b ≐ okp b * ok N (half b) :=
  (st_front N b).sndE

theorem ok_zero (b : PTm n) : Γ ⊢[PRAAx] ok zero b ≐ one := (st_zero b).sndE

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
  ipra_ind [subst_ap2]
  · exact (congrAp2 (sumF f) (mul_zero _) (.eqRefl _)).eqTrans ((sum_zero _ _).eqTrans (sum_zero _ _).eqSymm)
  · exact pairs_step f Prf.hyp0

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

/-- `∑_{c < 2^{N+1}} [c even] ok(N + 1, c) = C(N)`. -/
theorem E_sum (N : PTm n) : Γ ⊢[PRAAx] ap2 (sumF eB) (pw two (succ N)) (succ N) ≐ C N := by
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
  have h₂ := E_sum (Γ := Γ) N
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
  ipra_lc natEq ((ok_even (Γ := Γ) zero zero).eqTrans (ok_zero _)) +
    natEq ((ok_odd (Γ := Γ) zero zero).eqTrans ((congrMul ev_zero (ok_zero _)).eqTrans (one_mul _)))

/-! ## `C(N) = F_{N+2}` -/

/-- Variable: `0 = N`. -/
private abbrev indF : Fm PTm 1 := pairT (C (var 0)) (C (succ (var 0))) ≐ pairT (fibS (succ (var 0))) (fibS (succ (succ (var 0))))

theorem ind_base : Γ ⊢[PRAAx] pairT (C (zero : PTm n)) (C (succ zero)) ≐ pairT (fibS (succ zero)) (fibS (succ (succ zero))) := by
  have a := natEq (fibS_succ (Γ := Γ) (zero : PTm n)); have b := natEq (fibS_succ (Γ := Γ) (succ (zero : PTm n)))
  have c := natEq (fibS_zero (Γ := Γ) (n := n)); have d := natEq (fib_zero (Γ := Γ) (n := n))
  have f := natEq (C_zero (Γ := Γ) (n := n)); have g := natEq (C_one (Γ := Γ) (n := n))
  refine congrPair ?_ ?_
  · ipra_lc f - a - c - d
  · ipra_lc g - b - a - c - d - natEq (fib_succ (Γ := Γ) (zero : PTm n)) - c

theorem ind_step {N : PTm n} (ih : Γ ⊢[PRAAx] pairT (C N) (C (succ N)) ≐ pairT (fibS (succ N)) (fibS (succ (succ N)))) :
    Γ ⊢[PRAAx] pairT (C (succ N)) (C (succ (succ N))) ≐ pairT (fibS (succ (succ N))) (fibS (succ (succ (succ N)))) := by
  have i₁ := (fst_pair _ _).eqSymm.eqTrans ih.fstE
  have i₂ := (snd_pair _ _).eqSymm.eqTrans ih.sndE
  refine congrPair i₂ ((C_rec N).eqTrans ((congrAdd i₂ i₁).eqTrans ?_))
  exact ((congrAdd (.eqRefl _) (fib_succ _).eqSymm).eqTrans (fibS_succ _).eqSymm)

private theorem ind₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] indF := by
  ipra_ind [subst_ap2, subst_pairT, subst_fibS]
  · exact ind_base
  · exact ind_step Prf.hyp0

/-- The number of subsets of `{0, …, N − 1}` with no two adjacent elements is `F_{N+2}`; equivalently
the tilings of a row of length `N + 1` by squares and dominoes number `F_{N+2}`. -/
theorem independent_sets (N : PTm n) : Γ ⊢[PRAAx] C N ≐ fibS (succ N) := by
  have h := inst (Γ := Γ) ind₀ (![N] : Fin 1 → PTm n)
  have h' : Γ ⊢[PRAAx] pairT (C N) (C (succ N)) ≐ pairT (fibS (succ N)) (fibS (succ (succ N))) := by simpa using h
  exact (fst_pair _ _).eqSymm.eqTrans h'.fstE

/-! ## A leading zero does not change the scan -/

/-- `⌊d/2⌋ < P` when `d < 2P`. -/
theorem half_lt {d P : PTm n} (h : Γ ⊢[PRAAx] lt d (two * P)) : Γ ⊢[PRAAx] lt (half d) P := by
  refine .orE (lt_or_le (half d) P) Prf.hyp0 ?_
  have w := natEq (eq_add_of_le (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := le P (half d))))
  have hp := natEq (half_par (Γ := le P (half d) :: Γ) d)
  have hle : (le P (half d) :: Γ) ⊢[PRAAx] le (two * P) d :=
    le_of_eq_add (d := two * monus (half d) P + par d) (by apply deriveNat; ipra_simps; linear_combination hp + 2 * w)
  exact le_lt_absurd _ hle h.wk

/-- `1 ∸ [ok(N + 1, d) = ok(N, d)]`, over `0 = d`, `1 = N`. -/
abbrev vB : PTm 2 := monus one (eqb (ok (succ (var 1)) (var 0)) (ok (var 1) (var 0)))

theorem inst2_v (d N : PTm n) : inst2 vB d N = monus one (eqb (ok (succ N) d) (ok N d)) := by simp [inst2]

theorem okp_zero : Γ ⊢[PRAAx] okp (zero : PTm n) ≐ one :=
  (congrMonus (.eqRefl _) ((congrMul par_zero (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (monus_zero _)

theorem ext_base : Γ ⊢[PRAAx] ap2 (sumF vB) (pw two (zero : PTm n)) zero ≐ zero := by
  refine (congrAp2 (sumF vB) (pw_zero two) (.eqRefl _)).eqTrans ((sum_succ' _ _ _).eqTrans ?_)
  rw [inst2_v]
  refine (congrAdd (sum_zero _ _) (LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct.viol_of_eq ?_)).eqTrans (zero_add _)
  exact (ok_succ _ _).eqTrans ((congrMul okp_zero (ok_zero _)).eqTrans ((one_mul _).eqTrans (ok_zero _).eqSymm))

theorem ext_step {N : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF vB) (pw two N) N ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF vB) (pw two (succ N)) (succ N) ≐ zero := by
  refine (sum_congr_bounded vB LeanProofs.IPRA.Combinatorics.Vandermonde.zB (succ N) (succ N) (pw two (succ N))
    (.allI (.impI ?_))).eqTrans (LeanProofs.IPRA.Combinatorics.Vandermonde.zsum _ _)
  have e₁ : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  have e₂ : Syn.shift (pw two (succ N)) = pw two (succ (Syn.shift N)) := by simp [Syn.shift]
  rw [LeanProofs.IPRA.Combinatorics.Vandermonde.inst2_z, inst2_v, e₁, e₂]
  have ih' : Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF vB) (pw two (Syn.shift N)) (Syn.shift N) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using ih.shift
  have hl : (lt (var 0) (pw two (succ (Syn.shift N))) :: Γ.map Fm.shift) ⊢[PRAAx] lt (half (var 0)) (pw two (Syn.shift N)) :=
    half_lt (le_congr (.eqRefl _) (pw_two_succ _) Prf.hyp0)
  have v := sum_zero_elim vB ih'.wk hl
  rw [inst2_v] at v
  have e := LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct.eq_of_viol v
  exact LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct.viol_of_eq
    ((ok_succ _ _).eqTrans ((congrMul (.eqRefl _) e).eqTrans (ok_succ _ _).eqSymm))

/-- Variable: `0 = N`. -/
private abbrev extF : Fm PTm 1 := ap2 (sumF vB) (pw two (var 0)) (var 0) ≐ zero

private theorem ext₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] extF := by
  ipra_ind [subst_ap2]
  · exact ext_base
  · exact ext_step Prf.hyp0

/-- `ok(N + 1, d) = ok(N, d)` for `d < 2^N`. -/
theorem ok_ext {N d : PTm n} (h : Γ ⊢[PRAAx] lt d (pw two N)) : Γ ⊢[PRAAx] ok (succ N) d ≐ ok N d := by
  have Ψ := inst (Γ := Γ) ext₀ (![N] : Fin 1 → PTm n)
  have Ψ' : Γ ⊢[PRAAx] ap2 (sumF vB) (pw two N) N ≐ zero := by simpa using Ψ
  have v := sum_zero_elim vB Ψ' h
  rw [inst2_v] at v
  exact LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct.eq_of_viol v

/-! ## The cycle -/

/-- `[b independent in the n-cycle]`: no adjacent pair in the path, and not both `bit₀` and
`bit_{n−1}`; over `0 = b`, `1 = n`. -/
abbrev cyB : PTm 2 := ok (var 1) (var 0) * monus one (par (var 0) *
  LeanProofs.IPRA.Combinatorics.Stirling.gle (pw two (pred (var 1))) (var 0))

/-- `D(n) = ∑_{b < 2ⁿ} [b independent in the n-cycle]`. -/
abbrev D {n : ℕ} (N : PTm n) : PTm n := ap2 (sumF cyB) (pw two N) N

/-- `[c even] ok(y, c) [2c + 1 < 2^y]`, over `0 = c`, `1 = y`. -/
abbrev hB : PTm 2 := ev (var 0) * ok (var 1) (var 0) *
  monus one (LeanProofs.IPRA.Combinatorics.Stirling.gle (pw two (var 1)) (two * var 0 + one))

theorem inst2_cy (b N : PTm n) : inst2 cyB b N =
    ok N b * monus one (par b * LeanProofs.IPRA.Combinatorics.Stirling.gle (pw two (pred N)) b) := by simp [inst2]
theorem inst2_h (c y : PTm n) : inst2 hB c y =
    ev c * ok y c * monus one (LeanProofs.IPRA.Combinatorics.Stirling.gle (pw two y) (two * c + one)) := by simp [inst2]

/-- The two terms at `2c`, `2c + 1` for `n = M + 3`. -/
theorem cy_pair (c M : PTm n) :
    Γ ⊢[PRAAx] inst2 (pairB cyB) c (succ (succ (succ M))) ≐ inst2 (addBody okB hB) c (succ (succ M)) := by
  rw [inst2_pair, inst2_addBody, inst2_cy, inst2_cy, inst2_ok, inst2_h]
  have ep : Γ ⊢[PRAAx] pred (succ (succ (succ M))) ≐ succ (succ M) := pred_succ _
  refine congrAdd ?_ ?_
  · refine (congrMul (ok_even _ _) ((congrMonus (.eqRefl _) ((congrMul (par_double c) (.eqRefl _)).eqTrans (zero_mul _))).eqTrans
      (monus_zero _))).eqTrans ((mul_comm _ _).eqTrans (one_mul _))
  · have g : Γ ⊢[PRAAx] par (two * c + one) * LeanProofs.IPRA.Combinatorics.Stirling.gle (pw two (pred (succ (succ (succ M)))))
        (two * c + one) ≐ LeanProofs.IPRA.Combinatorics.Stirling.gle (pw two (succ (succ M))) (two * c + one) :=
      (congrMul (par_double_succ c) (congrMonus (.eqRefl one) (congrMonus (congrAp2 powF ep (.eqRefl two))
        (.eqRefl _)))).eqTrans (one_mul _)
    exact congrMul (ok_odd _ _) (congrMonus (.eqRefl _) g)

/-- `H = ∑_{c < 2^{M+2}} [c even] ok(M + 2, c) [2c + 1 < 2^{M+2}] = C(M)`. -/
theorem H_sum (M : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF hB) (pw two (succ (succ M))) (succ (succ M)) ≐ C M := by
  have eS : Γ ⊢[PRAAx] pw two (succ (succ M)) ≐ pw two (succ M) + pw two (succ M) :=
    (pw_two_succ _).eqTrans (by ipra_ring)
  refine (congrAp2 (sumF hB) eS (.eqRefl _)).eqTrans ((sum_split hB _ _ _).eqTrans ?_)
  refine (congrAdd ?_ ?_).eqTrans (add_zero _)
  · refine .eqTrans ?_ (E_sum M)
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_h, inst2_e]
    have e₁ : Syn.shift (succ (succ M)) = succ (succ (Syn.shift M)) := by simp [Syn.shift]
    have e₂ : Syn.shift (succ M) = succ (Syn.shift M) := by simp [Syn.shift]
    have e₃ : Syn.shift (pw two (succ M)) = pw two (succ (Syn.shift M)) := by simp [Syn.shift]
    rw [e₁, e₂, e₃]
    have hl : (lt (var 0) (pw two (succ (Syn.shift M))) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (pw two (succ (Syn.shift M))) :=
      Prf.hyp0
    have g : (lt (var 0) (pw two (succ (Syn.shift M))) :: Γ.map Fm.shift) ⊢[PRAAx]
        LeanProofs.IPRA.Combinatorics.Stirling.gle (pw two (succ (succ (Syn.shift M)))) (two * var 0 + one) ≐ zero := by
      refine LeanProofs.IPRA.Combinatorics.Stirling.gle_above ?_
      have w := natEq (eq_add_of_le hl); have p := natEq (pw_two_succ (Γ := (lt (var 0) (pw two (succ (Syn.shift M))) ::
        Γ.map Fm.shift)) (succ (Syn.shift M)))
      refine le_of_eq_add (d := two * monus (pw two (succ (Syn.shift M))) (succ (var 0))) ?_
      ipra_lc p + 2 * w
    refine (congrMul (congrMul (.eqRefl _) (ok_ext hl)) ((congrMonus (.eqRefl _) g).eqTrans (monus_zero _))).eqTrans ?_
    exact (mul_comm _ _).eqTrans (one_mul _)
  · refine (sum_congr_bounded (offB hB) LeanProofs.IPRA.Combinatorics.Vandermonde.zB (pairT (pw two (succ M)) (succ (succ M)))
      (pairT (pw two (succ M)) (succ (succ M))) (pw two (succ M)) (.allI (.impI ?_))).eqTrans
      (LeanProofs.IPRA.Combinatorics.Vandermonde.zsum _ _)
    rw [LeanProofs.IPRA.Combinatorics.Vandermonde.inst2_z, inst2_offB, inst2_h]
    have g : Γ.map Fm.shift ⊢[PRAAx] LeanProofs.IPRA.Combinatorics.Stirling.gle
        (pw two (sndT (Syn.shift (pairT (pw two (succ M)) (succ (succ M))))))
        (two * (fstT (Syn.shift (pairT (pw two (succ M)) (succ (succ M)))) + var 0) + one) ≐ one := by
      have e : Syn.shift (pairT (pw two (succ M)) (succ (succ M))) =
          pairT (pw two (succ (Syn.shift M))) (succ (succ (Syn.shift M))) := by simp [Syn.shift]
      rw [e]
      refine (congrMonus (.eqRefl _) (congrMonus (congrPw (.eqRefl _) (snd_pair _ _))
        (congrAdd (congrMul (.eqRefl _) (congrAdd (fst_pair _ _) (.eqRefl _))) (.eqRefl _)))).eqTrans ?_
      refine LeanProofs.IPRA.Combinatorics.Stirling.gle_of_le ?_
      refine le_of_eq_add (d := two * var 0 + one) ?_
      ipra_lc -natEq (pw_two_succ (Γ := Γ.map Fm.shift) (succ (Syn.shift M)))
    exact (congrMul (.eqRefl _) ((congrMonus (.eqRefl _) g.wk).eqTrans (monus_self _))).eqTrans (mul_zero _)

/-- The independent sets of the `n`-cycle number `L_n`, for `n ≥ 3`. -/
theorem cycle_count (M : PTm n) : Γ ⊢[PRAAx] D (succ (succ (succ M))) ≐ luc (succ (succ (succ M))) := by
  have hd : Γ ⊢[PRAAx] D (succ (succ (succ M))) ≐ C (succ (succ M)) + C M := by
    refine (congrAp2 (sumF cyB) (pw_two_succ _) (.eqRefl _)).eqTrans ((sum_pairs _ _ _).eqTrans ?_)
    refine (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))).eqTrans ((sum_add _ _ _ _).eqTrans (congrAdd (.eqRefl _) (H_sum M)))
    have e₁ : Syn.shift (succ (succ (succ M))) = succ (succ (succ (Syn.shift M))) := by simp [Syn.shift]
    have e₂ : Syn.shift (succ (succ M)) = succ (succ (Syn.shift M)) := by simp [Syn.shift]
    rw [e₁, e₂]
    exact cy_pair _ _
  ipra_lc natEq hd + natEq (independent_sets (Γ := Γ) (succ (succ M))) + natEq (independent_sets (Γ := Γ) M) -
    natEq (luc_eq (Γ := Γ) (succ (succ (succ M)))) + natEq (fib_succ (Γ := Γ) (succ (succ M))) -
    natEq (fibS_succ (Γ := Γ) (succ (succ M))) - natEq (fib_succ (Γ := Γ) (succ M))

end LeanProofs.IPRA.Combinatorics.IndependentSets
