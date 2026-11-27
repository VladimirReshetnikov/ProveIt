import IPRADerivations.DiophantineNumberTheory.GcdList
import IPRADerivations.Foundations.BoundedReflection

/-!
# Divisors of a coprime product (`robin_ipra_research_2026-11-19`, multiplicativity of `σ`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/lcm_bridge.tex`, Lemma "Exact finite identity":
"The finite geometric-series formula and multiplicativity of `σ` give `A(L_P) = Π_{p≤P} (1 − p^{−a_p(P)−1})/(1 − p^{−1})`",
and `report.tex`, `thm:three` (products of at most three prime powers). Multiplicativity of `σ` rests on the
factorization of the divisors of a coprime product, proved here for `m, N ≥ 1` with `gcd(m, N) = 1`:

* `split_exists`: a divisor `d ≥ 1` of `mN` is `d = a b` with `a = gcd(d, m) ∣ m` and `b = d / a ∣ N`
  (`Coprime.coprime_quotients` and Gauss's lemma `Coprime.gauss`);
* `split_unique`: `a b = a' b'` with `a, a' ∣ m`, `b, b' ∣ N` forces `a = a'` and `b = b'`;
* `cnt_pt`: the pointwise count `[a ∣ m][b ∣ N][ab = d] = [d ∣ mN][a = a₀][b = b₀]` for `d ≥ 1`, with
  `a₀ = gcd(d, m)`, `b₀ = d / a₀`: each divisor of `mN` has exactly one factorization, and other `d` have none.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.DivisorSplit

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_of_eq' eq_of_dvd' dvd_le' gcd_dvd' gauss coprime_dvd_left
  gcd_comm_one coprime_quotients pos_of_eq_mul one_le_of_pos dvd_mul')

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Cancellation and positivity -/

theorem mul_cancel {a x y : PTm n} (ha : Γ ⊢[PRAAx] a ≐ succ (pred a)) (h : Γ ⊢[PRAAx] a * x ≐ a * y) :
    Γ ⊢[PRAAx] x ≐ y :=
  mul_eq_cancel_at ha h

/-- A divisor of a positive number is positive. -/
theorem pos_of_dvd {a m : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (h : Γ ⊢[PRAAx] dvd a m) :
    Γ ⊢[PRAAx] a ≐ succ (pred a) := by
  refine .orE (zero_or_succ a) ?_ Prf.hyp0
  have z : ((a ≐ zero) :: Γ) ⊢[PRAAx] m ≐ zero :=
    (rem_by_zero m).eqSymm.eqTrans ((congrAp2 remF (.eqRefl _) Prf.hyp0).eqSymm.eqTrans h.wk)
  exact succ_ne_zero' _ (hm.wk.eqSymm.eqTrans z)

/-! ## Existence and uniqueness of the factorization -/

/-- A divisor `d ≥ 1` of `mN` is `gcd(d, m) · (d / gcd(d, m))` with the factors dividing `m` and `N`. -/
theorem split_exists {d m N : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hc : Γ ⊢[PRAAx] gcd m N ≐ one)
    (h : Γ ⊢[PRAAx] dvd d (m * N)) :
    (Γ ⊢[PRAAx] dvd (gcd d m) m) ∧ (Γ ⊢[PRAAx] dvd (quo d (gcd d m)) N) ∧
      (Γ ⊢[PRAAx] d ≐ gcd d m * quo d (gcd d m)) := by
  have hu := gcd_pos (B := m) hd
  have hud := gcd_dvd' (b := m) hd
  have eD := eq_of_dvd' hu (Prf.andE₁ hud)
  have eM := eq_of_dvd' hu (Prf.andE₂ hud)
  have cq := coprime_quotients (c := m) hd
  have hk := eq_of_dvd' hd h
  have he := pos_of_eq_mul hd eD
  have c1 : Γ ⊢[PRAAx] gcd d m * (quo m (gcd d m) * N) ≐ gcd d m * (quo d (gcd d m) * quo (m * N) d) := by
    refine withEq eM fun h1 => withEq eD fun h2 => withEq hk fun h3 => ?_
    ipra_lc h3 - 𝔞 N * h1 + 𝔞 (quo (m * N) d) * h2
  have c2 := mul_cancel hu c1
  have hdv : Γ ⊢[PRAAx] dvd (quo d (gcd d m)) (quo m (gcd d m) * N) := dvd_of_eq' he c2
  exact ⟨Prf.andE₂ hud, gauss he cq hdv, eD⟩

/-- `a b = a' b'` with `a, a' ∣ m`, `b, b' ∣ N` and `gcd(m, N) = 1` forces `a = a'`, `b = b'`. -/
theorem split_unique {a b a' b' m N : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m)) (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hc : Γ ⊢[PRAAx] gcd m N ≐ one) (ha : Γ ⊢[PRAAx] dvd a m) (hb : Γ ⊢[PRAAx] dvd b N)
    (ha' : Γ ⊢[PRAAx] dvd a' m) (hb' : Γ ⊢[PRAAx] dvd b' N) (h : Γ ⊢[PRAAx] a * b ≐ a' * b') :
    (Γ ⊢[PRAAx] a ≐ a') ∧ (Γ ⊢[PRAAx] b ≐ b') := by
  have pa := pos_of_dvd hm ha
  have pa' := pos_of_dvd hm ha'
  have pb := pos_of_dvd hN hb
  have pb' := pos_of_dvd hN hb'
  -- `gcd(a, b') = 1` and `gcd(a', b) = 1`
  have g1 : Γ ⊢[PRAAx] gcd a N ≐ one := coprime_dvd_left pa ha hc
  have g1' : Γ ⊢[PRAAx] gcd a' N ≐ one := coprime_dvd_left pa' ha' hc
  have g2 : Γ ⊢[PRAAx] gcd a b' ≐ one := gcd_comm_one pa (coprime_dvd_left pb' hb' (gcd_comm_one hN g1))
  have g2' : Γ ⊢[PRAAx] gcd a' b ≐ one := gcd_comm_one pa' (coprime_dvd_left pb hb (gcd_comm_one hN g1'))
  -- `a ∣ a'` and `a' ∣ a`
  have d1 : Γ ⊢[PRAAx] dvd a (b' * a') :=
    dvd_of_eq' pa (w := b) (((mul_comm _ _).eqTrans h.eqSymm))
  have d2 : Γ ⊢[PRAAx] dvd a' (b * a) :=
    dvd_of_eq' pa' (w := b') (((mul_comm _ _).eqTrans h))
  have aa : Γ ⊢[PRAAx] dvd a a' := gauss pa g2 d1
  have aa' : Γ ⊢[PRAAx] dvd a' a := gauss pa' g2' d2
  have e : Γ ⊢[PRAAx] a ≐ a' := le_antisymm (dvd_le' pa aa pa') (dvd_le' pa' aa' pa)
  exact ⟨e, mul_cancel pa (h.eqTrans (congrMul e.eqSymm (.eqRefl _)))⟩

/-! ## The pointwise count -/

/-- Three indicators: either their product vanishes or all three are `1`. -/
theorem tri {x y z : PTm n} (hx : Γ ⊢[PRAAx] (x ≐ zero) ⋎ (x ≐ one)) (hy : Γ ⊢[PRAAx] (y ≐ zero) ⋎ (y ≐ one))
    (hz : Γ ⊢[PRAAx] (z ≐ zero) ⋎ (z ≐ one)) :
    Γ ⊢[PRAAx] (x * y * z ≐ zero) ⋎ ((x ≐ one) ⋏ ((y ≐ one) ⋏ (z ≐ one))) := by
  refine .orE hx ?_ ?_
  · exact .orI₁ (withEq Prf.hyp0 fun e => by apply deriveNat; ipra_simps; rw [e]; ring)
  refine .orE hy.wk ?_ ?_
  · exact .orI₁ (withEq Prf.hyp0 fun e => by apply deriveNat; ipra_simps; rw [e]; ring)
  refine .orE hz.wk.wk ?_ ?_
  · exact .orI₁ (withEq Prf.hyp0 fun e => by apply deriveNat; ipra_simps; rw [e]; ring)
  exact .orI₂ (.andI Prf.hyp1.wk (.andI Prf.hyp1 Prf.hyp0))

/-- All three tests pass for `(a, b)`: `d ∣ mN`. -/
theorem pass_dvd {d m N a b : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (ha : Γ ⊢[PRAAx] dvd a m) (hb : Γ ⊢[PRAAx] dvd b N)
    (hab : Γ ⊢[PRAAx] a * b ≐ d) : Γ ⊢[PRAAx] dvd d (m * N) := by
  have em := eq_of_dvd' (pos_of_dvd hm ha) ha
  have eN := eq_of_dvd' (pos_of_dvd hN hb) hb
  refine dvd_of_eq' hd (w := quo m a * quo N b) ?_
  refine withEq em fun h1 => withEq eN fun h2 => withEq hab fun h3 => ?_
  ipra_lc 𝔞 N * h1 + 𝔞 a * 𝔞 (quo m a) * h2 + 𝔞 (quo m a) * 𝔞 (quo N b) * h3

/-- `[a ∣ m][b ∣ N][ab = d] = [d ∣ mN][a = gcd(d,m)][b = d/gcd(d,m)]` for `d, m, N ≥ 1`, `gcd(m, N) = 1`. -/
theorem cnt_pt {d m N : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hc : Γ ⊢[PRAAx] gcd m N ≐ one) (a b : PTm n) :
    Γ ⊢[PRAAx] eqb (rem m a) zero * eqb (rem N b) zero * eqb (a * b) d ≐
      eqb (rem (m * N) d) zero * (eqb a (gcd d m) * eqb b (quo d (gcd d m))) := by
  let X : PTm n := eqb (rem m a) zero * eqb (rem N b) zero * eqb (a * b) d
  let Pass : Fm PTm n := (eqb (rem m a) zero ≐ one) ⋏ ((eqb (rem N b) zero ≐ one) ⋏ (eqb (a * b) d ≐ one))
  have tr : Γ ⊢[PRAAx] (X ≐ zero) ⋎ Pass := tri (eqb_cases _ _) (eqb_cases _ _) (eqb_cases _ _)
  -- the facts behind a passing test
  have facts : ∀ {Δ : List (Fm PTm n)}, (Δ ⊢[PRAAx] Pass) →
      (Δ ⊢[PRAAx] dvd a m) ∧ (Δ ⊢[PRAAx] dvd b N) ∧ (Δ ⊢[PRAAx] a * b ≐ d) := fun h =>
    ⟨eq_of_eqb (Prf.andE₁ h), eq_of_eqb (Prf.andE₁ (Prf.andE₂ h)), eq_of_eqb (Prf.andE₂ (Prf.andE₂ h))⟩
  -- the right side is zero ⇒ so is the left side, given a passing test is impossible
  have zero_case : ∀ {Δ : List (Fm PTm n)}, (Γ ⊆ Δ) →
      (Δ ⊢[PRAAx] eqb (rem (m * N) d) zero * (eqb a (gcd d m) * eqb b (quo d (gcd d m))) ≐ zero) →
      ((Pass :: Δ) ⊢[PRAAx] (one : PTm n) ≐ zero) →
      (Δ ⊢[PRAAx] X ≐ eqb (rem (m * N) d) zero * (eqb a (gcd d m) * eqb b (quo d (gcd d m)))) := by
    intro Δ s hr hp
    refine .orE (tr.weaken s) ?_ ?_
    · exact Prf.hyp0.eqTrans hr.wk.eqSymm
    · exact succ_ne_zero' _ hp
  refine .orE (eqb_cases (Γ := Γ) (rem (m * N) d) zero) ?_ ?_
  · -- `d ∤ mN`
    let C : List (Fm PTm n) := (eqb (rem (m * N) d) zero ≐ zero) :: Γ
    have hr : C ⊢[PRAAx] eqb (rem (m * N) d) zero * (eqb a (gcd d m) * eqb b (quo d (gcd d m))) ≐ zero :=
      (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
    refine zero_case (List.subset_cons_self _ _) hr ?_
    obtain ⟨fa, fb, fab⟩ := facts (Δ := Pass :: C) Prf.hyp0
    have dv := pass_dvd hd.wk.wk hm.wk.wk hN.wk.wk fa fb fab
    exact (eqb_of_eq dv).eqSymm.eqTrans Prf.hyp1
  · -- `d ∣ mN`: the factorization `(a₀, b₀)`
    let C : List (Fm PTm n) := (eqb (rem (m * N) d) zero ≐ one) :: Γ
    have hdv : C ⊢[PRAAx] dvd d (m * N) := eq_of_eqb Prf.hyp0
    obtain ⟨h0a, h0b, h0e⟩ := split_exists hd.wk hc.wk hdv
    have uniq : ∀ {Δ : List (Fm PTm n)}, (C ⊆ Δ) → (Δ ⊢[PRAAx] Pass) →
        (Δ ⊢[PRAAx] a ≐ gcd d m) ∧ (Δ ⊢[PRAAx] b ≐ quo d (gcd d m)) := by
      intro Δ s hp
      obtain ⟨fa, fb, fab⟩ := facts hp
      exact split_unique (hm.weaken (fun _ hx => s (List.mem_cons_of_mem _ hx)))
        (hN.weaken (fun _ hx => s (List.mem_cons_of_mem _ hx))) (hc.weaken (fun _ hx => s (List.mem_cons_of_mem _ hx)))
        fa fb (h0a.weaken s) (h0b.weaken s) (fab.eqTrans (h0e.weaken s))
    refine .orE (eqb_cases (Γ := C) a (gcd d m)) ?_ ?_
    · let C' : List (Fm PTm n) := (eqb a (gcd d m) ≐ zero) :: C
      have hr : C' ⊢[PRAAx] eqb (rem (m * N) d) zero * (eqb a (gcd d m) * eqb b (quo d (gcd d m))) ≐ zero :=
        (congrMul (.eqRefl _) ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (mul_zero _)
      refine zero_case (fun _ hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) hr ?_
      have u := uniq (Δ := Pass :: C') (fun _ hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) Prf.hyp0
      exact (eqb_of_eq u.1).eqSymm.eqTrans Prf.hyp1
    · let C' : List (Fm PTm n) := (eqb a (gcd d m) ≐ one) :: C
      refine .orE (eqb_cases (Γ := C') b (quo d (gcd d m))) ?_ ?_
      · let C'' : List (Fm PTm n) := (eqb b (quo d (gcd d m)) ≐ zero) :: C'
        have hr : C'' ⊢[PRAAx] eqb (rem (m * N) d) zero * (eqb a (gcd d m) * eqb b (quo d (gcd d m))) ≐ zero :=
          (congrMul (.eqRefl _) ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))).eqTrans (mul_zero _)
        refine zero_case (fun _ hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))) hr ?_
        have u := uniq (Δ := Pass :: C'')
          (fun _ hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))) Prf.hyp0
        exact (eqb_of_eq u.2).eqSymm.eqTrans Prf.hyp1
      · -- `(a, b) = (a₀, b₀)`: everything is `1`
        let C'' : List (Fm PTm n) := (eqb b (quo d (gcd d m)) ≐ one) :: C'
        have ea : C'' ⊢[PRAAx] a ≐ gcd d m := eq_of_eqb Prf.hyp1
        have eb : C'' ⊢[PRAAx] b ≐ quo d (gcd d m) := eq_of_eqb Prf.hyp0
        have t1 : C'' ⊢[PRAAx] eqb (rem m a) zero ≐ one := eqb_of_eq (dvd_congr_left ea.eqSymm h0a.wk.wk)
        have t2 : C'' ⊢[PRAAx] eqb (rem N b) zero ≐ one := eqb_of_eq (dvd_congr_left eb.eqSymm h0b.wk.wk)
        have t3 : C'' ⊢[PRAAx] eqb (a * b) d ≐ one := eqb_of_eq ((congrMul ea eb).eqTrans h0e.wk.wk.eqSymm)
        have r0 : C'' ⊢[PRAAx] eqb (rem (m * N) d) zero ≐ one := Prf.hyp1.wk
        refine (congrMul (congrMul t1 t2) t3).eqTrans (Prf.eqTrans ?_
          (congrMul r0 (congrMul Prf.hyp1 Prf.hyp0)).eqSymm)
        apply deriveNat; ipra_simps; try ring

end LeanProofs.IPRA.AnalyticNumberTheory.DivisorSplit

export_ipra AnalyticNumberTheory.DivisorSplit (pos_of_dvd)
