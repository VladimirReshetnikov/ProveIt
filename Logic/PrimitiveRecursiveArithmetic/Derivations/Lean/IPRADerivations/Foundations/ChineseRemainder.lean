import IPRADerivations.Core.EuclidLemma
import IPRADerivations.Combinatorics.BinomialIdentities

/-!
# The two-modulus Chinese remainder theorem

Packet: `foundations/ipra_categorical_methods`, Theorem `thm:crt` (constructive two-modulus
Chinese remainder isomorphism, without a coprimality assumption).

For `a, b ≥ 1`, `g = gcd(a, b)`, `b' = b / g` and `ℓ = a b'`:

* `crt_exists`: residues `r mod a` and `s mod b` that agree modulo `g` are the residues
  of a common `x`;
* `crt_unique`: numbers with the same residues modulo `a` and modulo `b` have the same
  residue modulo `ℓ`.

The witness of `crt_exists` is the paper's `x = r + a t`. With `a = g a'`, Bézout's identity
gives `P a' + b' W = 1 + Q b'` (with `W = 0`, or with `W = 1` after multiplying the other
Bézout case by `b' - 1`), and `t = P (β + α (b' - 1))`, where `r = g α + ρ` and
`s = g β + ρ`. Uniqueness follows the paper: if `a ∣ z` and `b ∣ z`, then `z = a k`,
`b' ∣ a' k` and, multiplying the Bézout relation by `k`, `b' ∣ k`, so `ℓ ∣ z`.
-/

namespace LeanProofs.IPRA.Foundations.ChineseRemainder

open_ipra exports
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Residues -/

theorem rem_eq_of_eq {M x y k₁ k₂ : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] x + M * k₁ ≐ y + M * k₂) : Γ ⊢[PRAAx] rem x M ≐ rem y M := by
  have rx := Prf.andE₂ (Division.div_mod_add_mul (x := x) (k := k₁) hM)
  have ry := Prf.andE₂ (Division.div_mod_add_mul (x := y) (k := k₂) hM)
  exact rx.eqSymm.eqTrans ((congrAp2 remF h (.eqRefl M)).eqTrans ry)

/-- `x + M k₁ = y + M k₂` gives `x ≡ y (mod M)`. -/
theorem rem_eq_of_eq' {M' x y k₁ k₂ : PTm n} (h : Γ ⊢[PRAAx] x + succ M' * k₁ ≐ y + succ M' * k₂) :
    Γ ⊢[PRAAx] rem x (succ M') ≐ rem y (succ M') :=
  rem_eq_of_eq (congrSucc (pred_succ _).eqSymm) h

/-- Equal remainders give the equality obtained by exchanging the two quotients. -/
theorem eq_add_quo_of_rem_eq {M x y : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] rem x M ≐ rem y M) :
    Γ ⊢[PRAAx] x + M * quo y M ≐ y + M * quo x M := by
  ipra_lc natEq (Prf.andE₁ (div_mod_at (x := x) hM)) -
    natEq (Prf.andE₁ (div_mod_at (x := y) hM)) + natEq h

/-- Compare the missing summands in two balances with congruent known terms. -/
theorem rem_of_balanced_add {x y a b c e M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hx : Γ ⊢[PRAAx] x + a ≐ b) (hy : Γ ⊢[PRAAx] y + c ≐ e)
    (ha : Γ ⊢[PRAAx] rem a M ≐ rem c M) (hb : Γ ⊢[PRAAx] rem b M ≐ rem e M) :
    Γ ⊢[PRAAx] rem x M ≐ rem y M := by
  refine rem_eq_of_eq hM (k₁ := quo e M + quo a M) (k₂ := quo b M + quo c M) ?_
  ipra_lc natEq hx - natEq hy + natEq (eq_add_quo_of_rem_eq hM hb) - natEq (eq_add_quo_of_rem_eq hM ha)

/-- Multiplying both sides of a congruence by a fixed factor preserves it. -/
theorem rem_mul_right_congr {M x y : PTm n} (c : PTm n) (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] rem x M ≐ rem y M) : Γ ⊢[PRAAx] rem (x * c) M ≐ rem (y * c) M := by
  refine rem_eq_of_eq hM (k₁ := quo y M * c) (k₂ := quo x M * c) ?_
  ipra_lc 𝔞 c * natEq (eq_add_quo_of_rem_eq hM h)

/-- Multiplication preserves congruence in both factors. -/
theorem rem_mul_congr_both {M x y x' y' : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h1 : Γ ⊢[PRAAx] rem x M ≐ rem y M) (h2 : Γ ⊢[PRAAx] rem x' M ≐ rem y' M) :
    Γ ⊢[PRAAx] rem (x * x') M ≐ rem (y * y') M := by
  exact (rem_mul_right_congr x' hM h1).eqTrans
    ((congrAp2 remF (mul_comm y x') (.eqRefl _)).eqTrans
      ((rem_mul_right_congr y hM h2).eqTrans (congrAp2 remF (mul_comm y' y) (.eqRefl _))))

/-- Compare two folds using the same operation on remainders at each successor step. -/
theorem fold_congr_mod (fold : PTm 2 → PR 2)
    (combine : PTm (n + 1) → PTm (n + 1) → PTm (n + 1))
    (f g : PTm 2) {N x y M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      rem (inst2 f (var 0) (Syn.shift x)) (Syn.shift M) ≐ rem (inst2 g (var 0) (Syn.shift y)) (Syn.shift M)))
    (base : Γ ⊢[PRAAx] ap2 (fold f) zero x ≐ ap2 (fold g) zero y)
    (advance : ∀ {Δ : List (Fm PTm (n + 1))} (body : PTm 2) (j z : PTm (n + 1)),
      Δ ⊢[PRAAx] ap2 (fold body) (succ j) z ≐ combine (ap2 (fold body) j z) (inst2 body j z))
    (combine_congr : ∀ {Δ : List (Fm PTm (n + 1))} {m a b c d : PTm (n + 1)},
      (Δ ⊢[PRAAx] m ≐ succ (pred m)) → (Δ ⊢[PRAAx] rem a m ≐ rem b m) →
      (Δ ⊢[PRAAx] rem c m ≐ rem d m) → (Δ ⊢[PRAAx] rem (combine a c) m ≐ rem (combine b d) m)) :
    Γ ⊢[PRAAx] rem (ap2 (fold f) N x) M ≐ rem (ap2 (fold g) N y) M := by
  let P : Fm PTm (n + 1) :=
    rem (ap2 (fold f) (var 0) (Syn.shift x)) (Syn.shift M) ≐
      rem (ap2 (fold g) (var 0) (Syn.shift y)) (Syn.shift M)
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N trivial ?_ ?_
    · simpa [P, rem] using congrAp2 remF base (.eqRefl M)
    · simp only [P, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI ((congrAp2 remF (advance f (var 0) (Syn.shift x)) (.eqRefl _)).eqTrans ?_)
      exact (combine_congr (Common.pos_shift hM).wk.wk Prf.hyp1 (.impE h.allOpen.wk.wk Prf.hyp0)).eqTrans
        (congrAp2 remF (advance g (var 0) (Syn.shift y)) (.eqRefl _)).eqSymm
  simpa [P, rem] using atBound

/-- Finite products of pointwise-congruent bodies are congruent. -/
theorem rem_prod_congr (f g : PTm 2) {N x y M : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      rem (inst2 f (var 0) (Syn.shift x)) (Syn.shift M) ≐ rem (inst2 g (var 0) (Syn.shift y)) (Syn.shift M))) :
    Γ ⊢[PRAAx] rem (ap2 (prodF f) N x) M ≐ rem (ap2 (prodF g) N y) M :=
  fold_congr_mod prodF (· * ·) f g hM h ((prod_zero f x).eqTrans (prod_zero g y).eqSymm)
    (fun body i z => prod_succ body i z) (fun hPos hPrefix hEntry => rem_mul_congr_both hPos hPrefix hEntry)

/-- A natural power preserves the congruence of its base. -/
theorem rem_pow_congr {M x y : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] rem x M ≐ rem y M) (e : PTm n) :
    Γ ⊢[PRAAx] rem (pw x e) M ≐ rem (pw y e) M := by
  let P : Fm PTm (n + 1) :=
    rem (pw (Syn.shift x) (var 0)) (Syn.shift M) ≐ rem (pw (Syn.shift y) (var 0)) (Syn.shift M)
  have all : Γ ⊢[PRAAx] Fm.all P := by
    refine PRA.qfInd P trivial ?_ ?_
    · simpa [P, rem] using congrAp2 remF ((pw_zero x).eqTrans (pw_zero y).eqSymm) (.eqRefl M)
    · simp only [P, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have factor : Γ.map Fm.shift ⊢[PRAAx] rem (Syn.shift x) (Syn.shift M) ≐ rem (Syn.shift y) (Syn.shift M) := by
        simpa [Fm.shift, Syn.shift] using h.shift
      exact (congrAp2 remF (pw_succ _ _) (.eqRefl _)).eqTrans
        ((rem_mul_congr_both (Common.pos_shift hM).wk Prf.hyp0 factor.wk).eqTrans
          (congrAp2 remF (pw_succ _ _) (.eqRefl _)).eqSymm)
  simpa [P, rem] using all.allE e

/-- `x ≡ x + z (mod M)` gives `M ∣ z`. -/
theorem dvd_of_rem_eq {M' x z : PTm n} (h : Γ ⊢[PRAAx] rem x (succ M') ≐ rem (x + z) (succ M')) :
    Γ ⊢[PRAAx] dvd (succ M') z := by
  have dx := div_mod (Γ := Γ) x M'
  have dxz := div_mod (Γ := Γ) (x + z) M'
  have e : Γ ⊢[PRAAx] z + succ M' * quo x (succ M') ≐ succ M' * quo (x + z) (succ M') := by
    refine add_right_cancel (c := rem x (succ M')) ?_
    refine withEq (Prf.andE₁ dx) fun e₁ => withEq (Prf.andE₁ dxz) fun e₂ => withEq h fun e₃ => ?_
    ipra_lc e₂ - e₁ - e₃
  exact dvd_sub (dvd_of_eq e) (dvd_of_eq (.eqRefl _))

/-! ## The algebra -/

/-- The second congruence of the witness. -/
theorem crt_alg {A B D a' b' c P W Qc r s α β ρ ρ' : PTm n}
    (eA : Γ ⊢[PRAAx] A ≐ D * a') (eB : Γ ⊢[PRAAx] B ≐ D * b')
    (key : Γ ⊢[PRAAx] P * a' + b' * W ≐ one + Qc * b') (hb : Γ ⊢[PRAAx] b' ≐ succ c)
    (er : Γ ⊢[PRAAx] r ≐ D * α + ρ) (es : Γ ⊢[PRAAx] s ≐ D * β + ρ') (eρ : Γ ⊢[PRAAx] ρ ≐ ρ') :
    Γ ⊢[PRAAx] (r + A * (P * (β + α * c))) + B * (W * (β + α * c)) ≐
      s + B * (α + Qc * (β + α * c)) := by
  ipra_lc (Groth.ι (IPRA.Q.mk Γ P) * (Groth.ι (IPRA.Q.mk Γ β) + Groth.ι (IPRA.Q.mk Γ α) * Groth.ι (IPRA.Q.mk Γ c))) * natEq eA +
    (Groth.ι (IPRA.Q.mk Γ W) * (Groth.ι (IPRA.Q.mk Γ β) + Groth.ι (IPRA.Q.mk Γ α) * Groth.ι (IPRA.Q.mk Γ c)) - Groth.ι (IPRA.Q.mk Γ α) - Groth.ι (IPRA.Q.mk Γ Qc) * (Groth.ι (IPRA.Q.mk Γ β) + Groth.ι (IPRA.Q.mk Γ α) * Groth.ι (IPRA.Q.mk Γ c))) * natEq eB +
    (Groth.ι (IPRA.Q.mk Γ D) * (Groth.ι (IPRA.Q.mk Γ β) + Groth.ι (IPRA.Q.mk Γ α) * Groth.ι (IPRA.Q.mk Γ c))) * natEq key +
    natEq er - natEq es + natEq eρ - Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ α) * natEq hb

/-- Bézout's first case, divided by the gcd. -/
theorem bezout_reduced₁ {g A B D a' b' U V : PTm n} (hD : Γ ⊢[PRAAx] D ≐ succ (pred D))
    (h : Γ ⊢[PRAAx] g + V * B ≐ U * A) (hg : Γ ⊢[PRAAx] g ≐ D)
    (eA : Γ ⊢[PRAAx] A ≐ D * a') (eB : Γ ⊢[PRAAx] B ≐ D * b') :
    Γ ⊢[PRAAx] U * a' + b' * zero ≐ one + V * b' := by
  refine Combinatorics.BinomialIdentities.mul_cancel hD ?_
  ipra_lc -natEq h + natEq hg + Groth.ι (IPRA.Q.mk Γ V) * natEq eB - Groth.ι (IPRA.Q.mk Γ U) * natEq eA

/-- Bézout's second case, divided by the gcd and multiplied by `b' - 1`. -/
theorem bezout_reduced₂ {g A B D a' b' c U V : PTm n} (hD : Γ ⊢[PRAAx] D ≐ succ (pred D))
    (h : Γ ⊢[PRAAx] g + U * A ≐ V * B) (hg : Γ ⊢[PRAAx] g ≐ D)
    (eA : Γ ⊢[PRAAx] A ≐ D * a') (eB : Γ ⊢[PRAAx] B ≐ D * b') (hb : Γ ⊢[PRAAx] b' ≐ succ c) :
    Γ ⊢[PRAAx] (U * c) * a' + b' * one ≐ one + (V * c) * b' := by
  have k : Γ ⊢[PRAAx] one + U * a' ≐ V * b' := by
    refine Combinatorics.BinomialIdentities.mul_cancel hD ?_
    ipra_lc natEq h - natEq hg - Groth.ι (IPRA.Q.mk Γ U) * natEq eA + Groth.ι (IPRA.Q.mk Γ V) * natEq eB
  ipra_lc Groth.ι (IPRA.Q.mk Γ c) * natEq k + natEq hb

/-- `A k = z = B w` with `A = D a'`, `B = D b'`. -/
theorem unique_alg₁ {A A₁ B B₁ D a' b' z k w : PTm n}
    (eA : Γ ⊢[PRAAx] A ≐ D * a') (eB : Γ ⊢[PRAAx] B ≐ D * b') (hA : Γ ⊢[PRAAx] A ≐ A₁)
    (hB : Γ ⊢[PRAAx] B ≐ B₁) (ez : Γ ⊢[PRAAx] z ≐ A₁ * k) (ez' : Γ ⊢[PRAAx] z ≐ B₁ * w) :
    Γ ⊢[PRAAx] D * (a' * k) ≐ D * (b' * w) := by
  ipra_lc natEq ez' - natEq ez + Groth.ι (IPRA.Q.mk Γ k) * natEq hA - Groth.ι (IPRA.Q.mk Γ w) * natEq hB -
    Groth.ι (IPRA.Q.mk Γ k) * natEq eA + Groth.ι (IPRA.Q.mk Γ w) * natEq eB

/-- The Bézout relation times `k`, with `a' k = b' w`. -/
theorem unique_alg₂ {a' b' b₁ P W Qc k w : PTm n}
    (key : Γ ⊢[PRAAx] P * a' + b' * W ≐ one + Qc * b') (hk : Γ ⊢[PRAAx] a' * k ≐ b' * w)
    (hb : Γ ⊢[PRAAx] b' ≐ b₁) :
    Γ ⊢[PRAAx] k + b₁ * (Qc * k) ≐ b₁ * (P * w + W * k) := by
  ipra_lc -Groth.ι (IPRA.Q.mk Γ k) * natEq key + Groth.ι (IPRA.Q.mk Γ P) * natEq hk -
    (Groth.ι (IPRA.Q.mk Γ Qc) * Groth.ι (IPRA.Q.mk Γ k) - Groth.ι (IPRA.Q.mk Γ W) * Groth.ι (IPRA.Q.mk Γ k) - Groth.ι (IPRA.Q.mk Γ P) * Groth.ι (IPRA.Q.mk Γ w)) * natEq hb

/-- `z = A₁ k`, `k = b₁ m` give `z = (A b') m`. -/
theorem unique_alg₃ {A A₁ b' b₁ z k m : PTm n} (hA : Γ ⊢[PRAAx] A ≐ A₁) (hb : Γ ⊢[PRAAx] b' ≐ b₁)
    (ez : Γ ⊢[PRAAx] z ≐ A₁ * k) (ek : Γ ⊢[PRAAx] k ≐ b₁ * m) :
    Γ ⊢[PRAAx] z ≐ (A * b') * m := by
  ipra_lc natEq ez + Groth.ι (IPRA.Q.mk Γ A₁) * natEq ek -
    Groth.ι (IPRA.Q.mk Γ m) * Groth.ι (IPRA.Q.mk Γ b') * natEq hA -
    Groth.ι (IPRA.Q.mk Γ m) * Groth.ι (IPRA.Q.mk Γ A₁) * natEq hb

/-! ## The cores -/

/-- The witness `x = r + a P (β + α c)`, with `α = r / D`, `β = s / D`. -/
abbrev witness (A D P c r s : PTm n) : PTm n := r + A * (P * (quo s D + quo r D * c))

/-- Existence, given a reduced Bézout relation. -/
theorem exists_core {A B G' a' b' c P W Qc r s : PTm n}
    (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B))
    (eA : Γ ⊢[PRAAx] A ≐ succ G' * a') (eB : Γ ⊢[PRAAx] B ≐ succ G' * b')
    (key : Γ ⊢[PRAAx] P * a' + b' * W ≐ one + Qc * b') (hb : Γ ⊢[PRAAx] b' ≐ succ c)
    (hc : Γ ⊢[PRAAx] rem r (succ G') ≐ rem s (succ G')) :
    Γ ⊢[PRAAx] rem (witness A (succ G') P c r s) A ≐ rem r A ⋏
      rem (witness A (succ G') P c r s) B ≐ rem s B := by
  have dr := div_mod (Γ := Γ) r G'
  have ds := div_mod (Γ := Γ) s G'
  refine .andI (rem_eq_of_eq hA (k₁ := zero) (k₂ := P * (quo s (succ G') + quo r (succ G') * c))
    (by ipra_ring)) ?_
  exact rem_eq_of_eq hB (crt_alg eA eB key hb (Prf.andE₁ dr) (Prf.andE₁ ds) hc)

/-- Uniqueness for `x ≤ y`, given a reduced Bézout relation. -/
theorem unique_core {A B D a' b' P W Qc x y : PTm n}
    (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B))
    (hD : Γ ⊢[PRAAx] D ≐ succ (pred D))
    (eA : Γ ⊢[PRAAx] A ≐ D * a') (eB : Γ ⊢[PRAAx] B ≐ D * b')
    (key : Γ ⊢[PRAAx] P * a' + b' * W ≐ one + Qc * b') (hb : Γ ⊢[PRAAx] b' ≐ succ (pred b'))
    (hxA : Γ ⊢[PRAAx] rem x A ≐ rem y A) (hxB : Γ ⊢[PRAAx] rem x B ≐ rem y B)
    (hxy : Γ ⊢[PRAAx] le x y) : Γ ⊢[PRAAx] rem x (A * b') ≐ rem y (A * b') := by
  have ey := eq_add_of_le hxy
  -- x ≡ x + z modulo A and modulo B.
  have mA : Γ ⊢[PRAAx] rem x (succ (pred A)) ≐ rem (x + monus y x) (succ (pred A)) :=
    (congrAp2 remF (.eqRefl _) hA.eqSymm).eqTrans (hxA.eqTrans
      (congrAp2 remF ey hA))
  have mB : Γ ⊢[PRAAx] rem x (succ (pred B)) ≐ rem (x + monus y x) (succ (pred B)) :=
    (congrAp2 remF (.eqRefl _) hB.eqSymm).eqTrans (hxB.eqTrans
      (congrAp2 remF ey hB))
  have ez := eq_of_dvd (dvd_of_rem_eq mA)
  have ez' := eq_of_dvd (dvd_of_rem_eq mB)
  have hk := Combinatorics.BinomialIdentities.mul_cancel hD (unique_alg₁ eA eB hA hB ez ez')
  have hdk : Γ ⊢[PRAAx] dvd (succ (pred b')) (quo (monus y x) (succ (pred A))) :=
    dvd_sub (dvd_of_eq (unique_alg₂ key hk hb)) (dvd_of_eq (.eqRefl _))
  have hz := unique_alg₃ hA hb ez (eq_of_dvd hdk)
  have hL := pos_mul hA hb
  refine (rem_eq_of_eq hL (k₁ := zero) (k₂ := quo (quo (monus y x) (succ (pred A))) (succ (pred b'))) ?_).eqSymm
  refine withEq ey fun e₁ => withEq hz fun e₂ => ?_
  ipra_lc e₁ + e₂

/-! ## The theorems at arbitrary terms -/

/-- The gcd of positive numbers is positive. -/
theorem gcd_pos {A B : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) :
    Γ ⊢[PRAAx] gcd A B ≐ succ (pred (gcd A B)) := by
  refine .orE (zero_or_succ (gcd A B)) ?_ Prf.hyp0
  exact succ_ne_zero' _ (hA.wk.eqSymm.eqTrans (gcd_eq_zero Prf.hyp0))

/-- The data shared by both theorems: `A = D a'`, `B = D b'` with `D = S (pred g)`, and `b' ≥ 1`. -/
theorem setup {A B : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A)) (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) :
    Γ ⊢[PRAAx] (A ≐ succ (pred (gcd A B)) * quo A (succ (pred (gcd A B)))) ⋏
      (B ≐ succ (pred (gcd A B)) * quo B (succ (pred (gcd A B)))) ⋏
      (quo B (succ (pred (gcd A B))) ≐ succ (pred (quo B (succ (pred (gcd A B)))))) := by
  have hg := gcd_pos (B := B) hA
  have hd := gcd_dvd_at hg
  have eA := eq_of_dvd (dvd_congr_left hg (Prf.andE₁ hd))
  have eB := eq_of_dvd (dvd_congr_left hg (Prf.andE₂ hd))
  refine .andI eA (.andI eB ?_)
  refine .orE (zero_or_succ (quo B (succ (pred (gcd A B))))) ?_ Prf.hyp0
  refine succ_ne_zero' _ (a := pred B) (hB.wk.eqSymm.eqTrans (eB.wk.eqTrans ?_))
  exact (congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)

/-- Existence. -/
theorem crt_exists_at {A B r s : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A))
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hc : Γ ⊢[PRAAx] rem r (gcd A B) ≐ rem s (gcd A B)) :
    Γ ⊢[PRAAx] Fm.ex (rem (var 0) (Syn.shift A) ≐ rem (Syn.shift r) (Syn.shift A) ⋏
      rem (var 0) (Syn.shift B) ≐ rem (Syn.shift s) (Syn.shift B)) := by
  have hg := gcd_pos (B := B) hA
  have st := setup hA hB
  have eA := Prf.andE₁ st
  have eB := Prf.andE₁ (Prf.andE₂ st)
  have hb := Prf.andE₂ (Prf.andE₂ st)
  have hD : Γ ⊢[PRAAx] succ (pred (gcd A B)) ≐ succ (pred (succ (pred (gcd A B)))) :=
    congrSucc (pred_succ _).eqSymm
  have hc' : Γ ⊢[PRAAx] rem r (succ (pred (gcd A B))) ≐ rem s (succ (pred (gcd A B))) :=
    (congrAp2 remF (.eqRefl _) hg.eqSymm).eqTrans (hc.eqTrans (congrAp2 remF (.eqRefl _) hg))
  refine .orE (bezout_at A B) ?_ ?_
  · have key := bezout_reduced₁ (U := Bezout.cur one zero (succ B) A B) (V := Bezout.cur zero one (succ B) A B) hD.wk Prf.hyp0 hg.wk eA.wk eB.wk
    have core := exists_core hA.wk hB.wk eA.wk eB.wk key hb.wk hc'.wk
    refine .exI (witness A (succ (pred (gcd A B))) (Bezout.cur one zero (succ B) A B) (pred (quo B (succ (pred (gcd A B))))) r s) ?_
    simp only [Fm.subst_and, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift]
    exact core
  · have key := bezout_reduced₂ (U := Bezout.cur one zero (succ B) A B) (V := Bezout.cur zero one (succ B) A B) hD.wk Prf.hyp0 hg.wk eA.wk eB.wk hb.wk
    have core := exists_core hA.wk hB.wk eA.wk eB.wk key hb.wk hc'.wk
    refine .exI (witness A (succ (pred (gcd A B))) (Bezout.cur one zero (succ B) A B * pred (quo B (succ (pred (gcd A B))))) (pred (quo B (succ (pred (gcd A B))))) r s) ?_
    simp only [Fm.subst_and, Fm.subst_eq, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift]
    exact core

/-- Uniqueness modulo `ℓ = a (b / g)`. -/
theorem crt_unique_at {A B x y : PTm n} (hA : Γ ⊢[PRAAx] A ≐ succ (pred A))
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hxA : Γ ⊢[PRAAx] rem x A ≐ rem y A)
    (hxB : Γ ⊢[PRAAx] rem x B ≐ rem y B) :
    Γ ⊢[PRAAx] rem x (A * quo B (gcd A B)) ≐ rem y (A * quo B (gcd A B)) := by
  have hg := gcd_pos (B := B) hA
  have st := setup hA hB
  have eA := Prf.andE₁ st
  have eB := Prf.andE₁ (Prf.andE₂ st)
  have hb := Prf.andE₂ (Prf.andE₂ st)
  have hD : Γ ⊢[PRAAx] succ (pred (gcd A B)) ≐ succ (pred (succ (pred (gcd A B)))) :=
    congrSucc (pred_succ _).eqSymm
  have hL : Γ ⊢[PRAAx] A * quo B (gcd A B) ≐ A * quo B (succ (pred (gcd A B))) :=
    congrMul (.eqRefl _) (congrAp2 quoF (.eqRefl _) hg)
  refine (congrAp2 remF (.eqRefl _) hL).eqTrans (.eqTrans ?_ (congrAp2 remF (.eqRefl _) hL.eqSymm))
  -- In either Bézout case, split on `x ≤ y` or `y ≤ x`.
  refine .orE (bezout_at A B) ?_ ?_
  · have key := bezout_reduced₁ (U := Bezout.cur one zero (succ B) A B) (V := Bezout.cur zero one (succ B) A B) hD.wk Prf.hyp0 hg.wk eA.wk eB.wk
    refine .orE (le_total x y) ?_ ?_
    · exact unique_core hA.wk.wk hB.wk.wk hD.wk.wk eA.wk.wk eB.wk.wk key.wk hb.wk.wk
        hxA.wk.wk hxB.wk.wk Prf.hyp0
    · exact (unique_core hA.wk.wk hB.wk.wk hD.wk.wk eA.wk.wk eB.wk.wk key.wk hb.wk.wk
        hxA.wk.wk.eqSymm hxB.wk.wk.eqSymm Prf.hyp0).eqSymm
  · have key := bezout_reduced₂ (U := Bezout.cur one zero (succ B) A B) (V := Bezout.cur zero one (succ B) A B) hD.wk Prf.hyp0 hg.wk eA.wk eB.wk hb.wk
    refine .orE (le_total x y) ?_ ?_
    · exact unique_core hA.wk.wk hB.wk.wk hD.wk.wk eA.wk.wk eB.wk.wk key.wk hb.wk.wk
        hxA.wk.wk hxB.wk.wk Prf.hyp0
    · exact (unique_core hA.wk.wk hB.wk.wk hD.wk.wk eA.wk.wk eB.wk.wk key.wk hb.wk.wk
        hxA.wk.wk.eqSymm hxB.wk.wk.eqSymm Prf.hyp0).eqSymm

/-! ## The closed theorems -/

/-- Existence. Variables `0 = a - 1`, `1 = b - 1`, `2 = r`, `3 = s`; under the
quantifier, `0 = x`. -/
abbrev crtExistsFormula : Fm PTm 4 :=
  rem (var 2) (gcd (succ (var 0)) (succ (var 1))) ≐ rem (var 3) (gcd (succ (var 0)) (succ (var 1))) ⟶
    Fm.ex (rem (var 0) (succ (var 1)) ≐ rem (var 3) (succ (var 1)) ⋏
      rem (var 0) (succ (var 2)) ≐ rem (var 4) (succ (var 2)))

theorem crt_exists : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 crtExistsFormula := by
  refine closeUniv 4 (.impI ?_)
  have h := crt_exists_at (Γ := ([rem (var 2) (gcd (succ (var 0)) (succ (var 1))) ≐
      rem (var 3) (gcd (succ (var 0)) (succ (var 1)))] : List (Fm PTm 4))) (A := succ (var 0)) (B := succ (var 1))
    (r := var 2) (s := var 3)
    (congrSucc (pred_succ _).eqSymm) (congrSucc (pred_succ _).eqSymm) Prf.hyp0
  simp only [Syn.shift, ConciseIPRA.PTm.subst_succ, Syn.subst_var] at h
  exact h

/-- Uniqueness modulo `ℓ = a (b / gcd(a, b))`. Variables `0 = a - 1`, `1 = b - 1`,
`2 = x`, `3 = y`. -/
abbrev crtUniqueFormula : Fm PTm 4 :=
  (rem (var 2) (succ (var 0)) ≐ rem (var 3) (succ (var 0)) ⋏
      rem (var 2) (succ (var 1)) ≐ rem (var 3) (succ (var 1))) ⟶
    rem (var 2) (succ (var 0) * quo (succ (var 1)) (gcd (succ (var 0)) (succ (var 1)))) ≐
      rem (var 3) (succ (var 0) * quo (succ (var 1)) (gcd (succ (var 0)) (succ (var 1))))

theorem crt_unique : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 crtUniqueFormula :=
  closeUniv 4 (.impI (crt_unique_at (congrSucc (pred_succ _).eqSymm) (congrSucc (pred_succ _).eqSymm)
    (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Foundations.ChineseRemainder

export_ipra Foundations.ChineseRemainder (crt_exists_at crt_unique_at gcd_pos rem_eq_of_eq)
