import IPRADerivations.DiophantineNumberTheory.ModularCertificate
import IPRADerivations.DiophantineNumberTheory.DigitCode

/-!
# Polynomial systems and the modular certificate

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Theorem `thm:modular`: "Let `F_1, …, F_s` be
homogeneous integer polynomials. If none of the unimodular residue vectors modulo `m` satisfies all equations
`F_i(x̄) ≡ 0 (mod m)`, their projective zero locus has no rational point."

A polynomial in `N` variables is encoded by `K` monomials with natural coefficients `C(k)` and exponents
`E(k, i)`: `P(v) = ∑_{k<K} C(k) ∏_{i<N} v_i^{E(k,i)}` (`polyEval`). An integer polynomial is a pair `P⁺ − P⁻`
with natural coefficients, and `F(v) = 0` reads `P⁺(v) = P⁻(v)`.

* `pw_congr_mod`, `mono_congr`, `poly_congr`: congruent vectors have congruent polynomial values;
* `modular_cert`: a primitive natural solution `v` of `P⁺ = P⁻` reduces to a residue vector `w = v mod m` that is
  unimodular and satisfies `P⁺(w) ≡ P⁻(w) (mod m)`. Contrapositively, a modulus with no unimodular residue
  solution excludes every primitive (natural) solution.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.PolyModular

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.ModularCertificate (unimodular rem_mul_congr2 sum_congr_mod
  prod_congr_mod shift_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.GcdList (gv)
open LeanProofs.IPRA.DiophantineNumberTheory.DigitCode (rem_small)
open LeanProofs.IPRA.Combinatorics.LegendreDigits (dm)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- `x ≡ y (mod M)` gives `x^e ≡ y^e (mod M)`. -/
theorem pw_congr_mod {x y M : PTm k} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (h : Γ ⊢[PRAAx] rem x M ≐ rem y M) (e : PTm k) :
    Γ ⊢[PRAAx] rem (pw x e) M ≐ rem (pw y e) M :=
  Foundations.ChineseRemainder.rem_pow_congr hM h e

/-- The factor `v_i^{E(k, i)}`, over `0 = i`, `1 = ⟨k, x⟩`. -/
abbrev monoB (E V : PTm 2) : PTm 2 := pw (inst2 V (var 0) (sndT (var 1))) (inst2 E (fstT (var 1)) (var 0))

/-- The term `C(k) ∏_{i<N} v_i^{E(k, i)}`, over `0 = k`, `1 = ⟨N, x⟩`. -/
abbrev termB (C E V : PTm 2) : PTm 2 :=
  inst2 C (var 0) (sndT (var 1)) * ap2 (prodF (monoB E V)) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

/-- `P(v) = ∑_{k<K} C(k) ∏_{i<N} v_i^{E(k, i)}`. -/
abbrev polyEval (C E V : PTm 2) (K N x : PTm k) : PTm k := ap2 (sumF (termB C E V)) K (pairT N x)

theorem monoB_at (E V : PTm 2) (i k' x : PTm k) :
    Γ ⊢[PRAAx] inst2 (monoB E V) i (pairT k' x) ≐ pw (inst2 V i x) (inst2 E k' i) := by
  have h : inst2 (monoB E V) i (pairT k' x) = pw (inst2 V i (sndT (pairT k' x))) (inst2 E (fstT (pairT k' x)) i) := by
    rw [show inst2 (monoB E V) i (pairT k' x) = Syn.subst ![i, pairT k' x] (monoB E V) from rfl]; simp
  rw [h]
  exact congrPw (congrInst2 V (.eqRefl _) (snd_pair _ _)) (congrInst2 E (fst_pair _ _) (.eqRefl _))

theorem termB_at (C E V : PTm 2) (k' N x : PTm k) :
    Γ ⊢[PRAAx] inst2 (termB C E V) k' (pairT N x) ≐
      inst2 C k' x * ap2 (prodF (monoB E V)) N (pairT k' x) := by
  have h : inst2 (termB C E V) k' (pairT N x) =
      inst2 C k' (sndT (pairT N x)) * ap2 (prodF (monoB E V)) (fstT (pairT N x)) (pairT k' (sndT (pairT N x))) := by
    rw [show inst2 (termB C E V) k' (pairT N x) = Syn.subst ![k', pairT N x] (termB C E V) from rfl]; simp
  rw [h]
  exact congrMul (congrInst2 C (.eqRefl _) (snd_pair _ _))
    (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _)))

/-- Congruent vectors give congruent monomials. -/
theorem mono_congr (E V W : PTm 2) {N x M : PTm k} (k' : PTm k) (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      rem (inst2 V (var 0) (Syn.shift x)) (Syn.shift M) ≐ rem (inst2 W (var 0) (Syn.shift x)) (Syn.shift M))) :
    Γ ⊢[PRAAx] rem (ap2 (prodF (monoB E V)) N (pairT k' x)) M ≐ rem (ap2 (prodF (monoB E W)) N (pairT k' x)) M := by
  refine prod_congr_mod _ _ hM (.allI (.impI ?_))
  have e : Syn.shift (pairT k' x) = pairT (Syn.shift k') (Syn.shift x) := by simp [Syn.shift]
  rw [e]
  have c := pw_congr_mod (shift_pos hM).wk (Prf.impE h.allOpen.wk Prf.hyp0) (inst2 E (Syn.shift k') (var 0))
  exact (congrAp2 remF (monoB_at E V _ _ _) (.eqRefl _)).eqTrans
    (c.eqTrans (congrAp2 remF (monoB_at E W _ _ _) (.eqRefl _)).eqSymm)

/-- Congruent vectors give congruent polynomial values. -/
theorem poly_congr (C E V W : PTm 2) {K N x M : PTm k} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      rem (inst2 V (var 0) (Syn.shift x)) (Syn.shift M) ≐ rem (inst2 W (var 0) (Syn.shift x)) (Syn.shift M))) :
    Γ ⊢[PRAAx] rem (polyEval C E V K N x) M ≐ rem (polyEval C E W K N x) M := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (Syn.shift N)) ⟶
      rem (inst2 V (var 0) (Syn.shift (Syn.shift x))) (Syn.shift (Syn.shift M)) ≐
        rem (inst2 W (var 0) (Syn.shift (Syn.shift x))) (Syn.shift (Syn.shift M))) := by
    have e := h.shift
    simpa [Fm.shift, Syn.shift, Syn.subst_subst, Syn.up_succ, Syn.up_zero, Syn.shift_var] using e
  refine sum_congr_mod _ _ hM (.allI (.impI ?_))
  have e : Syn.shift (pairT N x) = pairT (Syn.shift N) (Syn.shift x) := by simp [Syn.shift]
  rw [e]
  have m := mono_congr E V W (var 0) ((shift_pos hM).wk : (lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) ⊢[PRAAx] _)
    (hs.wk : (lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) ⊢[PRAAx] _)
  have r := rem_mul_congr2 ((shift_pos hM).wk : (lt (var 0) (Syn.shift K) :: Γ.map Fm.shift) ⊢[PRAAx] _) (.eqRefl (rem (inst2 C (var 0) (Syn.shift x)) (Syn.shift M))) m
  exact (congrAp2 remF (termB_at C E V _ _ _) (.eqRefl _)).eqTrans
    (r.eqTrans (congrAp2 remF (termB_at C E W _ _ _) (.eqRefl _)).eqSymm)

/-- `thm:modular` for natural coordinates, the equation: a solution `v` of `P⁺ = P⁻` reduces to a residue vector
`w = v mod M` with `P⁺(w) ≡ P⁻(w) (mod M)`. -/
theorem modular_cert (Cp Cm E V W : PTm 2) {K N x M : PTm k} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hW : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      inst2 W (var 0) (Syn.shift x) ≐ rem (inst2 V (var 0) (Syn.shift x)) (Syn.shift M)))
    (hP : Γ ⊢[PRAAx] polyEval Cp E V K N x ≐ polyEval Cm E V K N x) :
    Γ ⊢[PRAAx] rem (polyEval Cp E W K N x) M ≐ rem (polyEval Cm E W K N x) M := by
  have cong : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      rem (inst2 V (var 0) (Syn.shift x)) (Syn.shift M) ≐ rem (inst2 W (var 0) (Syn.shift x)) (Syn.shift M)) := by
    refine .allI (.impI ?_)
    have hMs := (shift_pos hM).wk (ψ := lt (var 0) (Syn.shift N))
    have w := Prf.impE hW.allOpen.wk Prf.hyp0
    have lt1 := Prf.andE₂ (dm hMs (inst2 V (var 0) (Syn.shift x)))
    exact (rem_small hMs lt1).eqSymm.eqTrans (congrAp2 remF w.eqSymm (.eqRefl _))
  have p1 := (poly_congr Cp E V W (K := K) hM cong).eqSymm
  have p2 := poly_congr Cm E V W (K := K) hM cong
  exact p1.eqTrans ((congrAp2 remF hP (.eqRefl _)).eqTrans p2)

/-- `thm:modular` for natural coordinates, the residues: if `gcd(v) = 1`, every positive common divisor `d` of `M`
and all residues `w_i = v_i mod M` is `1`. -/
theorem residue_unimodular (V W : PTm 2) {N x M d : PTm k} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hg : Γ ⊢[PRAAx] gv V N x ≐ one)
    (hW : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      inst2 W (var 0) (Syn.shift x) ≐ rem (inst2 V (var 0) (Syn.shift x)) (Syn.shift M)))
    (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hdm : Γ ⊢[PRAAx] dvd d M)
    (hdw : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ dvd (Syn.shift d) (inst2 W (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] d ≐ one :=
  unimodular hg hM hd hdm (.allI (.impI (dvd_congr (Prf.impE hW.allOpen.wk Prf.hyp0) (Prf.impE hdw.allOpen.wk Prf.hyp0))))

end LeanProofs.IPRA.DiophantineNumberTheory.PolyModular
