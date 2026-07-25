/-
  SetTheory.PAHF.RiemannHypothesis

  A first-order Peano-arithmetic sentence whose standard interpretation is a
  classical arithmetic reformulation of the Riemann Hypothesis.
-/

import PAHF.PASyntax

namespace SetTheory
namespace PA
namespace Formula
namespace RiemannHypothesis

/-! ## Small formula combinators -/

/-- Object-language negation. -/
def notF (phi : Formula) : Formula :=
  imp phi bot

/-- Shift every free variable in a PA term through `k` freshly-bound variables. -/
def shiftTerm (k : Nat) (t : Term) : Term :=
  Term.rename (fun n => n + k) t

/-- Shift every free variable in a PA formula through `k` freshly-bound variables. -/
def shiftFormula (k : Nat) (phi : Formula) : Formula :=
  rename (fun n => n + k) phi

/-- `shiftTerm` fixes closed numerals. -/
theorem shiftTerm_numeral (k n : Nat) :
    shiftTerm k (Term.numeral n) = Term.numeral n :=
  Term.rename_numeral _ n

/-- Term-parametric divisibility. -/
def dvdTermAt (a b : Term) : Formula :=
  ex (eq (Term.mul (Term.rename Nat.succ a) (Term.var 0))
    (Term.rename Nat.succ b))

/-- Term-parametric evenness. -/
def evenTermAt (t : Term) : Formula :=
  ex (eq (Term.rename Nat.succ t)
    (Term.add (Term.var 0) (Term.var 0)))

/-- Term-parametric oddness. -/
def oddTermAt (t : Term) : Formula :=
  ex (eq (Term.rename Nat.succ t)
    (Term.succ (Term.add (Term.var 0) (Term.var 0))))

/-- Term-parametric nonzeroness, expressed as being a successor. -/
def nonzeroTermAt (t : Term) : Formula :=
  ex (eq (Term.rename Nat.succ t) (Term.succ (Term.var 0)))

/--
`properRemainderWitnessAt value modulus` says that `value` has a nonzero
remainder modulo `modulus`.

When `modulus` is known positive this is equivalent to `modulus ∤ value`, but
the positive remainder is much friendlier as a PA certificate than a negated
divisibility statement.
-/
def properRemainderWitnessAt (value modulus : Term) : Formula :=
  ex (ex (and
    (ltTermAt (Term.succ (Term.var 1)) (shiftTerm 2 modulus))
    (eq (shiftTerm 2 value)
      (Term.add (Term.mul (Term.var 0) (shiftTerm 2 modulus))
        (Term.succ (Term.var 1))))))

/--
Term-parametric primality.

The predicate uses bounded trial division: `p` is greater than `1`, and every
candidate divisor `d` with `1 < d < p` leaves a nonzero remainder when `p` is
divided by `d`.
-/
def primeTermAt (p : Term) : Formula :=
  and (ltTermAt (Term.numeral 1) p)
    (all (imp
      (and
        (ltTermAt (Term.numeral 1) (Term.var 0))
        (ltTermAt (Term.var 0) (shiftTerm 1 p)))
      (properRemainderWitnessAt (shiftTerm 1 p) (Term.var 0))))

/--
Term-parametric squarefreeness, bounded to primes `p <= n`.

For positive `n`, any prime square divisor of `n` must have `p <= n`; this is
the squarefree condition needed by the Mertens trace.  As above, non-divisibility
is certified by a nonzero remainder.
-/
def squarefreeTermAt (n : Term) : Formula :=
  all (imp
    (and
      (ltTermAt (Term.var 0) (Term.succ (shiftTerm 1 n)))
      (primeTermAt (Term.var 0)))
    (properRemainderWitnessAt
      (shiftTerm 1 n)
      (Term.mul (Term.var 0) (Term.var 0))))

/-! ## PA certificates for small arithmetic facts -/

theorem term_subst_upSubst_instTerm_rename_two_succ_exact
    (t u : Term) :
    Term.subst (Term.upSubst (instTerm u))
      (Term.rename Nat.succ (Term.rename Nat.succ t)) =
    Term.rename Nat.succ t := by
  have hrename : Term.rename Nat.succ (Term.rename Nat.succ t) =
      Term.rename (fun n : Nat => n + 1 + 1) t := by
    rw [Term.rename_comp]
  rw [hrename]
  exact term_subst_upSubst_instTerm_rename_two_succ t u

theorem term_subst_two_witnesses_rename_two_succ_add
    (t pred quot : Term) :
    Term.subst (instTerm quot)
      (Term.subst (Term.upSubst (instTerm pred))
        (Term.rename (fun n : Nat => n + 2) t)) = t := by
  have htwo : Term.rename (fun n : Nat => n + 2) t =
      Term.rename Nat.succ (Term.rename Nat.succ t) := by
    simpa using (Term.rename_comp t Nat.succ Nat.succ).symm
  rw [htwo]
  rw [term_subst_upSubst_instTerm_rename_two_succ_exact]
  exact term_subst_instTerm_rename_succ t quot

theorem term_subst_up2_instTerm_rename_three_succ_add
    (t u : Term) :
    Term.subst (Term.upSubst (Term.upSubst (instTerm u)))
      (Term.rename Nat.succ (Term.rename (fun n : Nat => n + 2) t)) =
    Term.rename Nat.succ (Term.rename Nat.succ t) := by
  have htwo : Term.rename (fun n : Nat => n + 2) t =
      Term.rename Nat.succ (Term.rename Nat.succ t) := by
    simpa using (Term.rename_comp t Nat.succ Nat.succ).symm
  rw [htwo]
  rw [Term.subst_rename_succ_up]
  rw [term_subst_upSubst_instTerm_rename_two_succ_exact]

theorem subst_properRemainder_body
    (pred quot value modulus : Term) :
    subst (instTerm quot)
      (subst (Term.upSubst (instTerm pred))
        (and
          (ltTermAt (Term.succ (Term.var 1)) (shiftTerm 2 modulus))
          (eq (shiftTerm 2 value)
            (Term.add (Term.mul (Term.var 0) (shiftTerm 2 modulus))
              (Term.succ (Term.var 1)))))) =
    and
      (ltTermAt (Term.succ pred) modulus)
      (eq value (Term.add (Term.mul quot modulus) (Term.succ pred))) := by
  simp [ltTermAt, shiftTerm, subst, instTerm, Term.subst, Term.rename,
    Term.upSubst, term_subst_upSubst_instTerm_rename_two_succ_exact,
    term_subst_instTerm_rename_succ,
    term_subst_two_witnesses_rename_two_succ_add,
    term_subst_up2_instTerm_rename_three_succ_add]

/--
Transport a concrete Euclidean decomposition `q * m + r = v` through a proof
that an open modulus term denotes `m`.  Both remainder-certificate constructors
below use this same arithmetic core.
-/
theorem BProv_Ax_s_euclideanDecomposition_of_modEq
    {G : List Formula} {modulus : Term} {r v m q : Nat}
    (hmod : BProv Ax_s G (eq modulus (Term.numeral m)))
    (hdiv : q * m + r = v) :
    BProv Ax_s G
      (eq (Term.add (Term.mul (Term.numeral q) modulus) (Term.numeral r))
        (Term.numeral v)) := by
  have hmul : BProv Ax_s G
      (eq (Term.mul (Term.numeral q) modulus) (Term.numeral (q * m))) :=
    BProv_eqTrans
      (BProv_eq_congr_mul_right (B := Ax_s) (G := G) (Term.numeral q) hmod)
      (BProv_weaken_nil (G := G) (BProv_Ax_s_mulNumerals q m))
  have hadd : BProv Ax_s G
      (eq (Term.add (Term.mul (Term.numeral q) modulus) (Term.numeral r))
        (Term.numeral (q * m + r))) :=
    BProv_eqTrans
      (BProv_eq_congr_add_left (B := Ax_s) (G := G) (Term.numeral r) hmul)
      (BProv_weaken_nil (G := G) (BProv_Ax_s_addNumerals (q * m) r))
  simpa [hdiv] using hadd

theorem BProv_Ax_s_properRemainderWitnessAt_numeral_of_modEq
    {G : List Formula} {modulus : Term} {r v m q : Nat}
    (hmod : BProv Ax_s G (eq modulus (Term.numeral m)))
    (hr : r < m) (hrpos : 0 < r) (hdiv : q * m + r = v) :
    BProv Ax_s G (properRemainderWitnessAt (Term.numeral v) modulus) := by
  let pred := r - 1
  have hnumPred : Term.succ (Term.numeral pred) = Term.numeral r := by
    subst pred
    cases r with
    | zero => cases hrpos
    | succ r => simp [Term.numeral]
  have hltClosed : BProv Ax_s G (ltTermAt (Term.numeral r) (Term.numeral m)) := by
    simpa [ltTermAt, Term.rename] using
      (BProv_Ax_s_ltConst_closed (G := G) hr)
  have hltR : BProv Ax_s G
      (ltTermAt (Term.succ (Term.numeral pred)) (Term.numeral m)) := by
    simpa [hnumPred] using hltClosed
  have hlt : BProv Ax_s G
      (ltTermAt (Term.succ (Term.numeral pred)) modulus) :=
    BProv_ltTermAt_of_eq_right (B := Ax_s) (G := G)
      (BProv_eqSym hmod) hltR
  have hsum : BProv Ax_s G
      (eq
        (Term.add (Term.mul (Term.numeral q) modulus)
          (Term.succ (Term.numeral pred)))
        (Term.numeral v)) := by
    simpa [hnumPred] using
      (BProv_Ax_s_euclideanDecomposition_of_modEq
        (G := G) (modulus := modulus) (r := r) (v := v) (m := m) (q := q)
        hmod hdiv)
  have hbodyQ : BProv Ax_s G
      (subst (instTerm (Term.numeral q))
        (subst (Term.upSubst (instTerm (Term.numeral pred)))
          (and
            (ltTermAt (Term.succ (Term.var 1)) (shiftTerm 2 modulus))
            (eq (shiftTerm 2 (Term.numeral v))
              (Term.add (Term.mul (Term.var 0) (shiftTerm 2 modulus))
                (Term.succ (Term.var 1))))))) := by
    simpa [subst_properRemainder_body] using
      BProv_andI hlt (BProv_eqSym hsum)
  have hexQ : BProv Ax_s G
      (subst (instTerm (Term.numeral pred))
        (ex (and
          (ltTermAt (Term.succ (Term.var 1)) (shiftTerm 2 modulus))
          (eq (shiftTerm 2 (Term.numeral v))
            (Term.add (Term.mul (Term.var 0) (shiftTerm 2 modulus))
              (Term.succ (Term.var 1))))))) := by
    exact BProv_exI (B := Ax_s) (G := G)
      (a := subst (Term.upSubst (instTerm (Term.numeral pred)))
          (and
            (ltTermAt (Term.succ (Term.var 1)) (shiftTerm 2 modulus))
            (eq (shiftTerm 2 (Term.numeral v))
              (Term.add (Term.mul (Term.var 0) (shiftTerm 2 modulus))
                (Term.succ (Term.var 1)))))) (t := Term.numeral q) hbodyQ
  simpa [properRemainderWitnessAt] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := ex (and
        (ltTermAt (Term.succ (Term.var 1)) (shiftTerm 2 modulus))
        (eq (shiftTerm 2 (Term.numeral v))
          (Term.add (Term.mul (Term.var 0) (shiftTerm 2 modulus))
            (Term.succ (Term.var 1)))))) (t := Term.numeral pred) hexQ)

theorem BProv_Ax_s_contradiction_one_lt_of_lt_two
    {G : List Formula} {d : Term}
    (h1d : BProv Ax_s G (ltTermAt (Term.numeral 1) d))
    (hd2 : BProv Ax_s G (ltTermAt d (Term.numeral 2))) :
    BProv Ax_s G bot := by
  have hcases : BProv Ax_s G
      (or (ltTermAt d (Term.numeral 1)) (eq d (Term.numeral 1))) := by
    simpa [Term.numeral] using
      (BProv_Ax_s_ltTermAt_succ_right_cases
        (G := G) (s := d) (t := Term.numeral 1) hd2)
  have hltBranch : BProv Ax_s (ltTermAt d (Term.numeral 1) :: G) bot := by
    have h1d' : BProv Ax_s (ltTermAt d (Term.numeral 1) :: G)
        (ltTermAt (Term.numeral 1) d) :=
      BProv_context_cons (B := Ax_s) (a := ltTermAt d (Term.numeral 1)) h1d
    have hd1 : BProv Ax_s (ltTermAt d (Term.numeral 1) :: G)
        (ltTermAt d (Term.numeral 1)) :=
      BProv_ass (B := Ax_s) (by simp)
    have hleD0 : BProv Ax_s (ltTermAt d (Term.numeral 1) :: G)
        (leTermAt d Term.zero) := by
      simpa [Term.numeral] using
        (BProv_Ax_s_leTermAt_of_ltTermAt_succ_right
          (G := ltTermAt d (Term.numeral 1) :: G)
          (s := d) (t := Term.zero) hd1)
    have hle01 : BProv Ax_s (ltTermAt d (Term.numeral 1) :: G)
        (leTermAt Term.zero (Term.numeral 1)) :=
      BProv_Ax_s_leTermAt_zero_left
        (G := ltTermAt d (Term.numeral 1) :: G) (Term.numeral 1)
    exact BProv_Ax_s_ltTermAt_leTermAt_bot h1d'
      (BProv_Ax_s_leTermAt_trans hleD0 hle01)
  have heqBranch : BProv Ax_s (eq d (Term.numeral 1) :: G) bot := by
    have h1d' : BProv Ax_s (eq d (Term.numeral 1) :: G)
        (ltTermAt (Term.numeral 1) d) :=
      BProv_context_cons (B := Ax_s) (a := eq d (Term.numeral 1)) h1d
    have hdeq : BProv Ax_s (eq d (Term.numeral 1) :: G)
        (eq d (Term.numeral 1)) :=
      BProv_ass (B := Ax_s) (by simp)
    have hlt11 : BProv Ax_s (eq d (Term.numeral 1) :: G)
        (ltTermAt (Term.numeral 1) (Term.numeral 1)) :=
      BProv_ltTermAt_of_eq_right
        (B := Ax_s) (G := eq d (Term.numeral 1) :: G) hdeq h1d'
    exact BProv_Ax_s_ltTermAt_leTermAt_bot hlt11
      (BProv_Ax_s_leTermAt_refl
        (G := eq d (Term.numeral 1) :: G) (Term.numeral 1))
  exact BProv_orE hcases hltBranch heqBranch

/--
Discharge any goal in a context whose head asserts `d < 2` while `1 < d` is
already provable: the two bounds are contradictory.
-/
theorem BProv_Ax_s_of_head_lt_two
    {G : List Formula} {d : Term} {a : Formula}
    (h1d : BProv Ax_s G (ltTermAt (Term.numeral 1) d)) :
    BProv Ax_s (ltTermAt d (Term.numeral 2) :: G) a :=
  BProv_botE
    (BProv_Ax_s_contradiction_one_lt_of_lt_two
      (BProv_context_cons (B := Ax_s) (a := ltTermAt d (Term.numeral 2)) h1d)
      (BProv_ass (B := Ax_s) (by simp)))

/--
Remainder certificate against modulus `var 0` when the context head pins
`var 0` to the numeral `m`.
-/
theorem BProv_Ax_s_properRemainderWitness_var_of_head_eq
    {G : List Formula} {r v m q : Nat}
    (hr : r < m) (hrpos : 0 < r) (hdiv : q * m + r = v) :
    BProv Ax_s (eq (Term.var 0) (Term.numeral m) :: G)
      (properRemainderWitnessAt (Term.numeral v) (Term.var 0)) :=
  BProv_Ax_s_properRemainderWitnessAt_numeral_of_modEq
    (G := eq (Term.var 0) (Term.numeral m) :: G)
    (modulus := Term.var 0) (r := r) (v := v) (m := m) (q := q)
    (BProv_ass (B := Ax_s) (by simp)) hr hrpos hdiv

theorem BProv_Ax_s_square_of_eq_numeral
    {G : List Formula} {p : Term} {a : Nat}
    (hp : BProv Ax_s G (eq p (Term.numeral a))) :
    BProv Ax_s G (eq (Term.mul p p) (Term.numeral (a * a))) := by
  exact BProv_eqTrans (BProv_eq_congr_mul hp hp)
    (BProv_weaken_nil (G := G) (BProv_Ax_s_mulNumerals a a))

/--
Shared equality-branch body of the small squarefreeness certificates: when the
context head pins `var 0` to the numeral `a` and `0 < v < a * a`, the value
`v` leaves the proper remainder `v` modulo `var 0 * var 0`.
-/
theorem BProv_Ax_s_properRemainderWitness_square_of_head_eq
    {G : List Formula} {a v : Nat} (hvpos : 0 < v) (hv : v < a * a) :
    BProv Ax_s (eq (Term.var 0) (Term.numeral a) :: G)
      (properRemainderWitnessAt (Term.numeral v)
        (Term.mul (Term.var 0) (Term.var 0))) := by
  have hpEq : BProv Ax_s (eq (Term.var 0) (Term.numeral a) :: G)
      (eq (Term.var 0) (Term.numeral a)) :=
    BProv_ass (B := Ax_s) (by simp)
  exact BProv_Ax_s_properRemainderWitnessAt_numeral_of_modEq
    (modulus := Term.mul (Term.var 0) (Term.var 0))
    (r := v) (v := v) (m := a * a) (q := 0)
    (BProv_Ax_s_square_of_eq_numeral hpEq) hv hvpos (by simp)

/-- The opened bounded-divisor hypothesis of `primeTermAt` at a numeral. -/
def primeDivisorHyp (p : Nat) : Formula :=
  and (ltTermAt (Term.numeral 1) (Term.var 0))
    (ltTermAt (Term.var 0) (Term.numeral p))

theorem BProv_Ax_s_primeDivisorHyp_one_lt {G : List Formula} {p : Nat} :
    BProv Ax_s (primeDivisorHyp p :: G)
      (ltTermAt (Term.numeral 1) (Term.var 0)) := by
  have hhyp : BProv Ax_s (primeDivisorHyp p :: G) (primeDivisorHyp p) :=
    BProv_ass (B := Ax_s) (by simp)
  simpa [primeDivisorHyp] using BProv_andE1 hhyp

theorem BProv_Ax_s_primeDivisorHyp_lt {G : List Formula} {p : Nat} :
    BProv Ax_s (primeDivisorHyp p :: G)
      (ltTermAt (Term.var 0) (Term.numeral p)) := by
  have hhyp : BProv Ax_s (primeDivisorHyp p :: G) (primeDivisorHyp p) :=
    BProv_ass (B := Ax_s) (by simp)
  simpa [primeDivisorHyp] using BProv_andE2 hhyp

/--
Shared scaffold of the small primality certificates: `primeTermAt` at a
numeral follows from the closed bound `1 < p` plus the opened bounded-divisor
obligation, taken in a context holding `primeDivisorHyp p`.
-/
theorem BProv_Ax_s_primeTermAt_numeral {p : Nat} (hp : 1 < p)
    (hbody : BProv Ax_s [primeDivisorHyp p]
      (properRemainderWitnessAt (Term.numeral p) (Term.var 0))) :
    BProv Ax_s [] (primeTermAt (Term.numeral p)) := by
  have hgt1 : BProv Ax_s [] (ltTermAt (Term.numeral 1) (Term.numeral p)) := by
    simpa [ltTermAt, Term.rename] using
      (BProv_Ax_s_ltConst_closed (G := []) hp)
  have hforall : BProv Ax_s []
      (all (imp
        (and (ltTermAt (Term.numeral 1) (Term.var 0))
          (ltTermAt (Term.var 0) (shiftTerm 1 (Term.numeral p))))
        (properRemainderWitnessAt (shiftTerm 1 (Term.numeral p))
          (Term.var 0)))) := by
    refine BProv_allI_of_sentences (B := Ax_s) Ax_s_sentences ?_
    rw [shiftTerm_numeral]
    exact BProv_impI hbody
  simpa [primeTermAt] using BProv_andI hgt1 hforall

theorem BProv_Ax_s_prime_two :
    BProv Ax_s [] (primeTermAt (Term.numeral 2)) := by
  refine BProv_Ax_s_primeTermAt_numeral (by decide) ?_
  exact BProv_botE
    (BProv_Ax_s_contradiction_one_lt_of_lt_two
      BProv_Ax_s_primeDivisorHyp_one_lt BProv_Ax_s_primeDivisorHyp_lt)

theorem BProv_Ax_s_prime_three :
    BProv Ax_s [] (primeTermAt (Term.numeral 3)) := by
  refine BProv_Ax_s_primeTermAt_numeral (by decide) ?_
  have hcases : BProv Ax_s [primeDivisorHyp 3]
      (or (ltTermAt (Term.var 0) (Term.numeral 2))
        (eq (Term.var 0) (Term.numeral 2))) := by
    simpa [Term.numeral] using
      (BProv_Ax_s_ltTermAt_succ_right_cases
        (G := [primeDivisorHyp 3]) (s := Term.var 0) (t := Term.numeral 2)
        BProv_Ax_s_primeDivisorHyp_lt)
  exact BProv_orE hcases
    (BProv_Ax_s_of_head_lt_two BProv_Ax_s_primeDivisorHyp_one_lt)
    (BProv_Ax_s_properRemainderWitness_var_of_head_eq
      (r := 1) (q := 1) (by decide) (by decide) (by decide))

/-- The opened bounded-prime hypothesis of `squarefreeTermAt` at a numeral. -/
def squarefreePrimeHyp (n : Nat) : Formula :=
  and (ltTermAt (Term.var 0) (Term.numeral (n + 1)))
    (primeTermAt (Term.var 0))

theorem BProv_Ax_s_squarefreePrimeHyp_lt_bound {G : List Formula} {n : Nat} :
    BProv Ax_s (squarefreePrimeHyp n :: G)
      (ltTermAt (Term.var 0) (Term.numeral (n + 1))) := by
  have hhyp : BProv Ax_s (squarefreePrimeHyp n :: G) (squarefreePrimeHyp n) :=
    BProv_ass (B := Ax_s) (by simp)
  simpa [squarefreePrimeHyp] using BProv_andE1 hhyp

theorem BProv_Ax_s_squarefreePrimeHyp_one_lt {G : List Formula} {n : Nat} :
    BProv Ax_s (squarefreePrimeHyp n :: G)
      (ltTermAt (Term.numeral 1) (Term.var 0)) := by
  have hhyp : BProv Ax_s (squarefreePrimeHyp n :: G) (squarefreePrimeHyp n) :=
    BProv_ass (B := Ax_s) (by simp)
  have hprime : BProv Ax_s (squarefreePrimeHyp n :: G)
      (primeTermAt (Term.var 0)) := by
    simpa [squarefreePrimeHyp] using BProv_andE2 hhyp
  simpa [primeTermAt] using BProv_andE1 hprime

/--
Shared scaffold of the small squarefreeness certificates: `squarefreeTermAt`
at a numeral reduces to the opened square-remainder obligation, taken in a
context holding `squarefreePrimeHyp n`.
-/
theorem BProv_Ax_s_squarefreeTermAt_numeral {n : Nat}
    (hbody : BProv Ax_s [squarefreePrimeHyp n]
      (properRemainderWitnessAt (Term.numeral n)
        (Term.mul (Term.var 0) (Term.var 0)))) :
    BProv Ax_s [] (squarefreeTermAt (Term.numeral n)) := by
  have hforall : BProv Ax_s []
      (all (imp
        (and (ltTermAt (Term.var 0)
            (Term.succ (shiftTerm 1 (Term.numeral n))))
          (primeTermAt (Term.var 0)))
        (properRemainderWitnessAt (shiftTerm 1 (Term.numeral n))
          (Term.mul (Term.var 0) (Term.var 0))))) := by
    refine BProv_allI_of_sentences (B := Ax_s) Ax_s_sentences ?_
    rw [shiftTerm_numeral]
    exact BProv_impI hbody
  simpa [squarefreeTermAt] using hforall

theorem BProv_Ax_s_squarefree_one :
    BProv Ax_s [] (squarefreeTermAt (Term.numeral 1)) := by
  refine BProv_Ax_s_squarefreeTermAt_numeral ?_
  exact BProv_botE
    (BProv_Ax_s_contradiction_one_lt_of_lt_two
      BProv_Ax_s_squarefreePrimeHyp_one_lt
      BProv_Ax_s_squarefreePrimeHyp_lt_bound)

theorem BProv_Ax_s_squarefree_two :
    BProv Ax_s [] (squarefreeTermAt (Term.numeral 2)) := by
  refine BProv_Ax_s_squarefreeTermAt_numeral ?_
  have hcases : BProv Ax_s [squarefreePrimeHyp 2]
      (or (ltTermAt (Term.var 0) (Term.numeral 2))
        (eq (Term.var 0) (Term.numeral 2))) := by
    simpa [Term.numeral] using
      (BProv_Ax_s_ltTermAt_succ_right_cases
        (G := [squarefreePrimeHyp 2]) (s := Term.var 0) (t := Term.numeral 2)
        BProv_Ax_s_squarefreePrimeHyp_lt_bound)
  exact BProv_orE hcases
    (BProv_Ax_s_of_head_lt_two BProv_Ax_s_squarefreePrimeHyp_one_lt)
    (BProv_Ax_s_properRemainderWitness_square_of_head_eq
      (by decide) (by decide))

theorem BProv_Ax_s_squarefree_three :
    BProv Ax_s [] (squarefreeTermAt (Term.numeral 3)) := by
  refine BProv_Ax_s_squarefreeTermAt_numeral ?_
  have hcases4 : BProv Ax_s [squarefreePrimeHyp 3]
      (or (ltTermAt (Term.var 0) (Term.numeral 3))
        (eq (Term.var 0) (Term.numeral 3))) := by
    simpa [Term.numeral] using
      (BProv_Ax_s_ltTermAt_succ_right_cases
        (G := [squarefreePrimeHyp 3]) (s := Term.var 0) (t := Term.numeral 3)
        BProv_Ax_s_squarefreePrimeHyp_lt_bound)
  have hlt3Branch : BProv Ax_s
      (ltTermAt (Term.var 0) (Term.numeral 3) :: [squarefreePrimeHyp 3])
      (properRemainderWitnessAt (Term.numeral 3)
        (Term.mul (Term.var 0) (Term.var 0))) := by
    have hp3 : BProv Ax_s
        (ltTermAt (Term.var 0) (Term.numeral 3) :: [squarefreePrimeHyp 3])
        (ltTermAt (Term.var 0) (Term.numeral 3)) :=
      BProv_ass (B := Ax_s) (by simp)
    have hcases3 : BProv Ax_s
        (ltTermAt (Term.var 0) (Term.numeral 3) :: [squarefreePrimeHyp 3])
        (or (ltTermAt (Term.var 0) (Term.numeral 2))
          (eq (Term.var 0) (Term.numeral 2))) := by
      simpa [Term.numeral] using
        (BProv_Ax_s_ltTermAt_succ_right_cases
          (G := ltTermAt (Term.var 0) (Term.numeral 3) ::
            [squarefreePrimeHyp 3])
          (s := Term.var 0) (t := Term.numeral 2) hp3)
    exact BProv_orE hcases3
      (BProv_Ax_s_of_head_lt_two
        (BProv_context_cons (B := Ax_s)
          (a := ltTermAt (Term.var 0) (Term.numeral 3))
          BProv_Ax_s_squarefreePrimeHyp_one_lt))
      (BProv_Ax_s_properRemainderWitness_square_of_head_eq
        (by decide) (by decide))
  exact BProv_orE hcases4 hlt3Branch
    (BProv_Ax_s_properRemainderWitness_square_of_head_eq
      (by decide) (by decide))

theorem BProv_Ax_s_remTermTermAt_numeral_of_modEq
    {G : List Formula} {modulus : Term} {r v m q : Nat}
    (hmod : BProv Ax_s G (eq modulus (Term.numeral m)))
    (hr : r < m) (hdiv : q * m + r = v) :
    BProv Ax_s G (remTermTermAt (Term.numeral r) (Term.numeral v) modulus) := by
  have hltClosed : BProv Ax_s G (ltTermAt (Term.numeral r) (Term.numeral m)) := by
    simpa [ltTermAt, Term.rename] using BProv_Ax_s_ltConst_closed (G := G) hr
  have hlt : BProv Ax_s G (ltTermAt (Term.numeral r) modulus) :=
    BProv_ltTermAt_of_eq_right (B := Ax_s) (G := G) (BProv_eqSym hmod) hltClosed
  have hsum : BProv Ax_s G
      (eq (Term.add (Term.mul (Term.numeral q) modulus) (Term.numeral r))
        (Term.numeral v)) :=
    BProv_Ax_s_euclideanDecomposition_of_modEq hmod hdiv
  exact BProv_Ax_s_remTermTermAt_of_eq_add_mul_terms
    (G := G) (rem := Term.numeral r) (value := Term.numeral v)
    (modulus := modulus) (quotient := Term.numeral q) hlt (BProv_eqSym hsum)

theorem BProv_Ax_s_betaModTermTerm_numeral_eq
    {G : List Formula} (step idx : Nat) :
    BProv Ax_s G
      (eq (betaModTermTerm (Term.numeral step) (Term.numeral idx))
        (Term.numeral (BetaModulus step idx))) :=
  BProv_eqSym (BProv_Ax_s_betaModTermTerm_numeral (G := G) step idx)

theorem BProv_Ax_s_betaTermTermAt_numeral_of_entry
    {G : List Formula} {out code step idx : Nat}
    (hentry : BetaEntry code step idx out) :
    BProv Ax_s G (betaTermTermAt (Term.numeral out) (Term.numeral code)
      (Term.numeral step) (Term.numeral idx)) :=
  BProv_Ax_s_betaTermTermAt_numeral_entry (G := G) hentry

theorem BProv_Ax_s_betaTermTermAtConstIdx_numeral_of_entry
    {G : List Formula} {out code step idx : Nat}
    (hentry : BetaEntry code step idx out) :
    BProv Ax_s G (betaTermTermAtConstIdx (Term.numeral out) (Term.numeral code)
      (Term.numeral step) idx) :=
  BProv_Ax_s_betaTermTermAtConstIdx_of_beta
    (BProv_Ax_s_betaTermTermAt_numeral_of_entry (G := G) hentry)

theorem BProv_Ax_s_not_lt_zero
    {G : List Formula} {t : Term}
    (hlt : BProv Ax_s G (ltTermAt t Term.zero)) : BProv Ax_s G bot :=
  BProv_Ax_s_ltTermAt_leTermAt_bot hlt
    (BProv_Ax_s_leTermAt_zero_left (G := G) t)

theorem BProv_Ax_s_eq_zero_of_lt_one
    {G : List Formula} {t : Term}
    (hlt : BProv Ax_s G (ltTermAt t (Term.numeral 1))) :
    BProv Ax_s G (eq t Term.zero) := by
  have hleT0 : BProv Ax_s G (leTermAt t Term.zero) := by
    simpa [Term.numeral] using
      (BProv_Ax_s_leTermAt_of_ltTermAt_succ_right
        (G := G) (s := t) (t := Term.zero) hlt)
  have hle0T : BProv Ax_s G (leTermAt Term.zero t) :=
    BProv_Ax_s_leTermAt_zero_left (G := G) t
  exact BProv_Ax_s_eq_of_leTermAt_leTermAt hleT0 hle0T

theorem BProv_Ax_s_even_zero {G : List Formula} :
    BProv Ax_s G (evenTermAt (Term.numeral 0)) := by
  have hzeroAdd : BProv Ax_s G (eq (Term.add Term.zero Term.zero) Term.zero) :=
    BProv_weaken_nil (G := G) (BProv_Ax_s_zero_add_term Term.zero)
  have hbody : BProv Ax_s G
      (subst (instTerm Term.zero)
        (eq (Term.rename Nat.succ (Term.numeral 0))
          (Term.add (Term.var 0) (Term.var 0)))) := by
    simpa [subst, instTerm, Term.subst, Term.rename, Term.numeral] using
      BProv_eqSym hzeroAdd
  simpa [evenTermAt] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := eq (Term.rename Nat.succ (Term.numeral 0))
        (Term.add (Term.var 0) (Term.var 0))) (t := Term.zero) hbody)

theorem BProv_Ax_s_odd_one {G : List Formula} :
    BProv Ax_s G (oddTermAt (Term.numeral 1)) := by
  have hzeroAdd : BProv Ax_s G (eq (Term.add Term.zero Term.zero) Term.zero) :=
    BProv_weaken_nil (G := G) (BProv_Ax_s_zero_add_term Term.zero)
  have hsucc : BProv Ax_s G
      (eq (Term.succ (Term.add Term.zero Term.zero)) (Term.succ Term.zero)) :=
    BProv_eq_congr_succ hzeroAdd
  have hbody : BProv Ax_s G
      (subst (instTerm Term.zero)
        (eq (Term.rename Nat.succ (Term.numeral 1))
          (Term.succ (Term.add (Term.var 0) (Term.var 0))))) := by
    simpa [subst, instTerm, Term.subst, Term.rename, Term.numeral] using
      BProv_eqSym hsucc
  simpa [oddTermAt] using
    (BProv_exI (B := Ax_s) (G := G)
      (a := eq (Term.rename Nat.succ (Term.numeral 1))
        (Term.succ (Term.add (Term.var 0) (Term.var 0))))
      (t := Term.zero) hbody)

/-! ## Prime-factorization parity -/

/--
`completePrimeFactorizationTraceAt n len code step` says that `code, step`
beta-code a finite sequence `a_0, ..., a_len` such that `a_0 = n`,
`a_len = 1`, and each transition divides out one prime:
`a_i = p * a_{i+1}` for some prime `p`.

The parity of `len` is therefore the parity of the total number of prime
factors of `n` in the standard model.
-/
def completePrimeFactorizationTraceAt
    (n len code step : Term) : Formula :=
  and (betaTermTermAtConstIdx n code step 0)
    (and (betaTermTermAt (Term.numeral 1) code step len)
      (all (imp (ltTermAt (Term.var 0) (shiftTerm 1 len))
        (ex (and (primeTermAt (Term.var 0))
          (ex (and
            (betaTermTermAt (Term.var 0)
              (shiftTerm 3 code) (shiftTerm 3 step)
              (Term.succ (Term.var 2)))
            (betaTermTermAt
              (Term.mul (Term.var 1) (Term.var 0))
              (shiftTerm 3 code) (shiftTerm 3 step)
              (Term.var 2)))))))))

/-- Trace-based even-length complete prime factorization. -/
def factorizationEvenTraceTermAt (n : Term) : Formula :=
  ex (ex (ex
    (and
      (completePrimeFactorizationTraceAt
        (shiftTerm 3 n) (Term.var 2) (Term.var 1) (Term.var 0))
      (evenTermAt (Term.var 2)))))

/--
`n` has an even-length complete prime factorization.

The closed base case for `1` is included explicitly as a PA-friendly redundant
certificate; the trace disjunct is the general definition.
-/
def factorizationEvenTermAt (n : Term) : Formula :=
  or (eq n (Term.numeral 1)) (factorizationEvenTraceTermAt n)

/-- Trace-based odd-length complete prime factorization. -/
def factorizationOddTraceTermAt (n : Term) : Formula :=
  ex (ex (ex
    (and
      (completePrimeFactorizationTraceAt
        (shiftTerm 3 n) (Term.var 2) (Term.var 1) (Term.var 0))
      (oddTermAt (Term.var 2)))))

/--
`n` has an odd-length complete prime factorization.

The closed base cases for `2` and `3` are included explicitly as PA-friendly
redundant certificates; the trace disjunct is the general definition.
-/
def factorizationOddTermAt (n : Term) : Formula :=
  or (eq n (Term.numeral 2))
    (or (eq n (Term.numeral 3)) (factorizationOddTraceTermAt n))

/-- The Möbius value of `n` is `+1`: squarefree with even factorization length. -/
def mobiusPositiveTermAt (n : Term) : Formula :=
  and (squarefreeTermAt n) (factorizationEvenTermAt n)

/-- The Möbius value of `n` is `-1`: squarefree with odd factorization length. -/
def mobiusNegativeTermAt (n : Term) : Formula :=
  and (squarefreeTermAt n) (factorizationOddTermAt n)

theorem BProv_Ax_s_factorizationEven_one :
    BProv Ax_s [] (factorizationEvenTermAt (Term.numeral 1)) := by
  exact BProv_orI1 (B := Ax_s) (G := [])
    (b := factorizationEvenTraceTermAt (Term.numeral 1))
    (BProv_eqRefl (B := Ax_s) (G := []) (Term.numeral 1))

theorem BProv_Ax_s_factorizationOdd_two :
    BProv Ax_s [] (factorizationOddTermAt (Term.numeral 2)) := by
  exact BProv_orI1 (B := Ax_s) (G := [])
    (b := or (eq (Term.numeral 2) (Term.numeral 3))
      (factorizationOddTraceTermAt (Term.numeral 2)))
    (BProv_eqRefl (B := Ax_s) (G := []) (Term.numeral 2))

theorem BProv_Ax_s_factorizationOdd_three :
    BProv Ax_s [] (factorizationOddTermAt (Term.numeral 3)) := by
  exact BProv_orI2 (B := Ax_s) (G := [])
    (a := eq (Term.numeral 3) (Term.numeral 2))
    (BProv_orI1 (B := Ax_s) (G := [])
      (b := factorizationOddTraceTermAt (Term.numeral 3))
      (BProv_eqRefl (B := Ax_s) (G := []) (Term.numeral 3)))

theorem BProv_Ax_s_mobiusPositive_one :
    BProv Ax_s [] (mobiusPositiveTermAt (Term.numeral 1)) :=
  BProv_andI BProv_Ax_s_squarefree_one BProv_Ax_s_factorizationEven_one

theorem BProv_Ax_s_mobiusNegative_two :
    BProv Ax_s [] (mobiusNegativeTermAt (Term.numeral 2)) :=
  BProv_andI BProv_Ax_s_squarefree_two BProv_Ax_s_factorizationOdd_two

theorem BProv_Ax_s_mobiusNegative_three :
    BProv Ax_s [] (mobiusNegativeTermAt (Term.numeral 3)) :=
  BProv_andI BProv_Ax_s_squarefree_three BProv_Ax_s_factorizationOdd_three

/-! ## Prefix-count traces for the Mertens function -/

/--
One guarded transition of two synchronized beta-coded traces.  The guard and
the two next-value terms live under the current-value witnesses
`leftCur = var 1` and `rightCur = var 0`; the trace index is `var 2`.

Keeping the shared four-entry beta plumbing here makes other paired trace
relations depend only on their guard and update expressions.
-/
def pairedBetaTraceStepAt
    (leftCode leftStep rightCode rightStep : Term)
    (guard : Formula) (leftNext rightNext : Term) : Formula :=
  let leftCode' := shiftTerm 2 leftCode
  let leftStep' := shiftTerm 2 leftStep
  let rightCode' := shiftTerm 2 rightCode
  let rightStep' := shiftTerm 2 rightStep
  let leftCur := Term.var 1
  let rightCur := Term.var 0
  let i' := Term.var 2
  ex (ex (and guard
    (and
      (betaTermTermAt leftCur leftCode' leftStep' i')
      (and
        (betaTermTermAt leftNext leftCode' leftStep' (Term.succ i'))
        (and
          (betaTermTermAt rightCur rightCode' rightStep' i')
          (betaTermTermAt rightNext rightCode' rightStep'
            (Term.succ i')))))))

/--
The update relation for the two cumulative counts in the Mertens function.

At loop index `i`, the integer being inspected is `i+1`.  The positive count is
incremented when `mu(i+1)=+1`, the negative count is incremented when
`mu(i+1)=-1`, and both counts are preserved when the Möbius value is `0`.
-/
def mertensCountStepAt
    (posCode posStep negCode negStep : Term) : Formula :=
  let posCur := Term.var 1
  let negCur := Term.var 0
  let k' := Term.succ (Term.var 2)
  let positiveUpdate :=
    pairedBetaTraceStepAt posCode posStep negCode negStep
      (mobiusPositiveTermAt k') (Term.succ posCur) negCur
  let negativeUpdate :=
    pairedBetaTraceStepAt posCode posStep negCode negStep
      (mobiusNegativeTermAt k') posCur (Term.succ negCur)
  let zeroUpdate :=
    pairedBetaTraceStepAt posCode posStep negCode negStep
      (and (notF (mobiusPositiveTermAt k'))
        (notF (mobiusNegativeTermAt k')))
      posCur negCur
  or positiveUpdate (or negativeUpdate zeroUpdate)

/--
`mertensCountsTraceAt n pos neg ...` says that `pos` and `neg` are the counts
of `k <= n` for which `mu(k)=+1` and `mu(k)=-1`, respectively.
-/
def mertensCountsTraceAt
    (n pos neg posCode posStep negCode negStep : Term) : Formula :=
  and (betaTermTermAtConstIdx (Term.numeral 0) posCode posStep 0)
    (and (betaTermTermAtConstIdx (Term.numeral 0) negCode negStep 0)
      (and (betaTermTermAt pos posCode posStep n)
        (and (betaTermTermAt neg negCode negStep n)
          (all (imp (ltTermAt (Term.var 0) (shiftTerm 1 n))
            (mertensCountStepAt
              (shiftTerm 1 posCode) (shiftTerm 1 posStep)
              (shiftTerm 1 negCode) (shiftTerm 1 negStep)))))))

/-- Existential trace wrapper for Mertens positive/negative prefix counts. -/
def mertensCountsTraceExistsAt (n pos neg : Term) : Formula :=
  ex (ex (ex (ex
    (mertensCountsTraceAt (shiftTerm 4 n) (shiftTerm 4 pos)
      (shiftTerm 4 neg) (Term.var 3) (Term.var 2)
      (Term.var 1) (Term.var 0)))))

/-- Closed base-case certificate for a Mertens positive/negative count pair. -/
def mertensCountsBaseAt (n pos neg : Term)
    (nValue posValue negValue : Nat) : Formula :=
  and (eq n (Term.numeral nValue))
    (and (eq pos (Term.numeral posValue))
      (eq neg (Term.numeral negValue)))

/--
Existential wrapper for Mertens positive/negative prefix counts.

The first three standard values are included explicitly as redundant base-case
certificates.  The final disjunct is the general beta-coded trace definition.
-/
def mertensCountsAt (n pos neg : Term) : Formula :=
  or (mertensCountsBaseAt n pos neg 1 1 0)
    (or (mertensCountsBaseAt n pos neg 2 1 1)
      (or (mertensCountsBaseAt n pos neg 3 1 2)
        (mertensCountsTraceExistsAt n pos neg)))

/-- Closed PA statement: `M(1)=1`, represented by counts `pos=1`, `neg=0`. -/
def mertensOneEqOneStatement : Formula :=
  and (mertensCountsAt (Term.numeral 1) (Term.numeral 1) (Term.numeral 0))
    (eq (Term.numeral 1) (Term.add (Term.numeral 0) (Term.numeral 1)))

/-- Closed PA statement: `M(2)=0`, represented by equal counts `pos=neg=1`. -/
def mertensTwoEqZeroStatement : Formula :=
  and (mertensCountsAt (Term.numeral 2) (Term.numeral 1) (Term.numeral 1))
    (eq (Term.numeral 1) (Term.numeral 1))

/-- Closed PA statement: `M(3)=-1`, represented by `neg=pos+1`. -/
def mertensThreeEqNegOneStatement : Formula :=
  and (mertensCountsAt (Term.numeral 3) (Term.numeral 1) (Term.numeral 2))
    (eq (Term.numeral 2) (Term.add (Term.numeral 1) (Term.numeral 1)))

/-- Closed numeral instances of `mertensCountsBaseAt` follow by reflexivity. -/
theorem BProv_Ax_s_mertensCountsBase_numerals {G : List Formula}
    (n pos neg : Nat) :
    BProv Ax_s G (mertensCountsBaseAt
      (Term.numeral n) (Term.numeral pos) (Term.numeral neg) n pos neg) :=
  BProv_andI (BProv_eqRefl (B := Ax_s) (G := G) (Term.numeral n))
    (BProv_andI (BProv_eqRefl (B := Ax_s) (G := G) (Term.numeral pos))
      (BProv_eqRefl (B := Ax_s) (G := G) (Term.numeral neg)))

theorem BProv_Ax_s_mertensCounts_one :
    BProv Ax_s [] (mertensCountsAt
      (Term.numeral 1) (Term.numeral 1) (Term.numeral 0)) :=
  BProv_orI1 (B := Ax_s) (G := [])
    (BProv_Ax_s_mertensCountsBase_numerals 1 1 0)

theorem BProv_Ax_s_mertensCounts_two :
    BProv Ax_s [] (mertensCountsAt
      (Term.numeral 2) (Term.numeral 1) (Term.numeral 1)) :=
  BProv_orI2 (B := Ax_s) (G := [])
    (a := mertensCountsBaseAt
      (Term.numeral 2) (Term.numeral 1) (Term.numeral 1) 1 1 0)
    (BProv_orI1 (B := Ax_s) (G := [])
      (BProv_Ax_s_mertensCountsBase_numerals 2 1 1))

theorem BProv_Ax_s_mertensCounts_three :
    BProv Ax_s [] (mertensCountsAt
      (Term.numeral 3) (Term.numeral 1) (Term.numeral 2)) :=
  BProv_orI2 (B := Ax_s) (G := [])
    (a := mertensCountsBaseAt
      (Term.numeral 3) (Term.numeral 1) (Term.numeral 2) 1 1 0)
    (BProv_orI2 (B := Ax_s) (G := [])
      (a := mertensCountsBaseAt
        (Term.numeral 3) (Term.numeral 1) (Term.numeral 2) 2 1 1)
      (BProv_orI1 (B := Ax_s) (G := [])
        (BProv_Ax_s_mertensCountsBase_numerals 3 1 2)))

theorem BProv_Ax_s_mertens_one_eq_one :
    BProv Ax_s [] mertensOneEqOneStatement := by
  have hadd : BProv Ax_s []
      (eq (Term.add (Term.numeral 0) (Term.numeral 1)) (Term.numeral 1)) :=
    BProv_Ax_s_addNumerals 0 1
  exact BProv_andI BProv_Ax_s_mertensCounts_one (BProv_eqSym hadd)

theorem BProv_Ax_s_mertens_two_eq_zero :
    BProv Ax_s [] mertensTwoEqZeroStatement :=
  BProv_andI BProv_Ax_s_mertensCounts_two
    (BProv_eqRefl (B := Ax_s) (G := []) (Term.numeral 1))

theorem BProv_Ax_s_mertens_three_eq_neg_one :
    BProv Ax_s [] mertensThreeEqNegOneStatement := by
  have hadd : BProv Ax_s []
      (eq (Term.add (Term.numeral 1) (Term.numeral 1)) (Term.numeral 2)) :=
    BProv_Ax_s_addNumerals 1 1
  exact BProv_andI BProv_Ax_s_mertensCounts_three (BProv_eqSym hadd)

/-! ## Power traces and the arithmetized RH growth bound -/

/-- Beta-coded exponentiation trace: `out = base ^ exp`. -/
def powTraceAt (base exp out code step : Term) : Formula :=
  and (betaTermTermAtConstIdx (Term.numeral 1) code step 0)
    (and (betaTermTermAt out code step exp)
      (all (imp (ltTermAt (Term.var 0) (shiftTerm 1 exp))
        (ex (and
          (betaTermTermAt (Term.var 0) (shiftTerm 2 code)
            (shiftTerm 2 step) (Term.var 1))
          (betaTermTermAt
            (Term.mul (Term.var 0) (shiftTerm 2 base))
            (shiftTerm 2 code) (shiftTerm 2 step)
            (Term.succ (Term.var 1))))))))

/-- Existential wrapper for `out = base ^ exp`. -/
def powRelAt (base exp out : Term) : Formula :=
  ex (ex (powTraceAt (shiftTerm 2 base) (shiftTerm 2 exp)
    (shiftTerm 2 out) (Term.var 1) (Term.var 0)))

/--
The integer inequality corresponding to
`|M(n)|^(2*q) <= C * n^(q+1)`.
-/
def mertensPowerBoundAt (n q C pos neg : Term) : Formula :=
  let diff := Term.var 0
  ex (and
    (or
      (eq (Term.add (shiftTerm 1 pos) diff) (shiftTerm 1 neg))
      (eq (Term.add (shiftTerm 1 neg) diff) (shiftTerm 1 pos)))
    (ex (and
      (powRelAt (Term.var 1)
        (Term.mul (Term.numeral 2) (shiftTerm 2 q))
        (Term.var 0))
      (ex (and
        (powRelAt (shiftTerm 3 n)
          (Term.succ (shiftTerm 3 q))
          (Term.var 0))
        (leTermAt (Term.var 1)
          (Term.mul (shiftTerm 3 C) (Term.var 0))))))))

/-- One `n`-instance of the arithmetized Mertens growth bound. -/
def mertensBoundAt (n q C : Term) : Formula :=
  ex (ex (and
    (mertensCountsAt (shiftTerm 2 n) (Term.var 1) (Term.var 0))
    (mertensPowerBoundAt
      (shiftTerm 2 n) (shiftTerm 2 q) (shiftTerm 2 C)
      (Term.var 1) (Term.var 0))))

/--
The PA sentence:

`forall q > 0, exists C, forall n,
  |M(n)|^(2*q) <= C * n^(q+1)`.

For each positive rational epsilon, choose `q` with `1/(2*q) < epsilon`.
Thus this is the integer-power form of the classical Littlewood/Mertens
criterion `M(n) = O(n^(1/2+epsilon))` for every epsilon > 0.
-/
def mertensRiemannHypothesisBody : Formula :=
  all (imp (nonzeroAt 0)
    (ex (all (mertensBoundAt (Term.var 0) (Term.var 2) (Term.var 1)))))

/-- The sealed PA sentence form of `mertensRiemannHypothesisBody`. -/
def mertensRiemannHypothesisSentence : Formula :=
  sealPA mertensRiemannHypothesisBody

theorem mertensRiemannHypothesisSentence_sentence :
    Sentence mertensRiemannHypothesisSentence :=
  sealPA_sentence _

end RiemannHypothesis
end Formula
end PA
end SetTheory
