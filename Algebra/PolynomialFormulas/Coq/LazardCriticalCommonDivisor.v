From mathcomp Require Import all_ssreflect all_algebra all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The reusable coprimality endpoint of the Figure-3 critical elimination.

    The formula-specific calculation produces two critical polynomials [A]
    and [B].  The three elimination identities have the schematic form

      Q  = B + A q,
      f' = Q + h1 A,
      f  = ell f' + h A.

    Consequently every common divisor of [A] and [B] divides both [f] and
    its derivative.  A nonconstant such divisor contradicts separability.
    Isolating this argument keeps the large Lazard coefficient certificates
    out of the elementary gcd proof and also covers the degenerate
    quadratic-remainder cases uniformly. *)
Module PolynomialFormulasLazardCriticalCommonDivisor.

Import GRing.Theory.
Local Open Scope ring_scope.

Section CommonDivisor.

Variable F : fieldType.

(** Divisibility propagates through the three critical elimination
    identities.  No degree or characteristic assumption is used here. *)
Theorem critical_common_divisor_propagates
    (f A B Q q h1 ell h u : {poly F})
    (hQ : Q = B + A * q)
    (hderiv : f^`() = Q + h1 * A)
    (hf : f = ell * f^`() + h * A)
    (huA : u %| A) (huB : u %| B) :
  (u %| f) /\ (u %| f^`()).
Proof.
have huQ : u %| Q.
  rewrite hQ.
  exact: dvdp_add huB (dvdp_mulr q huA).
have huderiv : u %| f^`().
  rewrite hderiv.
  exact: dvdp_add huQ (dvdp_mull h1 huA).
have huf : u %| f.
  rewrite hf.
  exact: dvdp_add (dvdp_mull ell huderiv) (dvdp_mull h huA).
by split.
Qed.

(** A nonconstant common divisor is an explicit obstruction to
    coprimality. *)
Lemma nonconstant_common_divisor_not_coprime
    (p q u : {poly F})
    (usize : (1 < size u)%N)
    (hup : u %| p) (huq : u %| q) :
  ~~ coprimep p q.
Proof.
apply/negP=> hcoprime.
move: hcoprime; rewrite coprimep_def=> /eqP hgcd.
have hugcd : u %| gcdp p q.
  by rewrite dvdp_gcd hup huq.
have hgcd0 : gcdp p q != 0.
  by rewrite -size_poly_gt0 hgcd.
have hsize := dvdp_leq hgcd0 hugcd.
rewrite hgcd in hsize.
move: usize.
by rewrite ltnNge hsize.
Qed.

(** Formula-independent separability contradiction used at the end of the
    Lazard determinant proof. *)
Theorem not_separable_of_critical_common_divisor
    (f A B Q q h1 ell h u : {poly F})
    (hQ : Q = B + A * q)
    (hderiv : f^`() = Q + h1 * A)
    (hf : f = ell * f^`() + h * A)
    (usize : (1 < size u)%N)
    (huA : u %| A) (huB : u %| B) :
  ~~ separable_poly f.
Proof.
have [huf huderiv] := critical_common_divisor_propagates
  hQ hderiv hf huA huB.
rewrite unlock /separable_poly.
exact: nonconstant_common_divisor_not_coprime usize huf huderiv.
Qed.

End CommonDivisor.

Print Assumptions critical_common_divisor_propagates.
Print Assumptions not_separable_of_critical_common_divisor.

End PolynomialFormulasLazardCriticalCommonDivisor.
