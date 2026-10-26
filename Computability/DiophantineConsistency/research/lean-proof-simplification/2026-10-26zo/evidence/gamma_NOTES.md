# Arithmetic proposals

Snapshot: `9f35798db4a63c25e435fca14d75931144657d7e`.

## A. Collapse the infinite Gamma unit family to one finite residue

Target: `CurrentControllerUnits2011.lean`, especially the three
`power_dimension_*` results (lines 48--72), factor-residue chain (86--129),
factorwise prime-coprimality chain (132--175), and final unit result (178--186).

Write

\[
d=94517=47\cdot2011,\quad p=120199,\quad M=dp=11360848883,
\quad r=2^{47},\quad B=2^{94517}.
\]

The actual source uses

\[
q_n=B^{p^n},\quad A_w=K+B^{p^w},\quad
\Gamma(w,n)=r^{977}(q_n^2-1)(1+q_nA_w).
\]

A single fixed-point fact in any monoid implies

\[
x^p=x\quad\Longrightarrow\quad x^{p^n}=x\quad(n\ge0).
\]

The proof is induction using `(p^(n+1)) = p^n*p`. Unlike an exact-order
argument, it does not classify the order or require prime hypotheses. In the
actual quotient `ZMod M`, modular exponentiation checks the premise directly.

The exact finite data are:

| Quantity modulo M | Value |
|---|---:|
| B | 10287028452 |
| r | 10653241607 |
| K | 1491904576 |
| Gamma(w,n), all w,n | 706142772 |

The K value is reconstructed by CRT from the *existing literal* kernel
residues 26 modulo 47, 1995 modulo 2011, and 114787 modulo 120199. It does not
replace K by a new kernel and does not assume a Gamma unit conclusion.

The independently reproducible finite identity

\[
(-567596732)(706142772)+(35279435)(11360848883)=1
\]

certifies coprimality. The Lean proof uses the corresponding decidable gcd
fact. Residue equality transports coprimality to every Gamma(w,n), and

\[
\gcd(a,dp)=1 \Longrightarrow
\gcd(a,d)=\gcd(a,p)=1 \Longrightarrow \gcd(a,dp^n)=1
\]

finishes the maintained conclusion. Primality and coprimality of d,p are not
needed for this last transport theorem.

Natural subtraction is handled honestly: before casting `q_n^2-1`, the
proof establishes `1 <= q_n^2` from `1 <= B`. It uses the ring subtraction
only after this guard. The independent exponents w and n are never
identified; both zero endpoints are included. Gamma positivity and safe
physical perturbation remain their own theorems.

**Validation.** `FixedPointCore.lean` and `GammaCertificate.lean` were checked
by Lean 4.32.0. The final theorem `gamma_current_from_kernel_residues` has
exactly the maintained natural Gamma expression with literal radix/base and
assumes only the three already available K-residue propositions. All printed
axiom sets are standard only. `GammaRepositoryAdapter.lean` is an explicitly
uncompiled integration sketch; the complete project was not rebuilt.

**Novelty boundary.** This is the fixed-point identity specialized to the
entire infinite Gamma family and transport through the fixed modulus dp.
It is not generic modular arithmetic cleanup, factorwise residue checking,
or deriving weaker moduli from a stronger existing theorem. The family is
proved from one new finite state certificate, with no exact-order or
Frobenius split. The audit agent found no matching Gamma/fixed-point proposal
in the 23 prior packets or five incoming manuscripts.

**Expected benefit.** The main benefit is removing mathematical dependencies
and repeated obligations from the unit proof. The verbose checked packet
includes explanatory lemmas, certificates, and compatibility examples; do
not claim its raw length is a measured repository reduction. Existing public
factor-residue and power theorems should remain wrappers until downstream
clients have been checked. Static search found their external uses in
`CurrentControllerUnits2011Checks.lean`, but that does not authorize deleting
the public interface. No runtime improvement is claimed.

## B. Replace a Pell bound's induction by a quadratic calculation

Target: `NativePellPower.sixteen_pow_bound`, lines 76--85. Put `t = 4^r`.
From r >= 2 one has t >= 16, while

\[
16^r=t^2,\qquad 2^{2r+2}=4t.
\]

The theorem is exactly `4t+2 <= t^2`, a single quadratic consequence of the
lower bound. The old custom successor induction is unnecessary. The checked
drop-in body is:

```lean
  have ht : 16 <= 4 ^ r := by
    simpa using (Nat.pow_le_pow_right (by decide : 0 < 4) hr)
  have h : 4 ^ r * 4 + 2 <= 4 ^ r * 4 ^ r := by nlinarith
  simpa [pow_add, pow_mul, <- mul_pow] using h
```

The actual Lean artifact and patch use Lean's Unicode operators. The theorem
type is unchanged; r >= 2 is retained. Its original proof body has 8 physical
lines and this one has 4, removing exactly 4 lines with no shared-helper
overhead. This is a small, validated cleanup, not a large architectural win.

Nearest excluded precedents included Pell norm/factor helpers, Pell index-six
anchors, and geometric-sum induction eliminations. None used this quadratic
substitution for the specific bound. The core theorem was checked in
isolation; applying the patch still requires a normal module/client build.
