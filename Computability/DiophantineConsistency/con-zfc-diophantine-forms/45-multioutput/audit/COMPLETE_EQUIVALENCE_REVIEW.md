# Independent audit of the complete simultaneous-output constructions

## Verdict and scope

The current nine-positive and ten-unrestricted-integer constructions pass this independent audit. No unresolved local mathematical defect was found after the nine-variable source estimate was explicitly extended from `g < 2 b B^W` to `g < 4 b B^W`. The latter is the bound actually supplied by `ratio_sound` with `Gcap = 32 b B^W`.

This verdict is conditional on the explicitly inherited compiler/K215 and Pell/Lucas arithmetic theorems. It is a mathematical review plus exact and finite implementation checks, not a new kernel formalization, a proof of consistency, or an unbounded search for solutions. Upstream programs were not executed. The three audit programs in this directory were independently authored and read mathematical data only.

Current metrics are:

* Nine positive unknowns: 788 live binary arithmetic gates, total degree 129875980.
* Nine nonnegative unknowns: 791 gates, same degree.
* Ten unrestricted integer unknowns: 936 gates, total degree 237526776.

These are different domains. Neither nine-variable equation is claimed to have the same zero-existence property over all integers.

## Source and coordinate contract

The fixed parent is the 31-positive-variable, 22-quadratic-equation system60 of package 31, pinned in the deliverable to commit `22e75dd6b87b1b199bb08c778d7cf075ae5aae08`. The four ports beta, K0, MC, MF are taken together from that package's complete compiler tuple. MF means the already shifted `MF_source`, not an unshifted payload.

Two coordinate changes must not be confused:

1. The system60 transport coordinate satisfies `z_old = z + 1` relative to the earlier parent.
2. Every positive system60 coordinate is replaced by a nonnegative coordinate plus one when forming the quadratic source rows.

The first change is NOT a bijection of arbitrary positive assignments. Its equivalence is on zero sets and uses inherited Pell/compiler consequences. The pinned `review/sources/31-sun10/quartic31/QUARTIC60_PROOF.md` proves, on each old zero, `C>0`, `F<q`, `X=wq=2^R`, and `R>3q`. Thus `w>q>F` and

    (z_old-1)(q-1) = (K0+w) C - F > 0.

Consequently `z_old>=2`, so the inverse shift stays positive. This inherited positivity argument is indispensable; a symbolic residual identity alone would not prove completeness.

The source row order is 1,2,3,4,6,...,22,5. The final row has constant coefficient 1 after the nonnegative shift. Thus the source code has leading coefficient 2, and the zero vector is not a common zero. The latter is needed to make the encoded g positive during completeness.

## Simultaneous coefficient extraction

The 31 positive weights, together with zero as a padding weight, have 528 distinct unordered pair sums. This proves injectivity for every monomial of total degree at most two. With W=799, spacing 1599, and targets H_j=1599j, each row's reversed coefficient block lies in `[H_j-2W,H_j]`; these intervals are disjoint.

Multiplication by `(1+sum z_i t^w_i)^2` gives target coefficient exactly twice the appropriate quadratic residual. The factorial coefficient `(2-|alpha|)! product alpha_i!` is essential: it inverts the degree-two multinomial factor. Another row cannot contribute at a target, since its target separation exceeds 2W. Off-target products may overlap and are permitted; the coefficient bound applies to the whole product, not just target coefficients.

The coefficient positivity and carry arguments do not assume that arbitrary g is already a valid encoding. The low-block carry mask first forces precisely the permitted base-B positions and digits less than b. Only then is the quadratic source polynomial interpreted. This order closes the malformed-witness loophole.

## Nine-variable source-to-ratio interface

The source has unconditional positivity for all inputs in its prescribed mixed domain: D(B)>0, N>=8, R>=N, b<=N and b<=R. These statements must hold before ratio soundness is invoked, not only on encoded source zeros. The large fixed floor supplies them.

With `Gcap=32 b B^W`, ratio soundness gives `8g<Gcap`, hence `g<4 b B^W`. Since g is integral, `1+g<=4 b B^W`. The displayed coefficient bound and `b>=4096 M` suffice for `g<N0`, `0<J<N1`, and `S,T<N`. No circuit change was needed for the four-cap correction.

When b is a power of two, N is a power of two. The three-block identity for R gives a central-binomial divisibility test equivalent to carry-free addition of S and T. Splitting the low and high blocks is valid because a carry across their boundary is itself forbidden. After the low mask enforces encoding, division of the two even high blocks by two is legitimate and converts the selected digits to equality tests. Target digits force all 22 quadratic residuals to zero.

Conversely a common nonnegative source zero is nonzero, so an arbitrarily large power-of-two b gives positive g and the stronger `32g<Gcap` needed for ratio completeness. The imported ratio statements do not require the former special exponent pattern `5^j`; the new positional source is proved separately.

## Nine-variable finalizer

All of u, a0, a1 and their strict majorants are positive on arbitrary prescribed-domain assignments. The inequalities `a0<V0^2` and `a1<V1^2` follow from explicit Pell-defect identities. The linear bound `Mdiv=Q+H` is sufficient because

    0 < v/u = Q/J + (H-C)/F < Q+H-1.

The case m=0 is excluded separately: then Omega=0 while Theta/u is strictly positive. For nonzero Omega, a zero of the quartic norm gives a rational signed sum of the two square roots. It cannot be zero, since that would force a positive integer radicand below one. Rationalization therefore proves both roots rational and hence integral. The strict majorants make the reconstructed integer Z at least `2 Mdiv+1`; positivity of the left side then forces m>0, and integrality forces u to divide v. Conversely integral roots and divisibility produce an allowed nonnegative n. No denominator is silently divided by zero.

## Ten-integer finalizer and arbitrary signs

The retained Sun tail handles unrestricted integer inputs rather than assuming positivity. The homogeneous polynomial Theta is nonzero whenever its odd parameter S is nonzero, because the associated one-variable polynomial has no rational root. Thus Sigma=0 cannot be a zero of the final equation. This excludes xi=0 and z=0 before later divisions and Pell arguments.

The first radicand's square condition, together with `b=1+3f` and z nonzero, supplies b positive square and O positive. Its absolute value is greater than one; the exceptional values 0 and +/-1 are excluded explicitly. The recursively separated weights then prevent cancellation under a highest-changed-sign Galois automorphism. This argument remains valid for negative radicands and dependent square classes; it does not falsely assume square-class independence. A rational weighted root sum therefore yields integral roots of all three integer radicands.

The divisibility implication uses valuations: Sigma divides Theta forces S to divide T. The reverse implication is not merely a generic congruence choice: it uses the retained Sun interpolation theorem to prescribe y while making xi a multiple of z. Likewise completeness of the first square condition uses a Pell unit whose second coordinate is divisible by b. These are explicitly inherited arithmetic dependencies, not consequences of finite testing.

The source proof establishes exactly the positivity, size, congruence and cap assumptions needed by the Sun bridge. In particular the power-of-two coefficient radix has even exponent, is 1 modulo 3, and `b=1+3f`; therefore the source X is divisible by 3. The actual source and the unchanged tail were compared directly, not inferred from similarity to the old quartic construction.

## Independent checks and precise evidential strength

`check_complete_equations.py` compares each complete emitted circuit with separately written source sums and finalizer formulas. It evaluates 105 assignments per family over three primes, using reductions of the actual four large fixed integers. It also checks acyclicity, every node's liveness, variable lists, named interfaces and operation counts. These are regression checks, not a symbolic identity proof.

`check_degree_certificates.py` verifies the exact telescope resolving `V1^2-a1` and the following inner-square identity symbolically. It checks 120 direct/certificate evaluations per family. Total-degree upper bounds on the cancellation-resolved circuit agree with a nonzero highest diagonal coefficient at each of three primes. Thus the degree claims do not rely on an uncorrected syntactic maximum at a cancellation. The nine exact leading coefficient is also explained in the mathematical proof as `2^2050`.

`check_fixed_bindings.py` independently evaluates coefficient recipes as full integers, verifies the four raw-port hashes and the active parent hash, and verifies all 17 materialized Sun fixed leaves exactly against the recipes. The maximum absolute bit length among all 136 quadratic coefficients is 2134926. The nine recipe maximum is the same, below the stated 2134927 exponent bound. Sixty further finite checks verify the positive/nonnegative circuit translation.

JSON outputs record the performed checks. The coefficient ports are fixed integers, not hidden existential variables. Arithmetic metrics charge every live binary addition, subtraction and multiplication, including scalar multiplication, and allow reusable registers. Large fixed coefficient bit lengths remain a separate metric.

## Residual limitations and final delta audit

The equivalence to Con(ZFC) still relies on the pinned compiler correctness and ratio/Sun theorems. The new full mathematical source and finalizer arguments have been reviewed here but not translated into an end-to-end Lean or Rocq proof.

The final frozen Sun instance uses radix exponent 2134940, reduced from the provisional 2140032. Its evenness and the strict bound `beta_sun > 4 max|c| * 32^2` are checked on actual integer coefficients. The shared homogeneous row evaluation followed by Horner evaluation reduces the provisional 954 gates to 936. Every one of the 136 transformed monomial exponents is checked exactly against the direct source exponent. All three independent audit programs were rerun after the author froze the 936-gate instance and regenerated its 17 payloads. They pass; the exact degree is unchanged. Its nonzero top diagonal coefficients modulo 101, 1009 and 1000003 are respectively 54, 453 and 982432. These final data supersede the provisional 954-gate metric.
