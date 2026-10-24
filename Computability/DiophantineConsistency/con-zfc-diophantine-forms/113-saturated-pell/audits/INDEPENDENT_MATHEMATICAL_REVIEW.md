# Independent mathematical review of the saturation candidates

Review date: 2026-10-24. This is a separate ordinary mathematical review
within the present AI collaboration, not external human peer review, a
proof-assistant certificate, or an encoded derivation in object ZFC.

## Scope and dependency boundary

I reviewed the ten-positive saturation formulas and degree proofs, the new
twelve-integer saturation formulas and degree proofs, and the retained
full-residue interpolation theorem used by the latter. I separately replayed
the literal candidate circuits as exact integer univariate polynomials. The
new equivalences are sound relative to the source interfaces explicitly
identified in the report. This review does **not** independently re-prove the
complete native-machine, compiler, or syntactic-refutation calibration chain.
Those are inherited mathematical dependencies, not new formalized endpoints.

No unresolved mathematical defect was found within the reviewed scope.

## Ten positive integers

The ordinary and direct displayed formulas agree with the graph definitions.
In particular, the ordinary denominator uses
`P1 = q^3(q-1)`, while the direct denominator uses
`P1 = q^4(q-1)`. Both have `M = P1 (q^2+1)^2 H`.
The extra direct numerator term `-(q-1)X` is essential. The corresponding
transport weights are `1+(q-1)L` and `1+q(q-1)L`.

The two-root norm recovers separate first and strong Pell squares because
`gcd(E, Df)=1`. Its zero-center exceptional case is impossible: equality of
the two squared radicals would give `delta E Df = Q V^2-1`, contradicting
`E | Q` and `E>1`. The rational auxiliary root is integral by the
adjacent-coefficient descent described below.

The sharp center `A U E` is already a strict upper bound for
`sqrt(E Df)`, because their squared difference is `E(U^2 E-1)>0`.
The stronger center gap used to absorb the direct carrier also follows
from the stated positive-domain inequalities. Completeness requires the
first-root factor in the divisibility modulus: choose the strong Pell
witness with `c^2 tau | I`, and put `U=I/tau`. This is an admissible
period choice in the retained auxiliary-completeness interface.

The independently derived exact degrees and leading homogeneous forms are:

| Candidate | Operations | Degree | Highest homogeneous form |
|---|---:|---:|---|
| Ordinary upper | 92 | 283 | `2^11 q0^149 w^29 Y^61 i^10 k0^32 (q0-F)^2` |
| Ordinary sharp | 93 | 278 | `2^10 q0^146 w^28 Y^60 i^10 k0^32 (q0-F)^2` |
| Direct upper | 98 | 258 | `2^11 q0^124 x0^29 Y^61 i^10 k0^32 (q0-F)^2` |
| Direct sharp | 99 | 254 | `2^10 q0^122 x0^28 Y^60 i^10 k0^32 (q0-F)^2` |

Here `q0=beta J`, `x0=q0+x`, and `k0=eta+zeta`; all fixed coefficient
ports have degree zero. Nonvanishing holds at the actual positive `beta`.
The Laurent expansions give a global upper bound, and these nonzero forms
attain it. Exact ray replays supply a separate literal-circuit check; they
are not used as a substitute for the global upper-bound argument.

## Twelve unrestricted integers

I checked the final formulas in
`report_parts/integer12_saturated.tex` against both current literal graphs.
The key definitions are `U=s r c^2`, `E=Dt`,
`Df=1+Delta U^2 E`, `Q=Delta^2 U^2 E`, and
`b=c-R+4 U E T`. The factor `E` in this last expression is necessary:
after square recovery the exact old coordinates are
`r_old=r tau`, `T_old=tau T`, `I=U tau`, so
`4 I T_old=4 U E T`.

### Soundness checks

1. The unconditional congruence and size bounds imply `H != 0`,
   `Delta>1`, and `E>=1`. If `U=0`, the output is `Ac^8`, and
   `Ac=H^5 pi(T+K/H)` cannot vanish at a rational input for
   `pi(x)=(x^2+3)(x^3-19)`. Thus a zero has `U != 0`, `Q>1`, and
   nonzero `V`; all radicands except the guard are positive before any
   projection is invoked.
2. A negative guard radicand would be the unique imaginary summand of a
   vanishing conjugate factor. Hence the guard is nonnegative. This gives
   the strict joint guard, and therefore both strict front inequalities.
3. Modulo 3, the squared orders of the normalized radical terms are
   `0`, `2`, and `4+v3(Dg)`. Within any nontrivial rational square class,
   the term of least 3-adic order is unique, so cancellation is impossible.
   This recovers all rational roots without presuming that they are
   integral. Coprimality of `E` and `Df` then gives their separate integer
   square roots. The zero guard case is harmless.
4. For a rational solution of `Q V^2-(Q-1)y^2=1`, write `y=a/b` in
   lowest terms. Then `b^2 | Q-1`. The transformation
   `V'=(2Q-1)V-2(Q-1)y`, `y'=(2Q-1)y-2QV` has integer `V'`, preserves
   the reduced denominator, and, after sign reflection, decreases `|V|`
   for `|V|>1`. The terminal case gives `|V|=|y|=1`, hence `b=1`.
5. A vanishing factor gives `S | Ac`, hence `H^5 | Ac`. If a prime
   divides `H` to order `e` but `zc` to smaller order `b`, the term
   `zc^5` in the expanded quintic has uniquely least valuation `5b`.
   Thus `H | zc`, recovering `H | K`. This argument permits negative
   values of `H` and `U`.

These recover precisely the stated signed source-kernel interface.
They do not assert a pointwise substitution into the old scalar polynomial.

### Completeness and quantifier order

I checked Section 6 of the retained `INTERPOLATION12.md` rather than
assuming that arbitrary divisibility follows from a generic Pell period.
For one fixed strong pair `I=psi_A(n0)`, `f=chi_A(n0)`, its corrected
period modulo `f^2` is `lambda=4 n0 f`. The valuation inequality
`v_p(I)>=v_p(n0)` gives `gcd(lambda,4 I^2) | 4I`, which makes the two
index congruences compatible for every requested residue. The Chebyshev
identity modulo **`4 S0^2`**, not merely `S0^2`, gives the necessary
factor 4. The final division yields exactly `T_old=a (mod I)`.
Consequently the theorem has the required order: choose one `I,f` first,
then realize every residue modulo that same `I`.

The saturated application takes the prescribed multiplier `N=s tau`,
so `4s tau c^2 | I`; writes `U=I/tau`; chooses an intersective residue
`a* (mod U)`; and only then requests `T_old=tau a* (mod I)`.
Since `I=tau U`, division gives an integer `T=T_old/tau` with
`T=a* (mod U)`. This proves the carrier divisibility at the unchanged
strong pair. No coprimality of `tau` and `U` is needed.

### Global degree and exact graph checks

For the rational candidate, the degree data are
`deg(U,E,Delta,Df,delta,b,V,Cy,S,Ac)=(4,34,12,54,66,39,93,252,34,45)`.
The exact cancellation `omega=fs-fc` has degree 254 and top part
`-S0^2 V0^2`. The rewritten norm intermediate has unique top part
`-4 fa0 fc0` of degree 542; all competitors have degree at most 508.
The final correction has degree 1042. Therefore the output degree is
1084, with entire highest homogeneous part

`2^1144 3^760 beta^624 j^624 w^132 v^164 h^32 s^32 r^32 c^64 T^4`.

The integral control has degree 1280 and entire highest part

`2^1320 3^880 beta^728 j^728 w^152 v^192 h^40 s^40 r^40 c^80 T^8`.

Both graphs have 123 live binary operations. The independent exact
univariate replay at all twelve variables equal to the indeterminate
and fixed ports `(2,3,5,7,11,13)` gives the same degrees and leading
coefficients `2^1768 3^760` and `2^2048 3^880`, respectively.
The release receipt is `checks/INTEGER12_SATURATED_DEGREE_RAY.json`.

