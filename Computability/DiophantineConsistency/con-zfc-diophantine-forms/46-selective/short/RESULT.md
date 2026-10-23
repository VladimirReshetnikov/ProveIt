# A 74-operation degree-68 local equation

Pinned source: ProveIt `124c07c0b77a9e20e84676514d8b1ff78536ea3f`, `Computability/DiophantineConsistency/circuits/p75_sos.json` and `SHORT_SYSTEM.md`. This is a new ordinary proof of a local equivalence, not a new checked Lean theorem or an independent proof of the native compiler.

Use precisely the fifteen positive unknowns, four fixed coefficient ports, whole coefficient binding, and polynomial abbreviations of the pinned P75. Write its six factors as `N0,N1,Na,Nk,Nt,Ns`. The new equation is

`N0^2 + Na^2 + Ns^2 + (N1*Nk*Nt-1)^2 - 3 = 0`.

The complete factor definitions are supplied locally in `UPSTREAM_SHORT_SYSTEM.md` and the literal evaluator in `p74_norm_minima.json`. Its fixed leaves bind to `coefficients/COEFFICIENT_BINDING.json`, with four exact binary payloads under that directory's `coefficients/` subdirectory. The aliases are `beta -> beta`, `K0 -> K`, `MC -> MC`, and `MF -> MF_source`. This is the **whole package-36 tuple**, with native base `2^1012115`; `MF_source` already includes the shift by `B-1`. It is separate from the main report's package-31 tuple. The local `SOURCES.json` records the pinned commit, Git blob SHA1, SHA256, byte size, and payload hashes for each inherited file.

The local zero-equivalence proof below is uniform for arbitrary fixed integer coefficient ports with `beta>0`. In particular `q=beta*J+1>=2` on the positive domain, so all positivity and nonsquare-discriminant premises used below hold independently of the remaining coefficient values. The ordinary compiler semantics are inherited only for the coherent package-36 tuple supplied here.

## Nonvanishing before any equation is assumed

1. Put `n=X*Y^2`. Since `n>0`, the integer `n(n+1)` lies strictly between `n^2` and `(n+1)^2`. It is not a rational square. With `k>0`, therefore `N0=tau^2-n(n+1)k^2` cannot vanish.
2. `Delta=(a+2)^2-1` lies strictly between `(a+1)^2` and `(a+2)^2` for `a>0`, so it is not a rational square. Because `i*c^2>0`, the norm `Ns=f^2-Delta*(i*c^2)^2` cannot vanish.
3. Put `A=Delta*(f^2-1)`. If `f=1` then `A=0` and `Na=y^2>0`. If `f>=2` then `A>=2`. A zero of `Na=A*V^2-(A-1)*y^2` would make `(A-1)/A=(V/y)^2`, since `y>0`. The fraction on the left is reduced. Consequently both `A-1` and `A` would be integer squares, impossible for two consecutive positive integers. Hence `Na` cannot vanish.

The elementary fact used here is that an integer which is a rational square is an integer square, and a reduced positive rational square has square numerator and denominator.

## Complete zero equivalence

All three squares `N0^2,Na^2,Ns^2` are at least one. The new equation therefore forces each to be exactly one and forces `N1*Nk*Nt=1`.

For the first norm, the consecutive-product negative Pell obstruction rules out `N0=-1` because `n>=2`. For the strong norm, `Delta` is 0 or 3 modulo 4, ruling out `Ns=-1`. Thus `N0=Ns=1`. The latter equation makes `A=Delta*(f^2-1)=(Delta*i*c^2)^2` a square. Reducing `Na` modulo four now rules out `Na=-1`, so `Na=1`. The new equation consequently implies `N0*N1*Na*Nk*Nt*Ns=1`, the unscaled P69 equation.

Conversely, the established factor-sign argument for the P69 product gives `N0=Na=Ns=1` and `N1*Nk*Nt=1`, so the new equation vanishes. Hence the new polynomial has exactly the positive zero set of P69, and therefore of P67 by the existing checked local equivalence. This argument needs no compiler theorem.

## Exact metrics

The supplied `p74_norm_minima.json` is an explicit division-free evaluator. It keeps P75's first 62 producers; adds one producer for `Ns`; uses two products for `N1*Nk*Nt`; one subtraction of one; four squares; three additions; and a final subtraction of three. Thus it has `62+1+2+1+4+3+1=74` live gates: 41 multiplications, 18 additions, 15 subtractions. P75 has the same multiplication/addition counts and one more subtraction.

Its exact total degree is 68. Only `Ns^2` reaches that degree; all other terms have degree at most 62. The leading form is the same as in P75:

`i^4*w^4*s^12*(eta+zeta)^8*(beta*J)^40`.

In particular `J^40*eta^8*i^4*w^4*s^12` has nonzero coefficient `beta^40`. This is a modest new Pareto improvement over the checked 75/68 point, not a significant breakthrough or a global minimum.

`verify_p74.py` checks the actual package-36 compressed and decompressed payload hashes, byte and bit lengths, pinned Git blob identities, `beta=2^1012115-1>0`, the shifted-mask convention, and the entire producer prefix inherited from P75. For the real coefficient tuple it verifies a nonzero diagonal leading coefficient modulo `1000000007`, equal to `2^8*beta^40` modulo that prime. Thus its exact-degree check is about the supplied coefficients, not merely a small test specialization. The displayed uniform leading form also proves exact degree 68 directly for every nonzero beta. Run `python3 verify_p74.py` or `python3 -O verify_p74.py` from this directory.

## A lower-degree tradeoff

Promoting `c` from abbreviation to a sixteenth positive unknown and adding the equation `c-(eta+zeta)*Y-eta=0` lowers the strong norm degree from 34 to 18 and the auxiliary norm degree from 28 to 26. The first norm remains degree 22. A sum-of-squares presentation can therefore have degree 52. This increases variables and arithmetic operations and is not obviously superior to the already available quadratic-lifting approach.

## Strong-rank obstruction to the tempting c-squared deletion

The inherited Pell audit explicitly uses `psi_A(m)=i*c^2` to deduce `p*c | m`, then `c | m`. The latter divisibility is essential when the auxiliary congruence is reduced modulo `c`. Replacing `i*c^2` by `i*c` proves only `p | m` and does not justify the index recovery `p=R`. No such weakening is claimed.
