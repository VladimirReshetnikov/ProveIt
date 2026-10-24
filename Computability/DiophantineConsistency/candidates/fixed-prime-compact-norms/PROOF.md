# Exact compact evaluation of the fixed-prime polynomials

This candidate changes the division-free **evaluator**, while preserving every coefficient of the six parent polynomials. It uses the entire mixed-parity-unrounded source34 tuple, all independent variables, the literal complete live prefix and each finalizer unchanged. It adds no new semantic normalization, choice of witnesses or condition on an integer input. Its zero correspondence is pointwise equality, stronger than an existence-only reparameterization.

The ordinary fixed-prime/positivity/native calibration of the parent therefore transfers exactly. It remains an ordinary mathematical dependency; no Lean or internal object-ZFC proof is claimed. Lean formalization is paused. No old H10 emitter or numeral array is executed by this construction or its audit.

## Universal norm identity

Write

```
F_m(x;a1,...,am)= product over all m independent signs
                    (x + sum signs_i sqrt(ai)).
```

Sign invariance makes F_m an integer polynomial. The three-root identity, valid over a free commutative integer polynomial ring, is

```
s=a+b+c, p=ab+ac+bc,
F_3(x;a,b,c) = [(x²-s)²-4p]²-64abc x².
```

It follows by first taking the two conjugate signs of one radical, then taking the other two norms. It is also checked coefficient-for-coefficient in the pinned norm templates. The following two constructions are identities in freely varying x,a,b,c,d,C,delta. They remain polynomial identities when delta=0; only their rational interpretation below requires a nonzero delta.

### Four roots: 43 binary operations

Let u²=c and put t=x-u. Clearing the inner three-root norm gives

```
delta^4 F_3(t;a,b,C/delta)
  = [q²-4(delta²ab+delta C(a+b))]²
      -64 delta³abC t²,
q=delta(t²-a-b)-C.
```

Write `q=q0+q1 u`, and the bracketed polynomial as `A0+A1 u`. The literal formulas are

```
q0=delta(x²+c-a-b)-C, q1=-2delta x,
A0=q0²+c q1²-4(delta²ab+delta C(a+b)),
A1=2q0q1, z=64delta³abC,
f0=A0²+c A1²-z(x²+c),
f1=2A0A1+2zx.
```

The cleared inner norm is `f0+f1 u`. Multiplying its conjugate therefore gives the ordinary polynomial

```
f0²-c f1² = delta^8 F_4(x;a,b,c,C/delta).
```

This is `cleared_norm4` in `build.py`. It has43 live binary additions, subtractions and multiplications after constant folding and common-register sharing. Fixed integer numeral leaves, including negative numerals, are free. The parent's generic Taylor evaluator has110 operations on the same free radicands, so substitution saves67 in every parent fourteen-variable graph.

### Five roots: 93 binary operations

Let u²=c, v²=d and t=x-u-v. Store t² directly in the basis `1,u,v,uv`:

```
t2=(x²+c+d,-2x,-2x,2).
```

The same cleared three-root identity gives

```
q=delta(t²-a-b)-C,
T=q²-4[delta²ab+delta C(a+b)],
f=T²-64delta³abC t².
```

All three objects are stored as four integer-polynomial components. Squaring a component tuple `(A,B,E,G)` uses only

```
(A²+cB²+dE²+cdG²,
 2(AB+dEG), 2(AE+cBG), 2(AG+BE)).
```

If `f=f0+f1u+f2v+f3uv`, first norm over u:

```
g0=f0²+d f2²-c(f1²+d f3²),
g1=2(f0f2-c f1f3).
```

The final answer is `g0²-d g1²`. Taking both conjugates gives

```
g0²-d g1² = delta^16 F_5(x;a,b,c,d,C/delta).
```

This is the unmodified `cleared_norm5` copied from the root-fusion archive into `compact_norms.py`, authenticated in `SOURCE_PINS.json`. Its free graph has93 live operations, compared with370 in the fixed-prime Taylor template. The resulting277-operation reduction is independent of the later source substitution.

## Exact substitution into the complete fixed equations

The old norm inputs are precisely the following named prefix registers, in order:

```
norm_z, rad_A, rad_B, rad_D, [rad_G], Cnum, delta.
```

The new evaluator reads the same registers, with the same order and the same number of roots. `build.py` uses the parent's exact operation normalization and exponent schedule to recreate the stored prefix. The auditor compares every live prefix node and all named definitions literally. It also checks that the set of retained live prefix records is unchanged; no source witness or fixed coefficient is accidentally dropped.

The old actual norm tail is compared to the pinned generic Taylor template by exact shared term interning. The new actual tail is compared to the compact generic template the same way. These comparisons identify only the designated cut registers with free variables and allow operand commutation; they introduce no hash-based equality or numerical evaluation premise. Any other mathematical input encountered below the cut fails the check. The output finalizer is checked separately at the norm/guard cut.

Thus the generic identities substitute into every complete literal graph without assuming any equation or inequality on the source registers. For four roots the unchanged finalizer is

```
(1+4 norm)(1+4 guard)-1.
```

For five roots the norm itself is the complete polynomial. Both are therefore identical to their parents at **every** integer assignment, including singular inputs where delta=0. No pointwise quotient by delta is performed.

## Complete source binding and attained degree

The six fixed leaves are the complete parent source34 tuple:

```
beta=2^1064921-1,
K0,MC,MF (MF already shifted),
cone_A=2^1113, cone_B=2^666104.
```

`coefficients/BINDING.json` and every compressed payload are copied unchanged. The candidate contains actual coefficients, rather than parameters requiring a future calibration. `SOURCE_PINS.json` authenticates the retained parent equations, generic templates, article, degree proof and copied compact-ring utilities. The preceding review authenticated these raw coefficients against the independently reconstructed native recipe; this candidate does not rerun that recipe or change it.

Pointwise polynomial equality preserves every expanded coefficient, total degree and zero. The parent's unbounded degree upper bounds and leading-form arguments therefore transfer directly. The candidate auditor additionally evaluates each whole stored DAG on an exact univariate polynomial substitution modulo a prime using the actual fixed coefficient bytes. It attains the stated degree with a nonzero coefficient and checks every node, input and coefficient leaf live. This is an attained-degree certificate combined with the inherited upper bound, rather than a heuristic gate-degree estimate.

The resulting complete evaluators are:

| Integer variables | Degree | Parent operations | New operations |
|---:|---:|---:|---:|
| 13 | 1392 | 475 | 198 |
| 13 | 1408 | 473 | 196 |
| 14 | 652 | 230 | 163 |
| 14 | 664 | 223 | 156 |
| 14 | 700 | 217 | 150 |
| 14 | 748 | 215 | 148 |

The thirteen-variable points remain dominated by root fusion. Against root-fusion14/696/150, degree664/156 and652/163 trade modest extra operations for lower degree, while degree748/148 saves two operations for greater degree. Degree700/150 remains dominated. Counts measure these stored evaluators, not an arithmetic-circuit optimum. The expanded coefficients are unchanged exactly; no coefficient-height improvement is claimed.

## Check scope

Run `python3 build.py`, then `python3 check.py` and `python3 -O check.py --output CHECKS_OPTIMIZED.json`. Only the generated candidate files and requested receipt are written. Incoming archives and their extracted trees stay untouched.

The exact sparse-ring checks compare495 and20,349 complete generic coefficient records respectively. The five-root result also matches the independently expanded full32-sign polynomial retained from root fusion. Both modes reject an operation-preserving generic norm mutation. Complete literal prefix/cut/finalizer checks, source pins, numeral hashes, deterministic generation, topology, liveness and nonzero degree certificates pass for all six graphs. These finite checks prove the specified polynomial identities; the inherited ordinary source/refutation theorem remains a separate mathematical dependency, and no consistency search is performed.
