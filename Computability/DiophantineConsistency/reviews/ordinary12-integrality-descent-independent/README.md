# Independent review of the ordinary-tail descent plan

Reviewed commit `e5e341f1e2`, specifically its plan and finite checker,
whose SHA-256 values are pinned in `check.py`. The algebra and proposed
descent are consistent with the stated hypotheses. This is a mathematical
review and finite check, not a Lean proof, a model proof, or an iPRA proof.
The graph-to-hypotheses, fixed-port calibration and proof transport identified
in the plan remain open. The checker retrieves the reviewed historical files
from that local Git commit, so later fixes to the workspace do not change
what this review checks.

## Descent and sign cases

Write the plan's reduced equation as

```
q v² b² = (q-1)a² + b²,   q>1, b>0, gcd(a,b)=1.
```

Normalizing signs of the original integer `v,Y,D` is legitimate because
they occur squared and `D != 0`; the equation forces `v,Y != 0`. With
`a,b` reduced, the cubic Bézout identity in the plan gives a Bézout
certificate for `a²,b²`. From the equation, `b² | (q-1)a²`, hence
`b² | (q-1)`. Thus the claimed natural `s` with `q-1=b²s` exists.
For `v=1`, cancellation by `q-1>0` gives `a=b`; the Bézout relation then
implies `b=1`.

For `v>1` the first inequality in the plan follows from
`(q-1)(a²-v²b²)=b²(v²-1)>0`. The second follows by comparing the
nonnegative terms after squaring:

```
(qvb)² - ((q-1)a)² = q b² + (q-1)a² > 0.
```

Consequently, the proposed transform satisfies `-v<v'<v`. Its norm
equation rules out `v'=0`; it also rules out `a'=0`, since that would give
`q(v')²=1`. If `a'=a+bt` and `ax+by=1`, then
`a'x+b(y-tx)=1`; negating the coefficient of `a'` handles the absolute
value when `a'<0`. The explicit polynomial checks cover the norm and
certificate transformations; they do not discharge their model-level
inequalities or gcd-construction obligations.

The `q=1` case is genuinely excluded: `v=Y=1,D=2` satisfies the original
cleared equation but `D` does not divide `Y`. The graph has a distinct
argument for strictness: for positive `X,Y,t`, `a=XY+Y>=2`,
`Delta=(a+1)(a+3)>=15`, `f=t+1>=2`, so `Q=Delta(f²-1)>=45`.
Also `c=(eta+zeta)Y+eta>=3` and `d=c⁴>0` for positive inputs. These are
elementary mathematical observations, not an existing signed graph-to-model
binding.

The nonzero denominator still needs proof. In the generic tail, even
`Q>1`, `d=c⁴>0`, `n>0`, and `N=0` do not imply `bn!=0`: take
`Q=16,c=2,d=16,n=1,V=-1`, giving `w=bn=A=N=0`. This is **not** claimed
to be a valuation of the complete positive-coordinate graph; it shows why
the required graph-specific bound on `V` or another nonzero argument must
not be omitted. The plan's proposed route from `T>=1`, `f>=2`, `2R<c`,
and `c>0` to `V>c` is valid: first `cT-R>=c-R>0`, then
`V-c>=4(c-R)-2c=2c-4R>0`. Establishing those premises and the signed
substitutions in the intended model remains work.

## Induction and iteration

The displayed `Bad(k)` has a quantifier-free matrix with a finite
existential prefix. Given an appropriate coding and the usual hierarchy
formalization, it is a plausible Σ₁ predicate, so classical `IΣ₁`
least-number reasoning is a suitable proposed route. The least element
cannot be zero (the right side of the norm equation is positive) or one
(the base case contradicts fixed `b>=2`), while the signed and normalized
transform yields a strictly smaller positive witness. The plan correctly
labels representability, model inequalities, and the encoded certificate
as unproved; this review does not build that Lean theorem.

The bounded primitive-recursive iteration is also a plausible separate
route. For initial `v0>0`, start at `k=0` with `v+k<=v0+1`; if `v>1`,
strict descent preserves the inequality at the next step. If the state is
frozen at `v=1`, preservation for the next step uses the induction-side
condition `k<v0`, giving `1+(k+1)<=v0+1`. At `k=v0`, positivity and the
bound force `v=1`. Encoded state updates, signed-pair arithmetic and finite
iteration are primitive-recursive candidates; the full invariant must be
shown quantifier-free in the chosen expanded iPRA language and proved there.
In particular, primitive-recursive gcd normalization and its Bézout
certificates, signed cancellation, and object-level proof transport are not
provided by this observation. Neither the classical Σ₁ plan nor the
iteration design is an established iPRA derivation.

## Reproducible checks and limits

The independent checker uses a sparse sorted-monomial collector, rather than
the author's exponent-vector collector. It checks six exact polynomial
identities, including the Bézout coefficient update and polarization, and
independently evaluates the 95-gate graph's tail from the free cut variables
`Q,d,V,n`. It also checks 19 literal rows used in the displayed definitions
of `a,c,Delta,f,Q,d,V`. This validates those isolated identities, not the
complete graph binding or the implication `P12=0 -> N=0`.

It exhausts `2<=q<=25`, `1<=b<=12`, `1<=v<=100`, finding all 50 reduced
states by exact divisibility and integer square root; 26 need a descent step.
It also checks 472 solutions of the original cleared equation in the signed
finite box stated in `CHECK.json`. These finite checks are sanity tests,
not proofs of the unbounded statements. Their mutation controls and all
checks use explicit exceptions and remain active under `python -O`.

The author's checker exits 0 under normal Python. Its identity and bounded
checks are written with `assert`; Python removes them under `-O`. A temporary
copy with an appended false assertion exited 1 normally but exited 0 and
printed the original PASS line under `-O`. The author's README prescribes the
normal run, so this does not invalidate that prescribed run; it means an
optimized invocation cannot be counted as a check.

Run from the repository root:

```sh
python3 -B Computability/DiophantineConsistency/reviews/ordinary12-integrality-descent-independent/check.py
python3 -B -O Computability/DiophantineConsistency/reviews/ordinary12-integrality-descent-independent/check.py
```

Both runs exited 0. Separate receipts preserve their optimization flags and
the actual nested checker exits. The note does not assert existence of a
proof in iPRA.
