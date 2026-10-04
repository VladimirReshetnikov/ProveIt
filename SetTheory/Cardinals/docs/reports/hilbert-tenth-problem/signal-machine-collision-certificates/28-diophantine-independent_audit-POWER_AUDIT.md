# Independent audit of the expanded POWER specialization

Date: 4 October 2026 UTC

## Verdict and scope

**PASS for the audited POWER subsystem.** For every integer base `B0 >= 2`, natural exponent `e`, and positive integer `out`, the fifteen displayed equations admit their other twenty-five positive leaves if and only if `out = B0^e`. Both POWER instances in the native three-input linear DAG implement those equations exactly. Each has twenty-six positive witness leaves including `out`, fifteen equations, and seventy body gates (`31 *`, `24 +`, `15 -`).

This is an independent mathematical specialization audit against the supplied pinned theorem statements and their constructive proof text. It is not a fresh Lean kernel verification, an authentication of the claimed remote commit, or a re-audit of the entire underlying Pell development. It is also not an audit of the surrounding geometric predicate, extraction argument, final sum-of-squares assembly, or one-input transport; those are outside this assigned subsystem.

No mathematical defect was found in the domain restriction, zero-exponent shift, strict modulus bound, natural subtraction, congruence orientation, or leaf count. No change to Section 7 is required by this audit.

## 1. Audited bytes and method

The artifact root is `/workspace/shared/five-signal-diophantine58-20261004/`.

| File | SHA-256 |
|---|---|
| `PROOF.md` | `b55f301d2b1531f348163f026b3c1f7f827669d266afb77d854eef7ceb21c482` |
| `sources/pell-source.lean` | `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a` |
| `evidence/three-input-linear.dag.json` | `707721d1a8dca21b29acda57df8df6e763a1df89761f513122bec5edd9261ccc` |

The local Pell-source hash agrees with the value printed in `PROOF.md:146` and recorded in the supplied pin manifest. The proof identifies mathlib4 commit `ac77769fabe23cb237559e7f56578dbead91499f`, file `Mathlib/NumberTheory/PellMatiyasevic.lean`. The actual checked object here is the local file with the hash above.

I read the displayed equations and pinned Lean source as inert text. I did not run Lean, an author emitter/checker, prior saved program, upstream program, or simulator. I did not use any author or previous-review report as the specification. A freshly written standard-library Python program parses only the native DAG as JSON and independently compares its equation sides with sparse integer polynomials constructed from the fifteen displayed formulas. It does not import any supplied code, evaluate a trajectory, or generate Pell witnesses.

The independent checking artifacts in this directory are:

| File | SHA-256 |
|---|---|
| `check_power_dag_independent.py` | `36db04154e4d7f255b1fb5b78ed01ca74054e5239b0dd464cb12db3265cf3a82` |
| `POWER_DAG_RECEIPT.json` | `5b3af57fa307404693bfe6fba020763bd4b7803ab364c726f385dcd3aa8dc994` |

The checker completed successfully. Its receipt records every checked equation's exact operand references, degree, and monomial count, and every module body-gate index. Its expected formulas were written directly for this audit, without reading the emitter or copying an earlier checker.

## 2. Exact source statements and variable correspondence

All line references below are to the hashed local `sources/pell-source.lean`.

### 2.1 Pell sequences

The natural sequence pair is defined at lines **104–106**, with initial pair `(1,0)`. Its components `xn` and `yn` are at **109–114**. The parameter hypothesis is `1 < a` at **86**. Thus the source uses natural-valued sequence components, rather than an unspecified signed Pell solution.

### 2.2 `Pell.matiyasevic`

The complete theorem statement is at **760–766**. It equates

`exists a1 : 1 < a, xn a1 k = x and yn a1 k = y`

with `1<a`, `k<=y`, and either the zero solution `(x,y)=(1,0)` or natural witnesses `u,v,s,t,b` satisfying:

1. Three Pell equations for `(x,y)`, `(u,v)` at parameter `a`, and `(s,t)` at parameter `b`
2. `1<b` and `b == 1 (mod 4y)`
3. `b == a (mod u)`
4. `0<v` and `y*y | v`
5. `s == x (mod u)` and `t == k (mod 4y)`

Its forward constructive proof is **767–806**. In particular, it obtains `k<=y` at **778**, `v>0` at **790**, `b>1` at **791–796**, and the two final congruences at **799–803**. The reverse direction is **807–847**.

The module substitutes `k=k0=e+1`, `b=beta`; its other Pell letters correspond directly. Module equations 1–9 encode precisely the nonzero branch, with additional positive/natural quotient adapters addressed below.

### 2.3 `Pell.eq_pow_of_pell`

The full theorem statement is at **860–864**. Its nonzero-base, nonzero-exponent branch states that `n^k=m` is equivalent to the existence of natural `w,a,t,z`, a proof `a1:1<a`, and:

- `xn a1 k == yn a1 k * (a-n) + m (mod t)`
- `2*a*n = t + (n*n+1)`
- **`m<t`**
- `n<=w`, `k<=w`
- `a*a - ((w+1)*(w+1)-1)*(w*z)*(w*z) = 1` in natural arithmetic

The source-to-module substitution is:

| Source name | Module expression/name |
|---|---|
| `n` | `B0` |
| `k` | `k0=e+1` |
| `m` | `m0=B0*out` |
| `w,a` | `w,a` |
| modulus `t` | `M` |
| `z` | `g` |
| `xn a1 k, yn a1 k` | `x,y`, certified by equations 1–9 |

The power theorem's modulus `t` is **not** the module's Pell-coordinate `t`; the modulus is `M`. Equations 10–15 match the six substantive conditions above.

The theorem's constructive direction is **865–897**. It chooses `w=max n k` at **870**, gives `1<a` at **876**, obtains the divisible Pell coordinate at **880–881**, obtains the strict modulus inequality at **882–888**, and supplies all witnesses at **897**. Its reverse direction is **898–928**, ending by using **both strict inequalities** to identify the congruent natural numbers at **926–928**. There is no generic MRDP invocation in this specialization.

## 3. Domain adapters and subtraction

The fifteen equations are `PROOF.md:128–142`; their domains and abbreviations are at **118–126**.

The two leaves `aMinus1` and `betaMinus1` are strictly positive. Setting `a=aMinus1+1` and `beta=betaMinus1+1` gives exactly all natural parameters at least two. There is no missing value at the lower endpoint.

Each of the eleven natural adapters is represented by its positive `.Plus` leaf minus one. This represents every natural, including zero. In particular the eight congruence-quotient quantities are allowed to vanish. Conversely, every such positive leaf produces a nonnegative integer. The output and the twelve remaining directly positive quantities are ordinary independent positive leaves.

The DAG uses integer subtraction. The source Pell equations use natural truncated subtraction. For natural `A,C`, the statement `A-C=1` with natural subtraction is equivalent to the integer equality `A=C+1`: the left side being positive forces `A>C`. This converts each source Pell equation exactly, in both directions. The inner differences `a*a-1`, `beta*beta-1`, and `(w+1)*(w+1)-1` are nonnegative under the stated domains and therefore also agree with integer subtraction. The source itself makes the relevant natural/integer Pell conversion explicit at **197–203**.

The remaining delicate difference is `a-B0` in equation 15. Equations 10 and 13, and positivity of `g`, yield `w>=B0>=2` and

`a^2 = 1 + (w^2+2w)*w^2*g^2 > w^2`.

Because `a,w` are natural, `a>w>=B0`. Thus the polynomial difference `a-B0` is positive and equals the source theorem's natural subtraction `a-n`. This implication is derived from the constraints before applying the power theorem; it does not presume the desired power conclusion.

In the reverse construction from the source theorem, its initially natural `g=z` cannot vanish: substituting zero into its final Pell equation gives `a*a=1`, contradicting `1<a`. Consequently `g>0`, and the same argument applies. There is no lost source witness caused by making `g` positive.

## 4. Soundness: positive module solutions imply the power identity

Assume all fifteen equations and all positive-leaf domains. Let `k0=e+1>=1`, `m0=B0*out>0`.

Equations 1–3 are the three required natural Pell equations after the exact subtraction conversion. Equation 4 gives `beta == 1 (mod 4y)`. Equation 5 gives `beta == a (mod u)`. Equation 6 gives `y*y | v`; `v>0` is a domain condition. Equation 7 gives `s == x (mod u)`. Equation 8 gives `t == k0 (mod 4y)`. Equation 9 and `dyk>=0` give `k0<=y`. Parameters `a,beta` are both greater than one.

All conditions of the existential branch of `matiyasevic`, **760–766**, are therefore met. The theorem's reverse direction yields

`x=xn(a,k0), y=yn(a,k0)`.

Equations 10 and 11 give `B0<=w`, `k0<=w`. Equation 12 gives **`m0<M`**, since its right-hand slack `Jp` is strictly positive. Equation 13 is the required additional Pell equation. Equation 14 gives `2*a*B0=M+(B0^2+1)`. By Section 3, `a-B0` in equation 15 agrees with the natural subtraction in the source; equation 15 therefore gives

`xn(a,k0) == yn(a,k0)*(a-B0)+m0 (mod M)`.

These are exactly the nonzero branch of `eq_pow_of_pell`, **860–864**. Since `B0>0` and `k0>0`, its reverse direction yields `B0^k0=m0=B0*out`.

Finally `B0^(e+1)=B0*B0^e`; cancellation of the nonzero integer `B0` gives `out=B0^e`. This proof uses no bound or sign condition not already encoded or derived.

## 5. Completeness: a genuine power has positive-leaf witnesses

Assume `out=B0^e`, with `B0>=2`, `e>=0`. Set `k0=e+1` and `m0=B0*out=B0^k0`.

Apply the constructive direction of `eq_pow_of_pell`, **865–897**, in its positive-base, positive-index branch. It supplies natural `w,a,M,g` with `a>1`, `m0<M`, the required two lower bounds, Pell equation, congruence, and modulus identity.

Their stricter module domains cause no loss:

- `w>=B0>=2` implies `w>0`
- `M>m0>0` implies `M>0`
- `g=0` is impossible by the argument in Section 3
- `a>1` is represented by the positive leaf `aMinus1=a-1`
- `Jp=M-m0` is positive
- `dwb=w-B0` and `dwk=w-k0` are natural

Set `x=xn(a,k0)` and `y=yn(a,k0)`. Apply the constructive direction of `matiyasevic`, **767–806**. The zero disjunct is impossible because it would have `y=0` while `k0<=y` and `k0>=1`. Hence the source supplies the nonzero-branch natural `u,v,s,t,beta`, as well as `k0<=y`.

All remaining positive requirements follow:

- `y>=k0>=1`, hence `y>0`
- Each of `x,u,s` has square equal to one plus a nonnegative natural, so each is positive. The source also records positivity of all `xn` values at **257–258**
- `v>0` is explicit in `matiyasevic`, **766**
- `beta>1` is explicit at **765**, so `betaMinus1=beta-1>0`
- `y*y | v` with `y>0`, `v>0` supplies a **positive** quotient `qv` in `v=y^2*qv`
- `beta == 1 (mod 4y)`, `beta>1`, `4y>0` supply a **positive** quotient `qb` in `beta=1+4y*qb`
- `t == k0 (mod 4y)` excludes `t=0`, because `1<=k0<=y<4y`; therefore the source's natural `t` is positive
- `dyk=y-k0` is natural

The two-sided congruence witnesses can be chosen as naturals exactly as detailed in Section 6. Every natural quantity is then encoded by its value plus one, which is positive. Thus equations 1–15 and all twenty-six positive-leaf domains hold simultaneously.

This proves existence for every exponent, without a numerical bounded-witness search or an assumption about the size of the constructive Pell witnesses.

## 6. Congruence signs and strict modulus

For any positive modulus `d` and integers `p,q`, the equation

`p+d*r1 = q+d*r2`, with natural `r1,r2`,

is equivalent to `p == q (mod d)`. Indeed it gives `p-q=d*(r2-r1)`. Conversely, if `p-q=d*z` for an integer `z`, choose `r1=max(-z,0)`, `r2=max(z,0)`. Both quotient signs are thereby represented without a signed-variable leaf or an inequality on `p-q`.

The module's exact orientations are:

| Equation | Difference divided by modulus |
|---|---|
| 5 | `beta-a = u*(alpha2-alpha1)` |
| 7 | `s-x = u*(sigma2-sigma1)` |
| 8 | `t-k0 = 4y*(tau2-tau1)` |
| 15 | `x-[y*(a-B0)+m0] = M*(rho2-rho1)` |

These match the source congruences at **766** and **862**. None of the four pairs is omitted. Each pair uses two natural quantities, so either sign and zero are available. Their `.Plus` leaves may equal one, correctly encoding quotient zero.

Equation 12 is `M=m0+Jp` with **positive**, rather than natural, `Jp`. It enforces the strict inequality `m0<M` required at source **863**, not merely `m0<=M`. The source proof visibly relies on that strict bound at **928**. The DAG names this positive leaf `strict`; it contains no subtract-one adapter for it. Thus the necessary strictness survives translation exactly.

## 7. Exponent zero and valid instantiation domains

At `e=0`, `k0=1`. The module still uses only the nonzero branches of both source theorems. Soundness gives `B0=B0*out`, hence `out=1`; completeness constructs witnesses for `B0^1=B0`. No branch, extra selector, or implicit exception for exponent zero is needed. The shifted exponent is an expression, not an additional witness leaf.

In the native DAG, `g:36` is exactly `valuation.n.Plus-1`; `g:50` and `g:129` each add one to it. This explicitly implements the shift even though its sparse polynomial simplifies to `valuation.n.Plus`.

The first module has literal base five. The second module base is exactly

`g:115 = 3+4*(4*power5.out+1) = 16*power5.out+7 >= 23`.

Its lower bound holds from positivity of the first output leaf, before using the first module's power semantics. Both modules use the same natural exponent `g:36`. Consequently there is no circular justification of the base or exponent hypotheses.

## 8. Native DAG equality and independent counting

The independent checker reads the DAG's raw arithmetic operations, not a `POWER` evaluator. It derives integer coefficient dictionaries for both sides of every named module equation, substitutes the actual domain adapters, and checks each side against independently written formulas. **All thirty pairs of equation sides match exactly.** In particular this is stronger than testing finitely many inputs, and checks signs rather than only zero sets.

The checker independently verifies the actual exponent expression and both base expressions. It traverses equation dependencies, stopping only at the external base/exponent ports, and counts the resulting body-gate operations. It does not adopt the DAG's claimed `regions`, gate totals, or leaf totals as evidence.

| Native instance | Equation labels | Body gates, inclusive | Positive leaves | Body operations |
|---|---|---|---:|---|
| `power5` | `power5.eq1` through `.eq15` | `g:37`–`g:106` | 26 | 31 multiplications, 24 additions, 15 subtractions |
| `power_complex` | `power_complex.eq1` through `.eq15` | `g:116`–`g:185` | 26 | 31 multiplications, 24 additions, 15 subtractions |

The leaf count per module is independently partitioned as:

- **13 directly positive:** `out,w,M,g,x,y,u,v,s,t,qb,qv,strict` (`strict` is the proof's `Jp`)
- **2 shifted-positive:** `aMinus1,betaMinus1`
- **11 natural-adapter leaves:** `.Plus` for `dwb,dwk,dyk,alpha1,alpha2,sigma1,sigma2,tau1,tau2,rho1,rho2`

These are exactly the declared module-prefixed leaves, with no duplicate names. Every one is reached by a module equation. The other twenty-five leaves are auxiliary witnesses after fixing the output; all twenty-six count in the outer existential certificate. Neither the external exponent leaf nor the base expression is counted as a module witness. The module's seventy gates include the exponent shift, multiplication `B0*out`, parameter shifts, natural adapters, and all formula-side arithmetic. Formation and squaring of residuals belong to the global assembly and are not silently included in that seventy.

Both equation-13 residuals have exact degree six in their independent positive leaves; their leading degree-six term is `-w^4*g^2`. The receipt checks residual degrees equation by equation. No opaque power operation occurs among the audited module gates: they are all binary `+`, `-`, or `*`.

## 9. Conclusion and qualification

The complete two-direction argument follows from the precise pinned theorem statements after accounting for every stricter domain. The source's natural arithmetic, the polynomial's integer arithmetic, and the natural-pair congruence encodings agree. Zero exponent is included, the modulus inequality remains strict, and both actual native module instances match the fifteen formulas exactly.

The resulting assurance is a **source-level mathematical audit plus independent exact inert-DAG polynomial checking**. It should not be described as a new Lean build, a newly machine-checked proof of the Pell theorems, or a numerical all-exponent test. Within that clearly stated scope, the POWER subsystem passes without a required correction.
