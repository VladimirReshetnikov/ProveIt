# Independent audit of the reduced positive POWER modules

Date: 4 October 2026. Source packet: `positive-power22-reduction-20261004`.

## Verdict

**PASS, with the stated pinned number-theoretic dependency.** The four displayed positive-integer modules have the asserted existential equivalence, leaf and residual counts, exact joint degrees, and infinite nonempty complete fibers. The successive 22→16→14→13 restrictions are bijections of solution tuples at fixed inputs and output. The earlier 26→22 reduction is an existential equivalence with a section; it is not a bijection because it removes four independent common-shift redundancies.

No mathematical error was found in the scoped claims. The rational-square argument for the 13-leaf construction is sound. There is also a shorter integrality proof from its fourth equation, recorded below. This is a simplification, not a correction.

This audit does not certify global optimality, novelty, finite-fold representability, a fixed polynomial for an unbounded horizon, physical executions from unencoded inputs, or a fresh Lean build. All-exponent POWER correctness imports the two precisely identified Pell theorems; finite evidence does not replace them.

## 1. What was inspected, and what was executed

I independently read `HANDOFF.md`, `PROOF.md`, `ELIMINATION_VARIANTS.md`, the source/manifest pins, and the complete author checker as inert text. I inspected the retained POWER module derivations, native-gap equations and trace ledger, and compressed construction's clipping, interpolation, six residuals, soundness/completeness, uniqueness, and degree arguments. I read the pertinent pinned Lean declarations and constructive passages as text, including the recurrence and theorems at lines 760–766 and 860–864.

Only the newly authored `check_independent.py` was executed for scientific checks. It uses Python's standard library and an independently implemented sparse polynomial representation with monomials stored as `(variable, exponent)` pairs. It does not import or execute the author's checker, upstream code, Lean, a counter-machine interpreter, a physical simulator, or a stored schedule. Pell fixtures are computed with newly authored binary exponentiation in an exact quadratic ring, rather than calling the packet's recurrence routine. Compressed acceptance sets in tests are explicitly supplied finite sets, not outputs of a simulated machine.

All eight complete residual/SOS expansions were independently computed from the displayed definitions before comparing their coefficients against inert source JSON. Equality with source JSON is supporting cross-check evidence; the author receipts were not treated as independent proof.

The audit and all outputs are outside the source tree. All 22 entries listed in the source manifest and all seven dependency pins match their declared byte counts and SHA-256 values. A complete 26-entry tree snapshot verifies unchanged file bytes, modes, sizes, and nanosecond mtimes across execution. Separate before/after shell snapshots agree as well. Access times are intentionally outside this claim because reading may update them.

## 2. Exact domains and the baseline theorem

Throughout, `b≥2` and `C,o≥1` are integers. The intended output is `o=b^(C−1)`. The output `o` is included in the module leaf count, whereas `C` and any separately supplied base are not. A variable base is supplied as an external positive input `B` with `b=B+1`; that input must be counted by the outer construction. Every natural alias is exactly its own positive adapter minus one. Thus zero natural values are represented by positive leaf 1.

The 22-leaf module contains thirteen directly positive leaves, the two positive leaves `alpha_plus,beta_plus`, and seven distinct natural adapters. There are exactly fifteen residual slots. Their squared sum is zero over integers if and only if all fifteen residuals vanish.

### 2.1 The four quotient signs

The sign argument is valid for every solution, not only for constructive fixtures. From `y≥C≥1` and `v=y²q_v` with `q_v≥1`, we get `v≥y` and `v≥1`. Subtracting the two Pell identities gives

- `u²−alpha²=(alpha²−1)(v²−1)≥0`, so `u≥alpha>0`
- `u²−x²=(alpha²−1)(v²−y²)≥0`, so `u≥x>0`

The elementary residue fact is: if `L>0`, `0<r≤L`, `z>0`, and `z=r+Lq` with integral `q`, then `q≥0`. Indeed, `q≤−1` would imply `z≤r−L≤0`. The endpoint `r=L` is allowed.

Apply this fact to the old congruences using `(L,r,z)=(u,alpha,beta)`, `(u,x,s)`, and `(4y,C,t)`. The three resulting quotients are nonnegative. No strict inequality `alpha<u` or `x<u` is needed.

For the fourth quotient, `w≥b≥2`, `g≥1`, and the auxiliary Pell equation imply

`alpha²=1+((w+1)²−1)(wg)²>w²`,

hence `alpha>w≥b`. Set `h=x−y(alpha−b)`. Direct expansion gives

`x²−[y(alpha−b)]²=(2alpha b−b²−1)y²+1>0`.

Both quantities being squared are nonnegative, and `x>0`; therefore `h>0`. Since `M=bo+J>bo>0`, the old final congruence says `h=bo+M q` for an integer `q`. The same residue fact forces `q≥0`. This sign argument does not circularly assume the final quotient is nonnegative.

The old-to-new quotient map is the difference of the second and first old natural aliases. The signs just proved make these differences natural. The reverse map assigns old first aliases zero and old second aliases the new quotients. Their positive adapters are respectively 1 and `q+1`. It is a valid section. Every old pair also permits an arbitrary shared nonnegative shift, which explains precisely why the old-to-new map is not bijective.

### 2.2 Imported all-exponent theorem, and subtraction semantics

The dependency is mathlib4 commit `ac77769fabe23cb237559e7f56578dbead91499f`, `Mathlib/NumberTheory/PellMatiyasevic.lean`, SHA-256

`993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`.

The locally retained bytes match that pin. This audit verifies the local pin and the actual retained declarations; it does not claim to have rebuilt or independently machine-checked mathlib or authenticated the remote Git commit anew.

`Pell.matiyasevic` says exactly that the index-`C` pair is characterized by `alpha>1`, `C≤y`, and either the zero pair `(1,0)` or the displayed three Pell equations, congruences, positivity of `v`, and divisibility `y²|v`. Here `y≥C≥1` excludes the zero branch. The module's first nine residuals supply the nonzero branch, so `x=X_C(alpha)` and `y=Y_C(alpha)`.

The positive-base/index branch of `Pell.eq_pow_of_pell` specializes with source variables

`n=b`, `k=C`, `m=bo`, `t=M`, `z=g`, `a=alpha`.

Its hypotheses are precisely the final congruence, `2alpha b=M+b²+1`, `bo<M`, `b≤w`, `C≤w`, and the auxiliary Pell equation. Thus it gives `b^C=bo`; canceling positive `b` yields `o=b^(C−1)`.

The source uses truncated natural subtraction. An equality `A−B=1` in naturals is equivalent to the ordinary equality `A=B+1`. The inner subtractions of 1 occur from squares at least 4. The only potentially troublesome `alpha−b` agrees with ordinary subtraction because the auxiliary Pell equation already gave `alpha>b`. The translation therefore neither admits extra solutions nor removes the intended ones.

For completeness, start with `o=b^(C−1)` and apply the constructive power theorem and then the positive-index Matiyasevic theorem. Its auxiliary `g` cannot be zero, because that would force `alpha=1`. The Pell x-coordinates are positive; `y≥C≥1` and `v>0` make `q_v=v/y²` a positive integer. Since `beta>1` and `beta≡1 mod 4y`, `q_b=(beta−1)/(4y)` is positive. The congruence `t≡C mod 4y` and `1≤C≤y<4y` exclude `t=0`. The strict modulus bound gives `J>0`. All signed quotients have old paired-natural presentations, and the sign lemma converts them to the new natural quotients. This proves completeness including `C=1`.

## 3. Independent audit of the eliminations

### 3.1 Twenty-two to sixteen

The six removed leaves are `w,y,beta_plus,M,x,s`, reconstructed uniquely by

`w=b+d_wb`, `y=C+d_yC`, `beta=1+4y q_b`,

`M=2b alpha−b²−1`, `x=y(alpha−b)+bo+M q_r`, `s=x+u q_sigma`.

The six corresponding removed residuals become identities. The nine retained residuals are exactly old slots 1,2,3,5,6,8,11,12,13.

The removed domains require proof, and the packet supplies it correctly. We have `w≥b≥2`, `y≥C≥1`, and the retained auxiliary Pell equation implies `alpha>w`. The retained modulus-gap equation gives `M=bo+J>0`. Consequently `x>0` and `s>0`. Also `beta−1=4y q_b>0`, restoring a positive `beta_plus`. All restored values are integral polynomial expressions. Projection and reconstruction are mutually inverse on solution tuples.

### 3.2 Sixteen to fourteen

Remove the positive leaves `v,t` and their two defining residuals, and restore them by

`v=y²q_v`, `t=C+4y q_tau`.

Here `y,q_v,C` are positive and `q_tau` is natural, so both restored leaves are positive integers. All earlier reconstructions remain valid. This is again a bijection of solution tuples.

### 3.3 Fourteen to thirteen

Remove `alpha_plus`, use `M=bo+J`, and define `d=2b`, `A=M+b²+1`, and the displayed scaled expressions `X,S`. Forward substitution from a 14-leaf solution gives `A=d alpha`, `X=dx`, `S=ds`. The six residuals are respectively the former residuals multiplied by `d²,d²,d²,d,1,d²`; the former modulus-gap residual becomes an identity.

Conversely, define the rational `alpha=A/d`. The positivity of `M,b` gives `A,d>0`. The sixth equation implies

`alpha²=1+((w+1)²−1)(wg)²`,

an integer. Writing a rational number in lowest terms shows that an integer square forces denominator 1. This is a correct integrality argument. It also gives `alpha>w≥b`, and therefore `alpha_plus=alpha−1>0`.

There is a simpler independent route to integrality: the fourth equation itself is

`d beta−A−d u q_alpha=0`,

so `A=d(beta−u q_alpha)`. Therefore `alpha=beta−u q_alpha` is already an integer. The sixth equation is still essential for its Pell condition and the strict lower bound on alpha.

With integral alpha, recover the previous `M`, then the positive integers `x=y(alpha−b)+bo+M q_r` and `s=x+u q_sigma`. Dividing the six zero residuals by their nonzero factors `d` or `d²` restores precisely the surviving 14-leaf equations. There are no additional rational-alpha solutions introduced by clearing denominators. The maps are mutually inverse.

## 4. Literal joint degree audit

All degrees here are taken before imposing constraints and after expanding every adapter. `C` is an independent positive input and `B` is an independent positive input in the variable-base column. A fixed integer base is a coefficient. The residual degree lists independently obtained are:

| Module | Fixed base | Base `B+1` |
|---|---|---|
| 22 | 4,4,4,2,2,3,2,2,1,1,1,1,6,1,2 | 4,4,4,2,2,3,2,2,1,1,1,2,6,2,2 |
| 16 | 4,4,6,2,3,2,1,1,6 | 6,4,6,2,3,2,1,2,6 |
| 14 | 4,8,8,2,1,1,6 | 6,8,8,2,1,2,6 |
| 13 | 4,8,8,2,1,6 | 8,10,10,3,1,8 |

This gives the claimed upper bounds. The following degree-maximal monomials have coefficient exactly 1 in the independently expanded squared sums:

- 22: `w^8 g^4`, degree 12, both base conventions
- 16: `d_wb_plus^8 g^4`, degree 12, both base conventions
- 14: `alpha_plus^4 d_yC_plus^8 q_v^4`, degree 16, both base conventions
- 13, fixed base: `J^4 d_yC_plus^8 q_v^4`, degree 16
- 13, variable base: `B^8 d_yC_plus^8 q_v^4`, degree 20

These witnesses are unaffected by which fixed integer `b≥2` is chosen. In each case their source is a unique relevant variable-bearing residual square; no other residual can cancel them. Thus the bounds are exact for the literal formulas, not simply overestimates. The fixed-base-13 degree 16 must not be carried over to a variable base. Replacing an independent base `b` by `B+1` is an invertible affine change, so the analogous independent-base degree is unchanged. Arbitrary nonlinear substitutions are outside these degree assertions.

The leaf counts include `o`: 22,16,14,13. With `o` also fixed externally, auxiliary counts are 21,15,13,12. Residual slots are 15,9,7,6. There is one final SOS polynomial equation in every case.

## 5. Infinite complete fibers

Fix any accepted input/output triple and one 22-leaf solution. Keep its `alpha,y,u` and other fixed data, and use the integer Pell polynomials determined by

`X_0(z)=1`, `Y_0(z)=0`,

`X_(n+1)=zX_n+(z²−1)Y_n`, `Y_(n+1)=X_n+zY_n`.

The Pell norm invariant follows by a direct polynomial identity; positivity for `z≥2,n≥1` follows by induction. Also `X_n(1)=1`, `Y_n(1)=n`. Being integer polynomials, these functions preserve congruent arguments modulo any positive integer.

Let `beta_k=beta_0+4yu k`, `s_k=X_C(beta_k)`, `t_k=Y_C(beta_k)` for natural `k`. Then `beta_k≡alpha mod u`, `beta_k≡1 mod 4y`, so `s_k≡x mod u` and `t_k≡C mod 4y`. The residue lemma gives natural quotients and all needed positive adapters. All fifteen equations hold with the other data fixed. The new pair at `k=0` need not equal the original pair, which causes no logical problem.

Most importantly, `q_b,k=q_b,0+u k` strictly increases because `u>0`. This leaf is retained in all four modules. Hence every nonempty complete fiber remains infinite after every bijective elimination, including elimination of `beta_plus`. The explicit base-two `C=1` family was additionally verified as a polynomial identity in a free parameter in all four presentations. This is not a finite-fold formula.

## 6. Native-gap and compressed composition

For three external positive gaps, let `D=g1+g2+g3`. The two paid equations are

`(20g1−D)p=2D`, `(20g3−D)q=2D`.

Together with two independent base-two modules of indices `A,B`, they say exactly

`g1/D=1/20+2^(−(A−1))/10`, `g3/D=1/20+2^(−(B−1))/10`.

All divisions in this deduction have positive denominators. A solution forces `20g1−D>0` and `20g3−D>0`, so no unrecorded sign condition is needed. If there is an encoded solution, the equations determine `p,q` uniquely; injectivity of powers of two then determines `A,B` uniquely. This is a predicate that explicitly includes being encoded, not a claim about arbitrary physical inputs.

For a module of `L` leaves and `r` residuals, paid decoding uses `2+2L` positive witnesses and `2+2r` residuals. Adding the compressed triple and its six residuals gives `2L+5` witnesses and `2r+8` residual slots:

| Module | Decoding witnesses/residuals | Compressed witnesses/residuals | Total variables including gaps |
|---|---:|---:|---:|
| 22/15 | 46/32 | 49/38 | 52 |
| 16/9 | 34/20 | 37/26 | 40 |
| 14/7 | 30/16 | 33/22 | 36 |
| 13/6 | 28/14 | 31/20 | 34 |

The compressed theorem uses `K=T+1`, `N=K²`, a finite table, and an integral Lagrange encoding of the unique pair `(min(A,K),min(B,K))`. The clipping proof is sound: a representative counter started at `T` remains positive at every instruction-entry time `t<T` despite at most `t` decrements. Counters originally below `T` remain identical. Thus all tests and states agree through the horizon, even though final counter values need not agree. The six residuals then force the table node, correct clipping through product-plus-positive-slack constraints, and acceptance. Conversely the clipped node and its two uniquely determined slacks satisfy them. This also validates projected uniqueness.

Their inherited polynomial has joint degree at most `4(T+1)²−4` for `T≥1`, and exact degree 2 for `T=0`. The composed polynomial is another literal sum of squares with independent module leaves, so its exact degree is `max(module degree, compressed degree)`. Highest homogeneous sums of squares cannot cancel over the reals; the explicit independent module monomials also certify the module lower bound. Thus the table's fixed module degrees 12,12,16,16 give precisely the claimed composition bounds and horizon-zero degrees. These are bounds on a horizon-indexed family, not a uniform fixed-polynomial result.

If using the finite trace instead, add `T(E+2)` witnesses and `T(E+Z+4)+1` residual slots to the decoding columns. Counting its selector, one-hot, update, zero-guard, and state-link slots gives that expression directly. For `T=0` the single constant state residual preserves the count. First-halt-exactly-`T` adds one residual for `T≥1`, none at zero. The trace residual degrees are at most two, so their squares cannot raise the module degree. The complete composed fibers are infinite because one module's beta family can vary while its output, index, outer witnesses, and compressed projection stay fixed.

## 7. Independently executed evidence

The successful receipt is `evidence/results.json`; complete expansions are `evidence/*.independent.json`. The execution log is `run.log`.

Verified:

- 8 complete literal polynomial expansions, all exact residual/SOS degrees, coefficient-one degree witnesses, leaf counts, and variable liveness
- Exact coefficient equality with all 8 retained source expansion files
- 31 generic elimination identities: 15 for 22→16, 9 for 16→14, and 7 for 14→13
- 192 complete fixed/variable-base module evaluations on independently generated fixtures, including exponent zero, positive exponent, multiple auxiliary Pell choices, and beta-family members
- 96 restriction/reconstruction round trips recovering every original leaf exactly
- 72 old common-shift tuples, with nonuniform shifts, recovering the four normalized quotients
- 132 rejected single-leaf baseline perturbations
- 37 entire explicit beta-family residual identities in a free polynomial parameter, covering all four modules
- One general symbolic Pell induction invariant, rather than only sampled Pell indices
- 15,360 exact rational-number integer-square cases, supplemental to the proof
- 28 full native-gap/compressed polynomial compositions spanning all four variants and seven horizon/acceptance tables
- 179 finite clipping/interpolation algebra fixtures, without machine interpretation
- All manifest/dependency pins and full source preservation checks

Finite fixture successes do not prove all-exponent correctness, all-input soundness, or infinite cardinality. Those conclusions come from the preceding proofs and the explicitly bounded theorem dependency.

## 8. Portable reproduction

Use Python 3.9 or newer; no third-party packages or network are needed. The source argument should point to a readable copy of the frozen packet. The output directory must be outside that source tree.

    python3 check_independent.py --source /path/to/positive-power22-reduction-20261004 --out /path/to/new-evidence

The program exits nonzero on any failed check. It refuses an output directory within the source tree and checks byte hashes, modes, and mtimes before and after. The successful run prints a compact PASS summary and writes exact integer JSON evidence. No source checker needs to be executable.
