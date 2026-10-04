# Independent audit: fixed-arity binary sandpile certificate

Date: 4 October 2026. Verdict: **PASS for the stated raw physical-code relation, conditional only on the explicitly pinned Pell theorems used by POWER.** No mathematical or emitted-source defect was found. This verdict does not certify a universal-machine loader, target firing, a prescribed odometer, real-domain exactness, or finite-foldness.

The source under audit is `/workspace/shared/sandpile-fixed-arity-20261004`. It was kept read-only by this audit. The author’s builder and checkers were inspected only as text; none was imported or executed. The emitted DAG was treated as inert syntax for formal polynomial comparison, not evaluated on an arithmetic witness assignment. All finite numerical experiments below run the freshly authored `independent_check.py` in this audit directory.

## 1. Exact theorem accepted

Let `InputPlus` be a positive integer. Decode `InputPlus−1` by the specified seven right-associated Cantor pairings into

`(p−1,q−1,r−1,T,d−1,e−1,f−1,D)`.

The six dimensions are positive. `T` must contain exactly the allowed base-32 tile slots, with digits 0 through 5, and `D` the allowed finite-patch slots, with digits 0 through 15. Leading zero slots are permitted; nonzero digits outside the declared arrays are not. The tile is periodic on Z³, and the finite patch is anchored at physical coordinates `[0,d)×[0,e)×[0,f)`.

For the literal emitted integer polynomial `P`, the accepted equivalence is:

> There exist 2,566 strictly positive integer witnesses with `P(InputPlus,w)=0` if and only if the input encoding is valid and its physical sandpile admits a finite legal global stabilization with a binary odometer.

The supplied binary stream in a polynomial witness need only be a finite stabilizing supersolution. It need not equal the legal odometer. The conclusion concerns existence of a binary legal odometer, not the identity of every witness stream. Quantifier count and polynomial shape are independent of all dimensions, input values, witness-box size, and halting time.

`P` has exact total degree 18 and its supplied arithmetic DAG has 11,469 binary arithmetic gates. These are literal-source counts under the convention that fixed integer constants are free; they are neither a minimality claim nor an operation bound in a more restrictive constant-generation model.

## 2. Independent emitted-source reconstruction

The new checker implements sparse formal polynomials over Z, and separately writes the intended complete set of equations from the theorem. It then normalizes the submitted expression nodes as formal syntax and compares every named clause, every exposed port, and every macro interface to the independent specification. This gives exact symbolic identities rather than probabilistic modular agreement.

Results:

- All 1,491 residual polynomials agree exactly
- All 122 macro interfaces agree, including all 92 POWER, 22 Sub, four AND, and four SPREAD instances
- All 16 ports agree
- The set of 2,566 positive witnesses agrees exactly; there are no duplicates or additional unaccounted witnesses
- Every reference is defined before use and every gate is `+`, `−`, or `×`
- Every gate and every witness is reachable from the final output
- The output is precisely the sum of squares of all 1,491 listed residuals, with no missing or extra clause

The exact ledger independently recounted from syntax is:

| Part | Multiplications | Additions | Subtractions | Total |
|---|---:|---:|---:|---:|
| Body | 3,027 | 2,443 | 1,527 | 6,997 |
| Sum of squares | 1,491 | 1,490 | 1,491 | 4,472 |
| Complete polynomial | 4,518 | 3,933 | 3,018 | 11,469 |

An independent witness decomposition is

`92·26 + 22·5 + 4·3 + 4·4 + 2·3 + 5 + 4 + 4 + 8 + 6 + 3 = 2566`.

These terms are POWER outputs plus internals; Sub outer witnesses; AND partitions/output; spread outer gaps and geometric values; the two three-bitplane families; five geometric values; four box masks; four odometer/shift streams; eight physical input descriptors; six inner Cantor codes; and three box-size witnesses.

An independent equation decomposition is

`92·15 + 22·3 + 4·2 + 4·4 + 5 + 1 + 7 + 4 + 3 + 1 = 1491`.

The terms are POWER; Sub outer equations; AND partitions; spread bounds and geometric equations; five geometric equations; tile reconstruction; seven pairings; four box-mask equations; three exact shifts; and the one sandpile balance equation. The simpler three-Sub AND actually used by the source was checked. The more economical optional AND in the companion note is not silently substituted into this ledger.

### Exact degree, independently established

The sparse polynomial comparison identifies maximum residual degree 9. Exactly three residuals attain it: `patch.shift.eq8`, `patch.shift.eq9`, and `patch.shift.eq11`. Each has highest homogeneous part

`−4 p q r d e f tx0 ty0 tz0`,

where the three `t?0` variables are the positive source witnesses before adding one. All other residuals have lower degree. Consequently the complete SOS has leading homogeneous term

`48 (p q r d e f tx0 ty0 tz0)²`.

Thus its degree is exactly 18. This lower bound follows from the independently reconstructed clauses and the checked SOS structure; the author’s specialized-degree checker was not run or relied on.

## 3. Mathematical audit of the interfaces

### 3.1 POWER and the explicit external dependency

The source of the two relevant mathlib theorems was fetched independently through the read-only GitHub connector at commit `ac77769fabe23cb237559e7f56578dbead91499f`. Its exact bytes agree with the normalized source copy supplied by the author. The observed blob is `6ede8ed67569fc1ddf2b4c09f0feb30ca42fca7e`, SHA256 `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`.

Source: [PellMatiyasevic.lean at the pinned commit](https://github.com/leanprover-community/mathlib4/blob/ac77769fabe23cb237559e7f56578dbead91499f/Mathlib/NumberTheory/PellMatiyasevic.lean), theorems `matiyasevic` and `eq_pow_of_pell`.

For each POWER call, set `k=e+1` and `m=b·out`. The first nine equations specialize `matiyasevic` to its positive-index branch:

- `a≥2`, `β≥2`, and `k≥1`
- The three integer Pell equalities imply the source’s natural-subtraction equalities, since each difference is exactly one
- `β=1+4y qb` enforces the required first congruence
- The paired nonnegative quotients enforce each other congruence without restricting the sign of its quotient
- `v=y² qv` gives the divisibility condition with `v>0`
- `y=k+δyk` supplies the required index bound

The last six equations supply precisely the constructive power characterization. They enforce `w≥b,k`, the strict remainder bound `m<T0`, the auxiliary Pell equation, and the modulus identity. The auxiliary Pell equation, `w≥b≥2`, and `g>0` force `a>w≥b`; therefore the polynomial subtraction `a−b` is the same as the natural subtraction in the source theorem. It follows that `b^k=m=b·out`, and cancellation of the positive `b` gives `out=b^e`.

Conversely, the constructive choices in the two source theorems give positive `x,y,u,v,s,t`, positive quotients `qb,qv,g`, and positive strict slacks. The four arbitrary signed congruence quotients are represented as differences of two nonnegative variables. The 11 zero-capable internal values are then positive adapters minus one, while `a,β` are positive witnesses plus one. There are exactly 25 internal positive witnesses and one positive output witness per call.

Seven genuine independently constructed POWER tuples were checked exactly, including exponent zero for bases 2 through 6 and exponent one for bases 2 and 3. Every tuple satisfies all 15 equations and all 26 positive-domain requirements. The largest checked witness is 34,887 bits. These finite constructions test the specialization; they do not replace the all-input number-theoretic theorem. Lean was not run, and no new formalization of the combined sandpile theorem is claimed.

### 3.2 All POWER domains are justified

There is no hidden requirement to quantify exponent bounds separately at every call: they follow from the surrounding, checked equations and positive adapters.

- Tile and patch dimensions are positive; the box multipliers are at least two
- Row and plane radices are powers of 32 at positive exponents
- Every spread length is positive and its equation forces `s≥n+1`, so its copy-base exponent `s−1≥1`
- Every geometric base is at least two; all geometric lengths used here are positive, while the derived interior factors also correctly allow zero length
- Every Sub mask and value is a nonnegative expression or natural adapter
- Each Sub first calls `2^(M+1)`, giving `L≥2`; its other bases are `L` and `L+1`, even when `M=0` or `X=0`
- The shift exponent `ax+A ay+AB az` is positive, and all three box-power bases and exponents satisfy their contracts
- Every exact quotient stream and every geometric unknown is a natural adapter

This is a mathematical dependency order, not a claim that arbitrary positive assignments automatically satisfy every macro domain. Invalid assignments are ruled out by the whole conjunction. All 92 actual call interfaces were compared to these intended uses.

### 3.3 Sub, AND, and stable digit masks

The binomial extraction has both necessary strict bounds. With `L=2^(M+1)`, every binomial coefficient is below `L`; division by `L^X` followed by reduction modulo `L` has the unique extracted digit. Positive slacks force `0<c<L` and `0≤r<L^X`, and `c=2o+1` makes it odd. Thus no adjusted quotient or remainder can fake a one-bit when `X>M` or the coefficient is even. The factorization of `(1+z)^M` over F₂ proves that oddness is exactly binary bit containment.

For AND, `X=W+a` and `Sub(X,W)` mean subtraction is borrow-free, and likewise for `Y=W+c`. `Sub(a+c,a)` is equivalent to disjoint binary supports of `a,c`. Hence every common bit and only a common bit belongs to `W`. All three subset calls are necessary parts of this implementation and are present.

For stable heights, each plane has one permitted bit per base-32 slot. If both upper planes occupied the same slot, their sum would have digit two there, which `Sub(J,T1+T2)` rejects. There is no carry to another base-32 slot. The reconstructed digits are therefore exactly 0 through 5. The patch mask `15J` admits exactly the low four bits per slot, including zero, and rejects all nonzero higher slots.

### 3.4 SPREAD and both input reshapes

For `s≥n+1`, the exponents `i+(s−1)j`, with `0≤i,j<n`, are pairwise distinct. Thus multiplying by the copy geometric sum introduces no coefficient collisions or carries, even for unrestricted full radix digits. A mask-selected exponent `sℓ` satisfies `i−j=s(ℓ−j)`; because `|i−j|<s`, it forces `i=j=ℓ`. The full-bit mask works because each radix is a power of two.

All four necessary spread bounds are paid. The tile’s first stage has `qr` blocks of radix `32^p` and stride `A/p`; the second has `r` blocks of radix `32^(Aq)` and stride `B/q`. Their outputs place tile entries at exactly `x+Ay+ABz`. The second input bound holds since the first output’s largest possible nonzero exponent is at most `(p−1)+A(qr−1)<Aqr`.

The patch uses the same argument with `d,e,f`. Its second input bound is `(d−1)+A(ef−1)<Aef`. Multiplication by `32^(ax+A ay+AB az)` moves physical origin to exactly the local index of `(ax,ay,az)`. Because `ax≥2d`, `ay≥2e`, and `az≥2f`, the complete patch is strictly inside the padded prism, not merely inside its closure.

The lower corner is a multiple of each period. Repetition of the tile by the three geometric factors has a unique mixed-radix decomposition at each prism site. It neither duplicates nor loses coefficients and leaves every background digit in 0 through 5. Thus neither tensor is guessed or accessed through an unpaid table oracle.

### 3.5 Shell, shifts, exterior, and packed conjunction

The three geometric equations uniquely identify the interior factors, since all denominators are positive. Their product gives precisely one low binary bit at each strict interior cell. `Sub(I,U)` therefore makes `U` binary and zero on all six faces.

The lower shell makes division by `32`, `32^A`, and `32^(AB)` exact. The upper shell prevents overflow. The x- and y-face zeros specifically remove row and plane wrap artifacts; a lower-z divisibility argument alone would not have sufficed for that. All six packed streams are therefore exact physical neighbors at every prism site, including its shell.

An outside site can have an inside neighbor only on the shell, whose odometer is zero. The patch is absent outside, and the periodic background is stable. Hence there is no missing exterior inequality or halo variable.

On the left side of balance, every slot is at most `5+15+6=26`; on the right it is at most `6+5=11`. Both are below 32, and every term lies in the same finite set of slots. Positional uniqueness therefore makes the one integer equality equivalent to all site equations. This is a fully paid replacement of the variable site conjunction, not a hidden bounded universal quantifier.

### 3.6 Least action and the distinction from a genuine odometer

Let `u` be a finite nonnegative integer supersolution with global endpoint at most five. If a legal process first attempted to topple beyond `u` at a vertex `v`, its pre-toppling count would equal `u(v)`, all neighbor counts would be at most their `u` values, and its height would be at most the certified stable endpoint. It could not be unstable. Thus every legal prefix is bounded coordinatewise by `u` and has at most `Σu` topplings.

Starting from stable periodic background plus finite additions, every finite prefix has only finitely many unstable sites. Repeatedly selecting one must terminate within this bound at a globally stable state. When `u` is binary, the resulting legal odometer is binary. The supplied lower bound on the endpoint is additional and harmless; the least-action comparison itself uses only its upper bound.

Conversely, any finite binary legal stabilization has finite support. The three box multipliers can be enlarged to contain it strictly, while retaining all four spread inequalities and the patch containment. Its actual endpoint and the proved complete arithmetic macros supply witnesses for every clause.

The distinction is material: two adjacent height-five sites in otherwise zero background have zero legal odometer, but the vector that topples both once is a nonnegative stable supersolution. The fresh exhaustive test found 22 such nongenuine certificates among its three-site fixtures. Consequently adding `U(target)=1` would not certify target firing. No such conclusion or constraint is part of the accepted theorem.

## 4. Edge cases and fresh finite coverage

The independent check completed successfully with the following coverage:

- 4,608 exact binomial extraction/parity cases, including zero mask/value and exponents beyond the mask
- 729 valid Sub witness constructions with both strict slacks checked
- 110,592 candidate AND triples, including false proposed outputs
- 34,408 digit-plane and patch-mask cases, including forbidden digits and nonzero high slots
- 5,006 full-radix spreads, including `n=1`, zero streams, maximal digits, and minimum valid stride
- An explicit failure outside the stride contract, confirming that the bound is substantive
- All 64 combinations of six physical dimensions in `{1,2}`, covering both input reshapes, repetition, physical patch placement, interior masks, all six shifts, and balance bounds at 53,056 prism sites
- 27 extra geometric boxes with side lengths 2 through 4, including empty interior factors (the complete certificate itself has sides at least 4)
- All 2,744 height triples in `{0,...,13}³` on three adjacent sites: direct legal stabilization compared with all eight candidate binary supersolutions, producing 1,446 valid certificates and 22 strictly nongenuine ones
- Seven genuine POWER tuples, 105 exact Pell equations, and all positive adapters
- 257 eight-field Cantor round trips, including the all-zero shifted field tuple, which has `InputPlus=1`

The zero tile, zero patch, zero odometer, and `n=1` spread cases require no exception or disjunction. In Sub at `M=X=0`, use `L=2`, `Y=Z=c=1`, `q=o=r=0`, and both slacks equal to one. For `n=1`, the copy and mask geometric values are both one. Positive adapters represent every zero by one. Full-witness existence in these cases follows from the proved macro completeness; a gigantic combined Pell witness was not numerically materialized.

## 5. Limits and publication wording

The certificate decides an existential integer relation for raw physical tile-and-patch data. It deliberately excludes finitely stabilizing examples that require repeated topplings, such as a height-12 singleton in zero background. This is consistent with its name and theorem.

Connecting the relation to the particular U15 loader still requires that loader’s one-shotness, exact periodic geometry, finite-input placement, and the universal-machine reduction. Report 35’s supplied proof explicitly claims all-site one-shotness and finite-total-toppling equivalence; this audit read those claims as inert dependency text but did not reconstruct its multimillion-component physical graph or its program-to-tape compiler. The new ordinary physical-code decoder does not by itself pay an arbitrary program-to-that-code map.

No claim of unique witnesses or finite-foldness is supported. Enlarging successful boxes yields infinitely many witnesses, as do simultaneous shifts of paired congruence quotients. No equivalence over real witnesses is claimed. No all-input theorem has been established by finite enumeration; the proofs, with the explicit Pell dependency, establish it.

Recommended concise statement: “An explicit horizon-free positive-integer polynomial certificate, of exact degree 18 with 2,566 witnesses and an 11,469-gate implementation, recognizes valid base-32 periodic 3D sandpile instances admitting finite binary legal stabilization. Its packed stream may be a stabilizing supersolution rather than the actual odometer. The constructive Pell power theorem is inherited from pinned mathlib; universal-loader identification remains a separate dependency.”

## 6. Reproduction and pins

Run the independent checker with ordinary Python 3, without `-O`:

`python /workspace/shared/sandpile-fixed-arity-independent-audit-20261004/independent_check.py`

It reads only the submitted JSON DAG and pinned-source text, reconstructs the intended formal clauses itself, and runs its own deterministic finite tests. It does not import the submitted builder, submitted checkers, historical recoders, or Lean. Results are written to `audit-receipt.json`; `audit-run.log` records this audit’s successful run.

Audited authoritative pins:

- DAG: `2e2403097ba0fb65bad349222246157bccad4ac59e99d594b48fa7a678a93723`
- Builder, inspected but not run: `6d123bbb4b20b5bff8b59915e3f7ee320207f39f036ee2143a874c9bdc28bc4a`
- Manuscript including sections 10–11: `40297f9767965fa5c47e310eadcd9bc89dcc3963ee090c93727712cf185a075a`
- Independently fetched Pell source: `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`
- Independent checker: see the self-hash in `audit-receipt.json`

Later changes to these files require affected checks and review to be repeated. The independent source fetch is preserved as inert `pell-pinned-fetch.json` with its verified URL and blob identifier.
