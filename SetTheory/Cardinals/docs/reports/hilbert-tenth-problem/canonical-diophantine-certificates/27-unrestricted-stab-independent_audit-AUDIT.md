# Root-assigned adversarial audit: unrestricted finite global stabilization

Date: 4 October 2026. Verdict: **PASS, conditional on the explicitly pinned constructive Pell theorem**. No mathematical defect, source mismatch, unpaid operation, invalid domain use, or fixed-bound obstruction was found. No repair to the frozen packet is requested.

This is an independent audit of the exact language and polynomial in `sandpile-unrestricted-stabilization-20261004`. It is not a claim of undecidability, a formal proof-assistant verification, or a test of a complete astronomical Pell witness. The author and the author's prior child audits were not used as executable authorities. Their text was read, then the system was independently reconstructed.

## 1. Frozen object and audit method

The authoritative input DAG has SHA256:

`8622585bcafaf9b3aee84e12f229beb17a33d27d6f1bf0b6cb6bc956ee4ac759`

The builder hash is `47c2e5c63ea6eceef26c4bd117ca8a195eb5180e00482f9d9384a7705788fb2c`; the audited proof hash is `1d426f591b2f9cdbf552fcc151515a7c402bb7c4b06a127bae8ab35de88e4579`.

The original packet was preserved. Its builder, checkers, schedules and all upstream programs were read only as data; none was imported or executed. No Lean process was run. Three fresh, inspected programs in this audit directory were executed:

- `check_exact.py`: independent sparse integer-polynomial reconstruction of the specification, comparison against the inert DAG, reference and operation validation, exact sum-of-squares verification, ledger, liveness, and exact degree
- `check_semantics_fresh.py`: new finite adversarial checks of bit extraction, AND, SPREAD, count masks, spatial shifts, tensor geometry, and the required separators
- `challenge_checker.py`: ten deliberately damaged temporary DAGs, tested against this audit's checker in normal and optimized Python

The exact checker derives its own mathematical system before loading the submitted DAG. It does not use submitted metadata as the specification. It checks every residual coefficient dictionary against that independently derived system, allowing reversal of both sides of an equation; such a reversal leaves its squared residual exactly unchanged. It checks all macro and public port polynomials without a sign relaxation. It then verifies the exact tail consisting of all residual squares and their sum. Consequently this is exact all-assignment polynomial correspondence, not randomized evaluation.

## 2. Exact input language and positive domain

The seven Cantor constraints uniquely decode the natural ordinary input `InputPlus−1` into the right-associated tuple `(p−1,q−1,r−1,T,d−1,e−1,f−1,D)`. All six dimensions are positive leaves; T, D and the six intermediate codes are positive-minus-one natural adapters. Multiplication by two avoids an unpaid division in Cantor decoding. Leading zero slots are permitted; nonzero slots beyond the declared volumes are rejected by the masks.

The raw tile validator gives one bit in each of three bitplanes per base-32 slot. The additional Sub constraint on the unweighted second-plus-third planes rules out simultaneous 2 and 4 contributions. Since their slot sum is at most two, it cannot evade the test through a radix carry. Thus it gives exactly 0–5. The patch mask `15G(32,def)` gives exactly 0–15 in the declared patch slots. This validates the same physical code before any precision is chosen.

The theorem is precisely existence of a finite legal toppling sequence ending globally stable on the original six-neighbor lattice. It does not assert infinite locally finite stabilization, recognition of a specified target, or that a proposed supersolution is the true odometer. The patch alphabet stays 0–15; unrestricted refers to toppling multiplicities.

## 3. POWER dependency: independently checked theorem translation

The local pinned `PellMatiyasevic.lean` source was read as text. Its hash is exactly the declared `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`. The statements and the relevant constructive directions of `matiyasevic` and `eq_pow_of_pell` were examined. This audit authenticates agreement with that pinned local source; it does not newly compile or independently reprove mathlib.

For `POWER(b,n,o)`, take the source theorem's positive index to be `k=n+1` and its represented value to be `m=bo`. Equations 1–9 translate the positive-index branch of `matiyasevic`; equations 10–15 supply precisely the witnesses required by `eq_pow_of_pell`. It follows that `b^(n+1)=bo`, and positive b can be cancelled. Conversely, `o=b^n` supplies the source theorem's value at index n+1.

The stronger positive leaf domains do not accidentally discard completeness:

- k is positive, and `y≥k`, so y is positive and the zero-index Pell branch cannot occur
- Pell identities force x, u and s positive; v is explicitly positive in the theorem
- beta is greater than one and congruent to one modulo positive 4y, hence `beta=1+4y·qb` with positive qb
- `v=y²qv`, with v and y positive, gives positive qv
- t cannot be zero: `t≡k mod 4y`, while `1≤k≤y<4y`
- the source parameter g cannot be zero because then equation 13 would give `a²=1`, contrary to a≥2
- the modulus M is strictly above positive m; the strict slack is positive
- w is at least b≥2

All remaining differences or paired congruence quotients may be zero and correctly use natural adapters. Paired natural multiples express either sign of an integer congruence. Equation 13, with positive w and g, forces a>w≥b, so the displayed integer `a−b` agrees with the source theorem's natural subtraction. Natural identities `x²−dy²=1` correspond to ordinary integer equalities `x²=dy²+1`: a truncated natural subtraction equal to one cannot be in its truncation branch.

No generic MRDP existence theorem is substituted for these explicit clauses. The number-theoretic dependency remains an explicit limit of the audit.

## 4. Sub, AND and SPREAD challenges

For natural M, `ell=2^(M+1)` is strictly larger than every binomial coefficient in `(ell+1)^M`. The two strict slacks make the extracted odd digit genuinely the digit indexed by U, with a nonnegative higher quotient and a remainder smaller than `ell^U`. If U>M that digit is zero, so no odd extraction is possible. M=U=0 succeeds. Binary binomial parity gives exactly the submask predicate.

For AND, the two Sub conditions on W make `X−W` and `Y−W` borrow-free. If A and C have a common one-bit, their lowest common bit starts a carry and that bit cannot remain in A+C; conversely disjoint bits cause no carry. Thus `Sub(A+C,A)` is exactly their disjointness. Together the constraints give W=X AND Y.

In SPREAD, `s≥n+1` ensures the terms at exponents `i+(s−1)j` are distinct; each term coefficient stays below b. The selector mask has full base-b digits at exponents sj. Modulo s the copied exponent is i−j, whose absolute value is less than s, so exactly i=j remains. This use of binary AND requires a power-of-two base. That requirement is actually established at every invocation. The fresh test finds the immediate failure at base 3, n=1, s=2, V=1 (formula returns 0 rather than 1), showing why the hypothesis must not be relaxed.

Each SPREAD has its own paid stride gap, range slack, three direct POWER calls, two geometric equations and paid AND. No array operation or unexpanded bit predicate survives in the polynomial DAG.

## 5. Precision and capacity are not circular

Positive L first gives b=32^L≥32 through a POWER whose base is the constant 32. The exact equation `16h=b` then gives `h=2^(5L−4)≥2`, so c=h−1 is natural and a contiguous low-bit mask. No floor operation is used.

Both paid raw conversions are present and feed their respective spatial embeddings. Their gaps force `L≥pqr+1` and `L≥def+1`. Therefore every actual complete certificate has L≥2 and b≥1024. The balance estimate is valid even at b=32, but b=32 is not an attainable complete certificate radix. The proof states this distinction correctly.

For the interior indicator I, `cI` has exactly the low `5L−4` bits at each permitted slot. They do not overlap adjacent slots. Sub(cI,U) therefore allows every digit from 0 through c, excludes every higher digit and every shell/outside slot, and implies U<Q independently of balance. This avoids a circular argument in which a nonexistent carry bound is inferred from the balance equation itself.

## 6. Tensor geometry, ranges, and exterior

The half-extents `hx=pd tx`, `hy=qe ty`, `hz=rf tz`, with padding at least two, give side lengths at least four and period-aligned lower faces. The finite patch lies strictly inside. The tile row reshape produces exponents `x+A(y+qz)`. In the next base `b^(Aq)`, each digit block has exponents below Aq, since x<p≤A and y<q; hence the second reshape's entire input is below its paid range. The plane reshape gives `x+Ay+ABz`. The patch calculation is identical with d,e,f. All four independent spatial gap inequalities can be met by increasing tx and ty; they do not constrain L from above.

The three tile repetition factors have unique coordinate representations `x+pi`, `y+qj`, `z+rk`. Thus each box site receives exactly one original tile digit, rather than a sum of overlapping copies. Period alignment makes the local pattern the actual physical pattern at the negative lower corner. The patch translation by `hx+Ahy+ABhz` places its original digits at the original physical coordinates. The constructed initial packed coefficients are exactly the background plus patch, at most 20.

The trimmed geometric equations uniquely yield `jx=G(b,A−2)`, `jy=G(X,B−2)`, `jz=G(Y,C−2)`. Their product with bXY is exactly the strict-interior indicator. All six faces, not only the first and last packed positions, are zero in U.

That whole shell is essential. Without the x upper face, multiplying the packed site (3,1,1) in a 4×4×4 prism by b spuriously produces (0,2,1). The actual mask excludes it. For a strict-interior source, all six index shifts remain genuine lattice neighbors within the box. The three negative divisions are exact because every source index is at least `1+A+AB`. Shell receiving sites are retained in the all-slot endpoint and balance, so boundary chips are not discarded.

Any exterior site has only zero-u neighbors across a box boundary, because those neighbors are on the shell. The patch is internal and the periodic background is stable. Thus the exterior endpoint is exactly the original stable background. There is no hidden sink or missing infinite exterior condition.

## 7. Carry-free balance and least action

Before the packed equality is used, every uncarried coefficient satisfies

- left: `0≤coefficient≤20+6c=3b/8+14<b`
- right: `0≤coefficient≤6c+5=3b/8−1<b`

At b=32 the bounds are 26 and 11. All streams are supported within the N slots. Consequently both sides are canonical finite base-b expansions, and the one integer equality is exactly the complete set of sitewise natural stable balance equations. There are no untested top carries or borrows.

Let a finite natural u satisfy global endpoint height at most five. In a legal prefix, consider the first toppling that would exceed u at v. Immediately before it, m(v)=u(v), while neighbor counts are at most u. The current height at v is at most the proposed stable endpoint, hence at most five: contradiction. This is valid for arbitrary natural multiplicities and does not require the supplied u to be legal.

Every legal prefix is thus pointwise bounded by u and has length at most its finite sum. Continuing whenever an unstable vertex exists must terminate within that bound; at termination every vertex is stable. No fairness, limit, compactness, or infinite stabilization notion is used. Conversely, a finite legal global stabilization directly supplies a finite natural odometer and a nonnegative stable endpoint. The imposed endpoint nonnegativity therefore does not weaken the existence equivalence.

Completeness has no fixed count or horizon: choose L above both raw volumes and large enough that `32^L≥16(max u*+1)`, and independently choose a sufficiently large period-aligned prism containing the true odometer support strictly inside and meeting the four gaps. Both choices can grow without bound. The actual endpoint need not have finite support; only its box restriction is packed, with the stable background supplied outside.

## 8. Required separators

1. Zero background, single patch height 12: any binary u would leave the origin height at least `12−6=6`, regardless of neighbor contributions. Two legal origin topplings give origin zero and all six neighbors two. Thus unrestricted acceptance genuinely goes beyond the binary certificate.
2. Zero background, adjacent patch digits [12,4]: the legal sequence origin, origin, neighbor stabilizes, with counts [2,1]. The final origin is one and the adjacent site zero; all other affected sites are at most two.
3. Adjacent heights [5,5], zero elsewhere: the empty legal sequence is already a stabilization, so the true odometer is zero. Nevertheless u=1 at each of the two sites gives a nonnegative stable endpoint. The certificate may and must accept this nonleast supersolution without describing it as legal.
4. Uniform height-five background plus one added chip: for any finite-support u, sum the endpoint's excess over five on a finite set containing the patch, support and all neighboring sites. The finite Laplacian cancels, leaving total excess one. Stability would make all terms nonpositive, impossible. The origin can still legally fire once, so target firing is not finite global stabilization.

The fresh finite checker verifies all four fixtures or their finite conservation identities. The universal impossibility in the fourth fixture follows from the argument just given, not from the 100 test assignments.

## 9. Exact reconstruction and ledger

All 1,897 equation residuals, 164 macro records, 33 public ports, and all 3,263 formal variable names including the input were checked. There are no unaccounted-for equations, macros, variables or ports; all references are valid and acyclic. The primitive gate alphabet is exactly binary +, − and × with fixed integer constants.

- Positive existential witnesses: 3,262
- Equality residuals: 1,897
- Body: 8,881 gates = 3,837 multiplications + 3,101 additions + 1,943 subtractions
- Sum-of-squares tail: 5,690 gates = 1,897 multiplications + 1,896 additions + 1,897 subtractions
- Total: 14,571 gates = 5,734 multiplications + 4,997 additions + 3,840 subtractions
- Macros: 117 POWER, 28 Sub, 6 AND, 6 SPREAD, 5 geometric and 2 stable
- Dead gates: zero; dead witnesses: zero; input is live

The exact residual degree is at most nine. Only `patch.shift.eq8`, `.eq9`, and `.eq11` attain nine. Their degree-nine terms are each `−4pqrdef tx₀ty₀tz₀`, where the three padding symbols here denote the actual positive witness leaves before adding one. The degree-eighteen homogeneous part of the whole final polynomial is therefore exactly

`48(p q r d e f tx₀ ty₀ tz₀)²`.

It is nonzero. The degree is exactly 18, not only an upper bound obtained by gate propagation.

The fresh source's construction AST uses only +, − and × arithmetic; imports are the stated standard-library modules. The builder is fixed syntax and never receives physical dimensions as runtime quantities to decide how many equations to emit. The audit did not run it, so no new claim of builder runtime replay is made. The frozen emitted DAG itself has been exactly reconstructed.

## 10. Fresh checks and checker challenges

Normal and optimized Python both passed the newly authored checkers. The finite semantic receipt records:

- 1,886 exact binomial-digit/Sub cases, including out-of-range indices
- 11,440 candidate AND witnesses
- 15,150 SPREAD cases
- 512 stable-bitplane cases
- 1,675 individual cap-bit checks over 25 precisions, plus endpoint and carry checks
- all 6,561 assignments of counts 0, 1 and 63 on the eight interior vertices of a 4×4×4 prism, checking every positive and negative neighbor stream
- five independent nonconstant anisotropic tensor geometries, totaling 9,024 checked physical slots
- both carry extrema, explicit row-wrap and non-power-of-two counterexamples, repeated-count and nonleast fixtures
- 100 finite conservation challenges for uniform five plus one chip

The checker was additionally challenged with ten corruptions: removing the exact-sixteenth relation, replacing the capacity with a binary mask, dropping a neighbor, falsifying a precision port, dropping endpoint digit exclusion, bypassing a raw conversion, weakening the shell mask, altering a POWER congruence, changing the final output, and removing a witness. All ten were rejected both normally and under `python -O`, for 20 expected rejections. The hash guard was explicitly disabled only for these temporary mutated copies, so the failures exercised semantic/structural checks rather than just the frozen hash. No rejected run wrote a PASS receipt.

These finite checks are corroboration and regression checks; the all-input conclusion rests on the inspected proofs and exact symbolic reconstruction. They do not instantiate the gigantic nested POWER witnesses.

## 11. Final scope and stopping point

The audited polynomial, over its stated strictly positive integer domain, represents exactly the unchanged raw eight-field physical inputs admitting a finite legal global stabilization, with arbitrary finite natural toppling counts. The conclusion is conditional on the pinned constructive Pell characterization and its stated domain; this audit adds no stronger claim about formal verification.

No proper reduction from a separately authenticated global-halting source was checked here. Therefore no hardness or undecidability corollary is asserted. A first-firing alarm would not establish the needed statement, as the uniform-five separator demonstrates. The audit also makes no real-witness, unique-witness, finite-fold, fixed-horizon or target-recognition claim.

**Final result: PASS; no corrective action required for this certificate.**
