# Report58 independent expanded-source audit

Date: 4 October 2026. Verdict: **PASS** for all four supplied expanded polynomial DAGs.

## Scope and independence

I read `emit_certificate.py`, the four `evidence/*.dag.json` files, `review/ALGEBRA_REVIEW.md`, and the prior POWER construction as inert text/data. I did not import or execute the emitter, the prior builder, any old checker, any saved program or collision schedule, or any physical simulator. The only newly executed verification program was the independently authored and inspected standard-library checker `independent_audit/check_dags.py`.

The checker independently specifies the mathematical residuals as sparse integer polynomials. It resolves and normalizes every DAG gate, compares every named residual and alias against the specification, verifies the literal sum-of-squares tail, and additionally compares the completely normalized output polynomial. It does not rely on the emitter's receipts or its degree/liveness claims. It parses source ASTs without evaluation to verify the full POWER prelude and all fifteen equation pairs against the pinned prior builder.

This is an exact source/algebra audit. The semantic theorem that the fifteen POWER equations represent exponentiation is inherited from the previously audited Pell construction. The reduction from the physical five-signal problem to the stated geometric validity criterion is likewise a prior dependency. This audit does not reprove either dependency, execute physical dynamics, or make a novelty claim.

## 1. Literal accounting

Fixed integer constants are free. Every actual binary `+`, `-`, and `*` node is charged, including multiplication by fixed coefficients. Aliases are names for existing references, not additional leaves or uncharged arithmetic. Both POWER calls are fully expanded and counted.

| Variant | Inputs | Positive witnesses | Equations | Body gates | Total gates | Multiplications | Additions | Subtractions |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Native three-gap, linear residue | 3 | 81 | 44 | 213 | 344 | 136 | 110 | 98 |
| One-input Cantor, linear residue | 1 | 85 | 46 | 230 | 367 | 144 | 118 | 105 |
| Native three-gap, quartic residue | 3 | 80 | 44 | 219 | 350 | 139 | 109 | 102 |
| One-input Cantor, quartic residue | 1 | 84 | 46 | 236 | 373 | 147 | 117 | 109 |

Each POWER block contributes 26 witnesses, 15 equations, and 70 body gates: 31 multiplications, 24 additions, and 15 subtractions. The native linear outer construction contributes 29 further witnesses and 14 equations. In detail its witness counts are 1 radius slack, 12 fraction/Bezout leaves, 1 exponent leaf, 4 valuation leaves, 10 bounded complex-remainder leaves, and 1 strict-acceptance leaf.

For 44 equations, the SOS tail has 44 subtractions, 44 squarings, and 43 additions, totaling 131 gates. For 46 equations it has 137 gates. Cantor decoding adds exactly four positive witnesses, two equations, and seventeen body gates, hence 23 gates overall. Replacing `s+t=5` by the quartic removes one witness and adds six gates, without changing the number of equations.

Native linear region ledger:

| Region | Witnesses | Equations | Gates | × | + | − |
|---|---:|---:|---:|---:|---:|---:|
| Radius and transformed coordinates | 1 | 1 | 22 | 12 | 6 | 4 |
| Primitive fraction | 12 | 4 | 14 | 7 | 2 | 5 |
| Exponent natural conversion | 1 | 0 | 1 | 0 | 0 | 1 |
| POWER(5,n) | 26 | 15 | 70 | 31 | 24 | 15 |
| Valuation/remainder | 4 | 3 | 5 | 2 | 2 | 1 |
| Extraction bases | 0 | 0 | 4 | 2 | 2 | 0 |
| POWER(3+4b,n) | 26 | 15 | 70 | 31 | 24 | 15 |
| Bounded complex remainder | 10 | 5 | 17 | 3 | 3 | 11 |
| Strict acceptance | 1 | 1 | 10 | 4 | 4 | 2 |
| SOS | 0 | 0 | 131 | 44 | 43 | 44 |

Every input, positive witness, and gate is reachable from the final output in every variant. There are no dead variables or dead arithmetic nodes. References are canonical, all gate references point backward, the declared equation sequence is complete, and all region intervals are contiguous and cover the source. The checker verifies region witness/equation allocations as well as totals.

## 2. Ordinary-integer domains

The theorem's leaves, including the input(s), range over strictly positive ordinary integers. A mathematical natural variable is represented by its positive `Plus` leaf minus one. Every signed integer is represented by a difference of two positive leaves. Every signed value is attainable: for example, any integer z equals `(max(z,0)+1)−(max(−z,0)+1)`. Nonuniqueness introduces no false restriction.

The POWER parameters `a` and `beta` are positive leaves plus one, hence at least two. All eleven natural POWER auxiliaries use positive leaves minus one. `strict` is positive, so `M=m+strict` imposes the required strict bound. The `rho`, `alpha`, `sigma`, and `tau` pairs preserve two-sided congruence quotients.

`n=valuation.n.Plus−1` is nonnegative before either POWER call is interpreted. The first base is 5. The positive output leaf P ensures `b=4P+1≥5` and `3+4b=16P+7≥23` before exponentiation semantics are invoked. Both bases exceed the required lower bound 2. Once `P=5^n` is known, P can still equal 1 when n=0, so the sharp second-base lower bound remains 23.

The complete zero condition is asserted only over these integer domains. It is not a claim about real zero sets or real quantifier elimination.

## 3. Every outer equation

The following are exactly the normalized identities found in each relevant DAG, after expanding the aliases. In the native version `g1,g2,g3` are the three positive input leaves. In the one-input version they are positive witnesses.

Set

- `D=g1+g2+g3`, `x=g1`, `y=g1+g2`
- `A=3x−D`, `B=3y−2D`
- `U=6A−13B`, `V=13A+6B`

The radius residual is

`4D² = 205(A²+B²)+delta`, with delta natural.

The four primitive-fraction residuals are

`U=hu`, `V=hv`, `2D=hq`, `c1u+c2v+c3q=1`,

with h,q positive and u,v,c1,c2,c3 signed. This is exactly the common-positive-denominator/Bezout construction in the algebra review. In particular `V=13A+6B` has the required orientation.

The first expanded POWER block defines `P=5^n`. The three valuation residuals are

`q=Pr`, `r=5k+s`, and `s+t=5`,

with r,s,t positive and k natural. Thus s is one of 1,2,3,4. The quartic variant replaces only the last residual by

`(s−1)(s−2)(s−3)(s−4)=0`.

Over integers this imposes exactly the same four choices. The positive complement t in the linear version is essential and is present.

Set `b=4P+1`; the second expanded POWER block defines `T=(3+4b)^n`. The five bounded-remainder residuals are

`C+P=l1`, `P−C=l2`, `S+P=l3`, `P−S=l4`,

`T−C−bS=kappa(b²+1)`,

with C,S,kappa signed and l1,l2,l3,l4 natural. These impose the intended inclusive bounds and exact congruence. As proved in the algebra review, they uniquely extract `C+iS=(3+4i)^n`; no bound on kappa is needed.

The last residual is

`delta²+(r−1)²+(u−C)²+(v+S)²=acceptance.positive`.

The right-hand side is a strictly positive leaf, so this is exactly the required strict positivity condition, not a nonnegativity relaxation. In particular the sign is `v+S`. Given the reviewed arithmetic reduction and the prior exact POWER semantics, this accepts precisely the claimed input predicate, including n=0.

No outer equation is missing, altered, or added. The fourteen native outer residuals and thirty expanded POWER residuals total forty-four.

## 4. One-input Cantor encoding

For the positive single input `code`, set `a=g1−1`, `b0=g2−1`, and `c=g3−1`, all natural. The extra natural inner witness j obeys

`2j=(b0+c)(b0+c+1)+2c`,

`2(code−1)=(a+j)(a+j+1)+2j`.

These are the standard integer equations for `j=π(b0,c)` and `code−1=π(a,j)`, where `π(s,t)=(s+t)(s+t+1)/2+t`. This pairing is a bijection on pairs of naturals: on each diagonal s+t=d, its values are exactly the interval from d(d+1)/2 through d(d+1)/2+d. Thus every positive code decodes to exactly one positive triple, and each positive triple has a unique positive code. No fractional coefficients, division gates, partial decoding, or externally executed decoder is present in the polynomial source.

The two added residuals have exact degree two. They preserve every downstream equation and its domains.

## 5. POWER identity with the prior pinned source

The checker reads the current POWER method and the inert copied prior method with `ast.parse`. It compares every statement from parameter conversion through the complete fifteen-pair equation list after only these declared renamings:

- `name` to `prefix`
- `out` to `z`
- `pp` to `p`
- `nn` to `d`
- `delta` to `dlt`
- witness suffix `modulus` to `M`

The ASTs match exactly. This covers all positive/natural declarations, intermediate definitions, congruence slacks, strict modulus slack, and all fifteen equations. The copied prior builder was additionally byte-hash compared with the actual prior `matrix-chronological-certificate-20261004/build_certificate.py`; they agree. The accompanying `POWER_SOURCE_NOTES.md` likewise matches the prior `SOURCE_NOTES.md`.

The prior builder's SHA256 is `722db1e253ac3d241fdb538c46a86ffc15e6c208cb8116d168883b6c5bfaa799`. No POWER equations were omitted behind a macro name. Independently of the AST comparison, the checker normalizes all thirty emitted POWER residuals and compares them against a mathematical transcription of the fifteen equations with their actual bases and exponent expressions.

The emitter has only fixed-size source construction: the two POWER calls each have fifteen equations and fixed auxiliary lists. No input, exponent, witness magnitude, or physical trajectory controls the number of gates or variables. Fixed source loops are compatible with the fixed polynomial claim.

## 6. Exact normalized degrees

All degrees below are in the independent input and positive witness leaves, after exact normalization; they are not inferred solely by syntactic propagation.

For either POWER block, residuals 1,2,3 have degree 4; residual 6 has degree 3; residual 13 has degree 6; residuals 4,5,7,8,15 have degree 2; and residuals 9,10,11 have degree 1. Residuals 12 and 14 have degree 1 in POWER(5,n), and degree 2 in POWER(3+4b,n).

The radius, four primitive-fraction, denominator decomposition, and final strict-acceptance residuals have degree 2. The valuation quotient/remainder residual has degree 1. The linear residue selector has degree 1 and the quartic selector degree 4. The four complex bound residuals have degree 1; the complex congruence has degree 3. Each Cantor residual has degree 2.

| Variant | Degree 1 residuals | Degree 2 | Degree 3 | Degree 4 | Degree 6 |
|---|---:|---:|---:|---:|---:|
| Native linear | 14 | 19 | 3 | 6 | 2 |
| One-input linear | 14 | 21 | 3 | 6 | 2 |
| Native quartic | 13 | 19 | 3 | 7 | 2 |
| One-input quartic | 13 | 21 | 3 | 7 | 2 |

For either POWER instance, residual 13 is

`a²−1−((w+1)²−1)(wg)²`.

Its leading degree-six term is `−w⁴g²`. Its square contributes `w⁸g⁴` at degree twelve. The two blocks use distinct w,g leaves. Exact normalization verifies coefficient **1** for this monomial in the complete final polynomial for each block. Therefore the exact output degree is **12** in all four variants, not merely at most twelve. The general noncancellation argument by a sum of real homogeneous squares also applies.

The completely normalized outputs have respectively 772, 802, 775, and 805 nonzero monomials in the table's variant order. Their hashes and every normalized residual hash are recorded in `audit-receipt.json`.

## 7. Adversarial corruption tests

The checker rejects eight independently applied corruptions in each of the four variants, for **32 rejected mutations**:

1. Remove an outer equation
2. Add an undeclared/dead witness
3. Change the radius coefficient 205 to 204
4. Insert an invalid forward gate reference
5. Relax the stated positive-leaf domain to nonnegative
6. Drop the final squared residual from the output
7. Change the forbidden-orbit test from `v+S` to `v−S`
8. Corrupt POWER equation 13

Mutations are made only to private in-memory copies, leaving every supplied DAG untouched. The JSON receipt records the exact rejection reason for each. These tests support the checker's sensitivity; they do not replace the all-equation identity checks or the mathematical proof.

## 8. Reproducibility and source pins

Run only the fresh checker:

`python -I independent_audit/check_dags.py`

It reads the source files inertly and writes `independent_audit/audit-receipt.json`. The checker uses only Python's standard library. It does not need to rebuild any DAG or run any prior program. The packaged inert prior source is sufficient; if the original prior builder is locally present, its byte identity is also checked.

Source pins:

- Emitter: `2093773340d3e7a9891d786e99711a2662a61b952b1c40a8bb1af5392d33ac6d`
- Native linear DAG: `707721d1a8dca21b29acda57df8df6e763a1df89761f513122bec5edd9261ccc`
- One-input linear DAG: `b64a268cc03033c13c020abc0cb12c1c81f9ba630aa75812ac84b08e2971efc3`
- Native quartic DAG: `11c1a3d6eca23af2a9ede232e1a5ab36ba395a3235a424ef76ff14d5e19f14d0`
- One-input quartic DAG: `3d2fe384ea6564950e0ca4b392396e3fa4489d88e1974dfd269a42610428ed24`
- Algebra review: `d640360159e2ec6436bc85c2e61a079bded5654ac372aca6e69588d7fd56e2b5`
- Prior POWER source notes: `56051940c6ce974dd891f2fb549ece313b710d9ac60ee1591c4e976887ca2435`
- Prior builder: `722db1e253ac3d241fdb538c46a86ffc15e6c208cb8116d168883b6c5bfaa799`

The checker itself and the Pell dependency files are additionally pinned in the machine-readable receipt. The review/checker/receipt manifest in this directory pins all three delivered audit artifacts.

## Conclusion

The supplied native and Cantor-encoded ordinary-positive-integer polynomials match the documented construction exactly, with the operation and witness counts above, and exact degree twelve. Both residue selectors are correct over the declared domains. All arithmetic is explicit and live, and both POWER modules exactly preserve the prior fifteen-equation construction. The remaining theorem dependencies are precisely the prior POWER semantic result and the prior five-signal geometric validity result.
