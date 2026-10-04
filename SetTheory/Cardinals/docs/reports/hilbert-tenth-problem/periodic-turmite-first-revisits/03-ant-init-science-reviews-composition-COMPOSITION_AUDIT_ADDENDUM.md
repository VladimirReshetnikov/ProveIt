# Independent all-length composition audit addendum

## Decision

**PASS for the fixed all-length initialization component, conditional on the explicitly pinned parent geometry, frozen literal-ant interface, and constructive Pell theorem. PASS for the qualitative existential halting-equivalence composition with the parent history and endpoint selector. No numerical universal bound is certified.**

This is a separate continuation of the already completed initialization audit. `/workspace/shared/literal-ant-initialization-independent-audit-20261003/AUDIT.md` and its scoped result are unchanged. The present addendum addresses the additional raw-input recoder splice, its domains and literal source, and an optional initializer-only degree/folding result.

The old snapshot synchronization issue was resolved before final review: the composed generator now reads the authoritative final inline recoder JSON, including its explicit output map. Its nodes/witnesses were also verified equal to the earlier port-form snapshot; deleting that snapshot's last three equalities gives exactly the final inline equations. This was a provenance correction, not a mathematical counterexample.

## 1. Exact sources and dependencies

The copied final files reviewed here have SHA256:

- Wrapper `bridge_dag.py`: `08491ae6aaf2084c948276c383d37a28bb3c05376db98157b9831b1bb634c2d6`
- Composed source `compose_initialization.py`: `af0493a2b6531566647e94da18b52dc79f7f0b94d49f0ee74eb75e717b2622d1`
- Composition proof: `1c999ac1c97c0fc3b7b6e1925c45aec54a3820be82ca2c97ee25a0597ba5c322`
- Authoritative inline recoder JSON: `a8fbf064395d2fac5aa041a4c54826938ea2645fba793e0de7500e19f7ca4567`
- Recoder proof: `6ada76c9a076d08a2b3ec448ac68dff9b7b76d0cf8fc616ce86ed0706249787a`

The recoder's explicit constructive dependency is mathlib4 commit `ac77769fabe23cb237559e7f56578dbead91499f`, `Mathlib/NumberTheory/PellMatiyasevic.lean`, SHA256 `993760c797ad0ff66fa77064a616fce779550bc745cbf6c44e04f392fd0bed0a`, specifically `matiyasevic` and `eq_pow_of_pell`. Its detailed all-integer specialization was separately audited in `/workspace/shared/audit-digit-dilation-bridge/AUDIT.md`. We read the final recoder proof and that audit, checked the composition domains below, and independently parsed its exact final arithmetic graph. We do not claim a second formal proof of the upstream Pell theorems.

The original audit pins the inherited 174-operation note, frozen interface proof, exact anchor, endpoint contract and Report40 sources. No upstream code, downloaded Lean program, saved arithmetic schedule, dense ant board, or enormous numeral prefix was executed in this audit.

## 2. Literal topology and exact boundary

The only seven external expression ports actually used by the composed source are:

`RawLeft, RawRight, W, Wp, Q, InitialHead, InitialMemoryPlus`.

All are positive under the stated contract. `W,Wp,Q` are already parent witnesses; the initial memory and head are already positive parent ports. Their reuse does not create new component witnesses.

The final inline recoder contains exactly 1,055 nodes, 228 equations and 392 positive witnesses, with 454 multiplications and 601 additions/subtractions. Its output map is:

- `A=g1051`, a product of two positive radix powers
- `B=R_radixPower`, an existing positive witness
- `T=g1054`, a nonnegative expression that can be zero

The host's four positive witnesses are disjoint from the namespaced recoder witnesses. The composed source does not quantify any additional A/B/T coordinate, and no free A/B/T or G port survives into a primitive gate or equation. In particular a zero `T` does not violate the positive-witness convention.

The exact shared radix is node 25. Independent monomial propagation through the prefix shows it is `W^576000`, obtained with precisely 23 multiplications. It is computed before the recoder is inserted and is reused by all fourteen exponential macros. The recoder occupies node interval `[32,1087)`. The final host aliases are:

- A → node 1083
- B → `Recoder:R_radixPower`
- T → node 1086

Every primitive operand and equation endpoint was independently validated against already available nodes, the seven external ports, the 396 declared positive witnesses, or prescribed constants. No forward reference, undeclared input, hidden quotient, exponent instruction or digit-extraction instruction remains. The three output mappings are wire aliases, not asserted equations. The wrapper's multiplication `A*G` remains paid.

The independently reproduced source hash, including all gates and equation assertions in exact source order, is:

`503215b20d317cfb9e6e40ec82eb26044afbdedf26f37e03029bcd7dc0a04130`.

## 3. Domains and all-length initialization iff

The parent geometry gives `W=3^w` with odd `w>=3`, hence the recoder's shared base `G=W^576000>=2`. Each raw input is an arbitrary positive integer and therefore has exactly one standard binary sentinel length and payload, including code one for the empty word.

The two recoders' seven power calls have valid domains in dependency order. The G-base and base-two calls first recover the radix and binary powers. The auxiliary radix is `B=2^(GP+2)>=2`, so its power call is valid. The nonnegative repunit adapter gives `U>=0`, so `L=2^(U+1)>=2`; the subsequent bases L and L+1 are valid. Every exponent is a nonnegative expression forced by a positive adapter or is a positive sum/product of already positive expressions. Thus the wrapper introduces no missing base or index hypothesis for the Pell macro.

The final recoder theorem gives, for uniquely sentinel-derived L,R:

`A=G^(L+R)`, `B=G^R`,

`T=G^(R+1) sum ell_j G^j + sum r_j G^(R-1-j)`.

Left reversal and right forward orientation therefore give exactly the old wrapper polynomial of `reverse(ell),0,r`. The central zero is intentional; the A0 head's physical bit is separately supplied by the wrapper's B term. Empty and zero-only words remain admitted with correct marker placement and length-dependent powers.

Substitution of these expression outputs into the already audited wrapper proves soundness of the composed initializer: its positive solutions describe exactly widths `w=1+au`, heights `h=2kv`, with `a>=2`, `k>=L+R+1`, initial head `3^u W^(kv)`, and the precise periodic-plus-anchor-plus-input board in the claimed translated rectangle.

Conversely, for any such rectangle and raw words, the recoder's all-input completeness theorem supplies its 392 positive witnesses. The wrapper's four witnesses are the already proved positive quotients/powers. In particular `P=G^(k-L-R-1)` may equal one at the tight boundary. Their namespaces are disjoint and their only shared non-raw input is the exact already-computed G. Hence no compatibility constraint is lost by joining the two systems. This proves an iff for one fixed source at every length, rather than merely a circuit family.

## 4. Exact initializer ledger and literal constants

The exact count is:

- 1,153,192 multiplications
- 1,153,195 additions/subtractions
- **2,306,387 total operations**
- **234 equations**
- **396 new strictly positive witnesses**

This is the sum of the 2,305,332-operation fixed wrapper and the 1,055-operation inline recoder, with G shared once. No operation is removed by deleting free output comparisons because equalities are not primitive arithmetic gates under the declared convention. The seven external/inherited ports are excluded from the 396 new witnesses.

The recoder's only small numerals are 1,2,4. The bridge's paid constant prefix already constructs two. One extra addition constructs four, for example `4=2+2`. Thus the combined literal-1/3 prefix is:

- 277,193,130,853,952,587 M
- 277,193,130,853,952,485 A
- **554,386,261,707,905,072 extra operations**

Adding the initializer yields **554,386,261,710,211,459 operations** under that deliberately unoptimized strict grammar. This remains a recipe/count theorem: the astronomical prefix and coefficients were neither materialized nor evaluated. It pays neither the parent's numerals nor endpoint or global equation-folding costs.

## 5. Qualitative history and endpoint composition

The qualitative corollary in the composition proof is sound. Existentially bind the parent's five positive parameters `InitialMemoryPlus, FinalMemoryPlus, InitialHead, FinalHead, FinalSignPlus`, retain all its existing positive witnesses including W,Wp,Q, and join the initializer and the normalized endpoint selector by their exact wires.

For soundness, the parent proves a positive finite no-escape ant history. The initializer identifies its initial word and north-facing even-parity head with the finite restriction of the exact infinite literal load. Deterministic step induction identifies every certified state with the infinite trajectory. The endpoint's single reachable normalized residue/heading clause is unchanged by the period-multiple translation. The frozen interface theorem therefore implies U15 halting.

For completeness, the frozen interface reaches its accepting event after positive finite time whenever the raw U15 configuration halts. Its finite prefix fits some allowed odd-width/even-height rectangle with the proved symmetric translation. The initializer, parent and endpoint positive converses then provide all witnesses simultaneously. The two memory adapters are positive even for zero memory; the head monomials are positive; the east-facing white endpoint has `FinalSignPlus=1`. No zero-time acceptance or forbidden zero coordinate is needed.

This establishes the fixed raw-pair halting relation qualitatively. It does not establish a numerical operation/variable/degree bound for the fully joined universal system, does not implement the separately published arbitrary-program-to-U15 compiler, and does not assert physical ant halting. A Report42 statement must keep these scopes explicit.

## 6. Optional exact initializer-only polynomial degree and folding

The degree convention is total degree in the seven external/inherited ports and all 396 supplied positive witnesses, each assigned degree one; prescribed fixed numerals have degree zero. Every gate expression is substituted. Parent equations are not substituted or eliminated.

`audit_degree.py` independently propagates degree upper bounds through every one of the 2,306,387 actual composed gates, storing only a four-byte degree per node. All 234 residuals have upper bound at most **1,152,000**. Exactly zero-based residuals 16 and 130 attain that bound; all other upper bounds are at most **1,127,949**.

Those two residuals are the left and right first exponential macro equations

`2aG - (T + G^2 + 1)`.

The actual source records were checked to have this exact shape. Their first term has degree at most 576001, T has degree one, and `G=W^576000`. Consequently each has unique top homogeneous term `-W^1152000`. This gives an exact lower bound, not merely a possibly loose max-propagation result. The maximum residual degree is therefore exactly **1,152,000**.

Replacing all 234 asserted residual equations by the single equation `sum residual_i^2=0` is equivalent over the positive integers. The resulting polynomial has exact degree **2,304,000** and leading homogeneous part **2 W^2304000**. No top-degree cancellation is possible, and the explicit leader identifies its coefficient as two.

A literal naive folding grammar charges 234 subtractions, 234 squares and 233 additions: **701 extra operations = 234 M + 467 A**, with no additional supplied witnesses. The initializer-only folded count is therefore:

- 1,153,426 M + 1,153,662 A
- **2,307,088 operations**, 396 new positive witnesses, one equation

This is an initializer-only result. The equation still depends on the inherited W,Wp,Q/head/memory ports and is meaningful as exact initialization under their parent geometry contract. It is not a final universal single-polynomial degree or operation bound. Adding the literal coefficient prefix, if desired, is separate from this free-fixed-numeral folding count.

## 7. Independent validation

The present directory contains:

- `audit_composition.py`: validates exact final inline JSON; independently checks every full composed opcode/reference, equality endpoint, count, witness namespace and source hash; confirms no output aliases survive as free ports; proves the one shared G chain's exponent
- `audit_composition_residuals.py`: 144 independent signed finite-field comparisons of every one of the 234 composed residuals, against a direct pair-JSON evaluator and independently written closed wrapper formulas, over three primes and two small row-period overrides
- `audit_degree.py`: full-node degree-upper certificate plus exact-source lower-bound witnesses for the two maximum-degree residuals
- Corresponding JSON receipts, logs and frozen reviewed sources

The source generators were inspected before interpretation. Full topology checks use constant space in the number of gates; degree propagation uses about 9.3 MB. Residual tests reduce every value modulo a fixed prime and use fewer than 2,400 gates per test. No test expands Pell witnesses or giant coefficients. The finite checks establish source correspondence and supplement, rather than replace, the all-integer mathematical proofs.
