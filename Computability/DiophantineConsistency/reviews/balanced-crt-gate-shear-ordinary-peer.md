# Independent ordinary review: balanced CRT gate shear

Verdict: **PASS** for the exact ordinary proposal and its stated finite coefficient claims. No author-packet correction is required. This approval supplies neither a generated polynomial nor an execution release, transformed whole height/support measurement, new numerical endpoint, or calibration acceptance.

The reviewed packet is `research/balanced-crt-gate-shear`, MANIFEST SHA-256 `a016d1e1f8fe2b33437a3502a9371257b82aef1ec4d4cc17367f509a93ae62a2` (509 bytes). Its exact two payloads total 26510 bytes:

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| README.md | 11765 | `84ecbcb44499a4965bb36bcc7a2e37014c9808f2c087f4fd2f37f106f61170f4` |
| SOURCE_PINS.json | 14745 | `0aae4e089aa9174f6bd258f56f511f6079a86f6f03b9a4f14a72e1d53e54b28c` |

Report history: the original peer MD (`548949dbe003ac6dae9b8beef5ac4d4f752fd4d5e7f5445473aab4fc9ecdbcdc`), companion JSON (`a6c387f8c060bac31db2f61316c5b00e89722ea0968337271bd50fc68f8336cf`), and ROOT's review-prose finding are preserved in commit `8f654b5ba7`. This authorized report-only repair corrects the row 15 linear-term trace below. I freshly reread the complete unchanged source note, all thirteen full literal rows in both profiles, both finite coefficient tables and the other explanatory traces, and reauthenticated the complete declared closure. No other explanatory trace mismatch was found; the source seal and ordinary PASS are unchanged.

## Review scope and authentication

I read the entire final README, SOURCE_PINS, and MANIFEST, not merely a change or the earlier informal shear calculation. I also read the complete accepted translation-height note, its pins and manifest, the outside observed-source JSON, and the complete current centering PROOF. The exact old centering proof and source interfaces had previously been fully reviewed; their authenticated identities agree with those earlier reads. This review does not adopt another reviewer's report as mathematical evidence.

Fresh inert byte/hash authentication checked every one of the 38 external pins and the own-core README. The proposal folder contains exactly README, SOURCE_PINS, and MANIFEST. The whole accepted translation proof contains exactly its two payloads (7331 bytes) and 465-byte MANIFEST `52bb637272f30005f9658e0afb76a1b1f2e388c621daaa1820f472bd69de9545`; its five external pins and own-core pin also match the present packet's closure. The complete observed centering folder contains exactly the 34 pinned files, totaling 611657 bytes. Every file matches both this packet's direct pins and its whole-input inventory. The outside inventory is the exact 5914-byte record with SHA-256 `af2b80aecbdf8bf701700df3b1e1184e09259c5fdcaec04f1a0c45379b944959`, and explicitly has `final_acceptance_or_manifest_sealing=false`. No mismatch, omitted file, or extra file was found.

Inert JSON inspection independently located every row containing coordinate 21 in each actual equation, displayed each such row in full, and located every row containing coordinates 22 and 37. It also displayed unchanged row 9, the actual coordinate names, and all seven existing quartic coefficients used below. The existing polynomials have 316/315 coordinates, 5737/5743 literal nonzero terms, and no missing coordinate in their actual monomial supports. No new polynomial was generated or expanded during these inspections.

## Whole substitution, inverse, and liveness

The map fixes all coordinates except `x21=u-2a-2b`, with `a=z10`, `b=z11`, and `u=z21`. Elementary row addition proves determinant one. The displayed inverse, `z21=x21+2x10+2x11` with every other coordinate fixed, is valid over the whole integer space. Consequently substituting into every original residual gives the literal universal identity `P'(z)=P(Sz)` for the entire SOS, and a bijection of the entire integer zero sets. It does not merely recover a subset of witnesses.

Every original row is retained. Linear substitution preserves the degree-two row bound; the invertible linear map is injective on the degree-four homogeneous component, preserving exact quartic degree. For coordinates outside `{10,11,21}`, the chain-rule argument in the note is correct: the only changed coordinate image does not involve such a coordinate, so the old nonzero partial derivative remains nonzero after substitution. The current canonical polynomial supports independently confirm the premise that every old coordinate is live.

For the three exceptional coordinates, literal row 7 has quadratic part `-(a+2z22)^2`, row 9 has quadratic part `-(b+c)^2`, and the substituted row 25 has quadratic part `-16u^2`. Thus their contributions to the pure fourth powers of `a,b,u` are respectively at least 1, 1, and 256. Other squared quadratic rows cannot cancel a pure fourth-power coefficient, since each such coefficient is a square. The note's liveness conclusion is therefore justified; invertibility alone would not have justified it.

The forward witness composition first uses the existing complete source/centering construction and then `S^-1`. The reverse composition first applies `S`, then the fixed 58 shifts, and then the complete original raw monic/Horn/source maps with their existing private-coordinate boundary. This is the order in the authenticated centering proof. Applying sign arguments only to the recovered old tuple avoids imposing an unsupported sign restriction on the new coordinates.

## All thirteen complete residuals

The complete actual occurrence lists are:

| Profile | Rows containing coordinate 21 |
| --- | --- |
| Plain | 5, 6, 12, 15, 19, 21, 25, 50, 51, 52, 71, 73, 90 |
| Weighted | 5, 6, 12, 15, 19, 21, 25, 50, 51, 52, 71, 74, 91 |

The ten common rows agree term for term between profiles. The remaining outputs are exactly plain `(86,89,105)` and weighted `(87,90,106)` in the note's order. I checked the entire literal rows, including constants and linear terms, against all thirteen displayed factorizations, rather than checking their leading parts alone.

Useful checks on the lower terms include the following. Row 5 changes from `x21-(a+b-1)^2` to `u-(a+b)^2-1`. Row 15's old linear part `6a+8b+8c+2x21+8z27+4z30` becomes `2a+4b+8c+2u+8z27+4z30`, which equals `2L15-M`, with its constant `+1` retained. Row 25 becomes `z41-16u^2-14u-2a-4b-6`. Row 50's remaining linear part becomes `4a+8b-c-4u`, exactly `-2L50+c`. Row 52's remaining linear part becomes `4a+8b-4u-2z67`, exactly `-L52+2z65`. The complete bilinear and addition rows give precisely the note's three final formulas; the addition row retains every term in the full displayed `D`.

All other rows are unchanged because the exhaustive literal occurrence lists contain no further use of coordinate 21. No hidden gate definition or presumed equality of coordinates is used in these substitutions.

## Entire leading-form identity and selected coefficients

For general integer `(m,n)`, substituting `x21=u-ma-nb` in the literal quadratic parts gives all eight displayed linear forms, with `M` counted twice. These represent all nine affected square-type quadratic parts. Their fourth powers account for the whole square-type degree-four change. The two actual bilinear quadratic parts are `-2g(a+x21)` and `-g(6a+8b+2x21)`, giving exactly the two additional differences with factors `4g^2` and `g^2`. Row 5's quadratic part is unchanged, and the addition row is only linear. This exhausts every changed row and proves the displayed difference of the complete degree-four components over all coordinates and both profiles. The unaltered gate coordinates inside the linear forms have not been dropped.

I independently evaluated the five elementary multinomial coefficient formulas over all eight forms, with `M` counted twice. The following ordered component lists use `(2M^4,L12^4,L15^4,L19^4,L25^4,L50^4,L51^4,L52^4)`:

| Monomial | Old component contributions | Balanced component contributions |
| --- | --- | --- |
| a²bc | 0, 110592, 13824, 0, 0, 0, 0, 0 | 0, 24576, 768, -384, 0, -192, 0, 0 |
| a²c² | 0, 55296, 3456, 96, 0, 24, 0, 0 | 0, 24576, 384, 96, 0, 24, 0, 0 |
| a²b² | 27648, 55296, 13824, 0, 24576, 0, 0, 0 | 768, 6144, 384, 384, 0, 384, 384, 6144 |
| ab³ | 24576, 24576, 12288, 0, 16384, 0, 0, 0 | 1024, 2048, 512, 512, 0, 512, 512, 8192 |
| a²bu | 13824, 27648, 6912, 0, 24576, 0, 0, 0 | 768, 6144, 384, -384, 0, -384, -384, -6144 |

Their sums are exactly the note's two contribution columns. The bilinear differences contain `g` and contribute to none of these five monomials. The actual existing literal coefficients and the resulting full selected coefficients are therefore:

| Monomial | Current plain/weighted | Balanced plain/weighted |
| --- | --- | --- |
| a²bc | 128446 / 128446 | 28798 / 28798 |
| a²c² | 126901 / 126901 | 93109 / 93109 |
| a²b² | 121910 / 121909 | 15158 / 15157 |
| ab³ | 78812 / 78812 | 14300 / 14300 |
| a²bu | 72960 / 72960 | 0 / 0 |

Thus the specific `a²bu` coefficient vanishes, and the other four specified positive coefficients decrease. Neither the arithmetic nor the proof implies that every coefficient decreases or that total support shrinks. The note states those limits explicitly.

## The family obstruction and the aggressive member

Coordinate 22 occurs only in rows 6, 7, 8. Row 6 contains it only linearly, even after any member of the shear family, so its square cannot yield `a*z22^3`. The quadratic parts of rows 7 and 8 are `-(a+2z22)^2` and `-(6a+16z22+2z23)^2`. Their contributions are `4*1*2^3=32` and `4*6*16^3=98304`, totaling 98336. Neither row contains coordinate 21. The same argument applies to coordinate 37, which occurs only in rows 21, 22, 23, with the analogous two quadratic parts. Both current literal quartic coefficients are independently 98336 in both profiles. Thus every member of this entire two-parameter gate-shear family has height at least 98336. This is a lower bound, not an asserted attained minimum.

For `(m,n)=(3,4)`, the repeated `M` becomes `2u`. The `ab^3` contributions inside `A` are zero except the four values 8192 from rows 19, 25, 50, 51 and 131072 from row 52. Their sum is 163840. The unchanged portion outside `A_(0,0)` contributes `78812-77824=988`, hence the full transformed coefficient is exactly 164828. The accounting correctly excludes row 5 from `A`: row 5 contributes 4 to `ab^3` but its quadratic part is unchanged. Including it in the thirteen-row contribution accounting instead would give old 77828/new 163844 and an outside part 984, with the same final answer. There is no discrepancy between these conventions.

The current input height is 128446 by the authenticated accepted translation proof. Since 164828 exceeds it, the aggressive member cannot improve height. This obstruction concerns that member only and does not establish an optimal balanced shear or a minimum under arbitrary unimodular transformations.

## Boundaries and result

The note's proposed balanced substitution is a complete ordinary mathematical recipe. Its finite claims, integer inverse, full row formulas, whole leading-form identity, degree, liveness, map order, and source provenance all pass. The packet carefully leaves the balanced chart's whole height/support and complete coefficient equality after materialization to a future separately reviewed implementation. It does not alter the accepted translation-only minimum theorem: this shear changes the degree-four component and belongs to a different class of transformations.

The observed source remains explicitly an observed immutable checkpoint, not a final accepted endpoint. The original fresh optimized exit 143 is retained as unresolved, without a successful-result label, inferred cause, or retry. The packet does not claim a new native tuple, calibration, or complete endpoint. The maintained page and all held/frozen author packages were untouched.

Review methods were inert source/JSON reads, byte/hash/inventory checks, and ordinary symbolic/multinomial arithmetic. I did not import, compile, run, or generate any application, application helper, optimizer, AST, substituted equation, expanded polynomial, numerical tuple, TeX/PDF, or Lean artifact. Only these outside review records were written. The companion JSON records the full fresh authentication and the finite ordinary calculations. PASS applies to the exact manifest above and supplies no execution authorization.
