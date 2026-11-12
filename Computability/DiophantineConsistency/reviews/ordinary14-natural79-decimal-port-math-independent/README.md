# Independent check of natural-79 decimal port mathematics

The four fixed integers in the pinned [decimal candidate TeX](../../research/ordinary14-natural79-decimal-render-candidate/equation.tex) agree, by exact external integer computation, with the corresponding retained P72 coefficient bytes and the pinned compact symbolic source definitions. No arithmetic or transcription discrepancy was found in this bounded comparison. The check reads the candidate and source files without running the generator, Lean, or a PDF renderer.

The checker concatenates the actual displayed decimal lines and matches them to the 15,086-digit seed file. It extracts 943 right-to-left blocks of 16 digits, padding the two leading zero positions, and independently computes each selector from the ordered `Compact943Data` row and `CompactCoefficientMass` formula. All blocks match in order and lie strictly between zero and `10^16`. It parses the displayed 41 kernel positions and compares their order with `CompactSymbolicKernel.slots`; it then evaluates the displayed `K` sum, including `rho^8849 = rho^8807 * rho^42`, and compares the result with the retained `K0` bytes.

For the low port, it parses the displayed intervals and exceptional positions, constructs every little-endian radix digit directly from `CompactListMask.digit`, and confirms that this integer equals the displayed subtraction formula for `mu`. The special position 1063 is in the support and has digit `rho-4`, so it needs the two additional `rho^1063` subtractions. For the high contribution, it parses the complete `CompactHighPopulation.highDigits` run list and verifies the displayed finite sum against all 8,807 digits. It then checks `omega = beta + H`, with beta added exactly once, and the source tuple `![beta,K,low,beta+high]`. The candidate's conditional Lean bridge takes the already shifted fourth value; the four necessary source port equalities remain hypotheses there.

All four computed integers agree exactly with the decompressed little-endian P72 bytes, whose gzip and raw hashes are pinned. This external equality is not a Lean theorem that the physical files, decimal TeX, or PDF denote those source expressions. The candidate remains a separate source-mapping draft: the 79 endpoint, the four port equalities, TeX/PDF interpretation and compatible provider/axiom closure remain open. This review does not independently check the 79 graph rows or PDF extraction; see the separate decimal-render review for those bounded observations.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-decimal-port-math-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-decimal-port-math-independent/result.json
```
