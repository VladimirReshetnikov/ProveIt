# Verification report

## Four separate levels of assurance

### 1. Mathematical proofs in the article

The universally quantified claims depend on the human-readable proofs: separated Hamming-ball profiles; coherent label existence; classification and packing of target/gate candidate lists; the four threshold-resolved recurrences; interval containment; minimum accepting weight; exact zero-input block sensitivity; composition; and the query lower bound.

These arguments have not been checked by Lean, Isabelle, Coq, or another proof assistant. Executing recurrence code does not prove that it bounds the actual sensitivity of all constructed Boolean functions. That logical link is Theorem 5.2 and the certificate-engine soundness proof.

### 2. Exact integer arithmetic

Run `python3 code/verify_certificate.py` from the project root. It:

1. Recomputes every meaningful profile entry using the array implementation.
2. Recomputes the same entries using separately organized memoized single/pair requests, without calling the array transfer routine.
3. Checks exact equality of all 1,938 meaningful entries.
4. Compares the recomputed constants and arrays against the packaged JSON files.
5. Checks the label-existence inequality with arbitrary-size integers.
6. Checks the two binary-power inequalities and a direct rational-power comparison.
7. Checks `n = beta*W`.

The exact binary-power certificate is:

```text
bit_length(A^50) = 14,472, so A^50 < 2^14,472.
bit_length(beta^50) = 29,337, and beta^50 > 2^29,336 is checked directly.
29336/14472 = 3667/1809.
1000*29336 - 2027*14472 = 1256 > 0.
```

The strictness of the lower binary bound is explicitly compared; its bit length alone would only give a non-strict inequality. Decimal logarithms do not certify any theorem.

The compact script duplicates the article's Appendix A recurrence in a short independently executable file. It uses the same mathematics, so this is not a logically independent proof. It makes auditing the arithmetic implementation easier.

### 3. Exhaustive small cases

Run `python3 code/test_local_geometry.py`. The included execution report records:

| Check | Coverage |
|---|---:|
| Local threshold configurations | 71,368 |
| Rejecting local configurations | 66,112 |
| One-gate configurations | 7,440 |
| Two-gate configurations | 552 |
| Three-gate configurations | 24 |
| Successful single-child repairs checked | 3,744 |
| Actual Boolean functions | 8 |
| Inputs per function | 262,144 |
| Total input assignments | 2,097,152 |
| Single-bit difference comparisons | 37,748,736 |

The eight functions use the three-row cyclic tournament, all eight binary edge-label assignments, depth one, and 18 raw bits. Each has exact sensitivity sides `(s0,s1) = (3,8)` against certified upper bounds `(5,8)`, minimum accepting weight six, and zero-input block sensitivity three. The block value is certified by exhibited disjoint witnesses and the minimum-weight upper bound, rather than an exhaustive optimization over all block families.

The conditional-expectation labelling example uses seven rows, two labels, and forbidden set size five. Its maximum coherent subset size is four; its final bad-set count is zero. The full labelling is included in `certificates/small_label_witness.json`.

### 4. Typesetting and package checks

The article was compiled with pdfLaTeX, all 19 pages were rendered for visual inspection, and the final compilation contained no unresolved cross-references or overfull/underfull warnings. The final package has a hash manifest. The clean-copy smoke test and environment details are recorded in `results/reproducibility.json`.

## What was not executed

The 28,800,000,001-row label table and the 188-digit-dimensional seed truth table were not generated. Label existence is established by a finite exact inequality; a deterministic finite construction is specified but is computationally astronomical at the chosen parameters. The small-label implementation deliberately rejects large row counts.

No exhaustive parameter search, global exponent optimality proof, classification of all possible threshold profiles, proof-assistant verification, or independent referee review is claimed.

## Audit order

A mathematical reader should first check the candidate-list packing lemma and the joint zero-to-one recurrence. Next check the base profiles and clipping induction, then the minimum-weight argument. Only after those logical steps should the exact integer certificate be relied upon to establish the numerical exponent.
