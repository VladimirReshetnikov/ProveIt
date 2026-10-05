# Independent review: multiway Hadamard packing and the paid finite certificate

**PASS within the stated finite-width/finite-horizon scope; no correction requested.** I read the entire author note and its entire fresh checker as inert text, authenticated all three frozen files, and independently checked the saved twelve arithmetic arrays as polynomial data. No author or predecessor helper was executed or imported. The construction represents a finite cyclic Boolean trajectory; it supplies neither a universal equation nor a gate improvement.

## Frozen author files

| File under `/tmp` | SHA256 |
|---|---|
| hadamard_next_arithmetic.md | 7d9ae05892b9daf43a8bd2630a2853cc49cb5250c96ffa777a4ec91b5e5f69f3 |
| hadamard_next_arithmetic_checks.py | 5246d7aa225630bc272660834ac077b91629f611989d979716cf78e12d0e20fd |
| hadamard_next_arithmetic_checks.json | 9415b89a1eae04efb5869b85d6f7cef02ff2eed85e94f1d80d55fa6b076c5b5d |

The receipt's source hash equals the helper's actual byte hash. Its three inert-note pins also match the installed `review_definable_operations_de37a66d1.md`, `finite_word_hadamard_skew.md` and `native_binary_reversal_inline129.md`. That authentication is not a new full audit of those ancestors. This review independently derives the present local proof and counts and does not depend on executing an inherited construction.

## Diagonal isolation and digit soundness

The arbitrary-k injectivity proof is correct. With `K=n^(k-1)`, the combined reversed index J ranges from0 through K-1. A collision implies

```
K*(i0-i0')=(n-1)*(J-J').
```

Since `gcd(K,n-1)=1`, a nonzero first-index difference could only be `±(n-1)`. Its left-hand magnitude would be `K(n-1)`, exceeding the maximum possible right-hand magnitude `(K-1)(n-1)`. This also covers n=2. The first indices therefore agree; uniqueness of the base-n representation of J gives all the remaining indices. An equal-index tuple has exponent `L+i`, so all n central positions are occupied by exactly the n diagonal tuples and no others.

The product digit bound is global, not merely a bound on the selected band. Every exponent has at most one tuple, with coefficient at most the product of the digit bounds and strictly less than B. Consequently there is no carry from lower exponents into the band or between its digits. The floor/remainder formula is exact for all admitted digit words.

For the Boolean application, the third word's digit `1+left` really is the already supplied bit hat. At B=4 each product digit is at most2. The local rule is Boolean: if `(center,right)` is `(0,0)`, `(0,1)`, `(1,0)`, or `(1,1)`, its output is respectively0,1,1, or `1-left`. Once extraction is established, the transition comparison is a sum of radix4 terms with coefficients in `{-1,0,1}`. Successive reduction modulo4 forces each coefficient to vanish. Thus equality of the packed words enforces every local update, rather than permitting signed carry cancellation.

## Positive witnesses and the full relation

Every bit hat is constrained by `(hat-1)(hat-2)=0`; positivity gives exactly the intended bits0 or1. Both external words are separately bound by ordinary binary Horner chains. The radix4 words, three skew loaders, cyclic neighbor rotation and transition comparisons are all explicitly paid. The penultimate radix4 accumulator has the required suffix `sum_(i>=1) bit_i*4^(i-1)`, and adding `bit_0*4^(n-1)` produces the right-neighbor word. The forward/reverse digit orders of the three skew chains agree with the stated exponents.

Subtracting the extraction hats shows that the offset `PQ+P+1` is exactly right:

```
N=low+P*(middle+Q*high).
```

The positive complementary slacks enforce `0<=low<P` and `0<=middle<Q`; the shifted positive high hat gives `high>=0`. These strict remainder bounds provide Euclidean uniqueness. Conversely the true quotient and remainders give positive hats and positive slacks. In particular the all-zero input is permitted: all three extracted unshifted values can be0, their hats are1, and the complementary slacks are P and Q. Width2 also causes no issue when the left and right neighbors coincide.

Over integers the sum-of-squares finalizer vanishes exactly when every Boolean and comparison residual vanishes. Completeness loads the actual finite trajectory and its quotient/remainders; soundness recovers each guarded state and each deterministic local transition. No Pell, native AND, infinite-line boundary condition, or cellular-automaton universality theorem enters this argument. The optional positive external encoding costs the additional2A stated by the author; it is not included in the saved counts.

## Counts, degree and the direct comparator

Writing `b=n(T+1)` for the number of bit hats, the independent ledger is:

| Quantity | Multiplications | Additions/subtractions |
|---|---:|---:|
| Producers, integer numerals given | `(5n+1)T+4n-3` | `(6n+5)T+5n-3` |
| Complete SOS | `(6n+5)T+5n-1` | `(7n+13)T+6n` |

There are `b+5T` positive witnesses and `b+4T+2` equations. The b Boolean residuals are already computed. The remaining `4T+2` residual differences, all `b+4T+2` squares, and `b+4T+1` summing additions yield exactly

```
(13n+18)T+11n-1
```

complete polynomial operations. No equality comparison, boundary conversion, or remainder slack is omitted from this convention.

The constructed-numeral prefix also checks out. An exponent-e binary chain starting with2 uses `bitlength(e)+popcount(e)-2` multiplications. Applying it separately to the six displayed positive exponents supplies all six needed powers. Forming PQ and the three offset/bound constants adds1M+4A. Repeated numerals at n=2 are deliberately duplicated, but all those rows remain live; this is an exact sufficient schedule, not an optimal numeral-construction claim. The n=2,T=1 totals are65 operations with given numerals and82 with the prefix.

The exact degree is6 on every stated fixed slice. Each skew word has a nonzero linear highest part in the bit hats, including at n=2. Their product is a nonzero cubic part of an extraction residual. All other residuals have degree at most3. The degree-six sum of squares of the cubic parts cannot cancel over the reals. Constant-only construction prefixes have degree0 and leave this conclusion unchanged.

For comparison, the direct guarded schedule has producer counts `(3T+3)n-2` M and `(5T+4)n-2` A. Its `b+nT+2` equations and the same SOS convention give `(5T+4)n` M and `(8T+5)n+1` A, totalling `(13T+9)n+1`. Thus it is cheaper than even the given-numeral packed construction by `18T+2n-2>0`. The comparison makes no lower-bound or optimality claim. Paying for the packed numerals only increases that difference.

## Fresh independent checks and limits

A newly written, unsaved standard-library polynomial checker read only the frozen JSON data. It did not import, call, regenerate from, or execute the author's Python. It authenticated the author and ancestor pins, checked topology and all-row/free-port liveness, and expanded every one of the1,556 saved source rows in all twelve arrays. Independently constructed polynomial formulas for each Boolean guard, binary input/output binding, skew product, extraction bound and transition yielded exactly all186 saved comparison residuals. Their independently formed SOS matched every complete output polynomial. The exact degree was6 in all twelve cases; the independent paid-count, prefix and witness formulas also matched. Constructed-numeral arrays use only literal operands0,1,2.

A separate fresh enumeration checked15,004 exponent tuples for `2<=n<=6` and `2<=k<=5`, confirming injectivity and the exact diagonal-band criterion. This corroborates the all-k proof, rather than extrapolating it from k=3. The author's18495 positional tests,5456 complete input/output pairs and744 positive trajectory checks were read as author-reported evidence and were not replayed. This review's fresh algebra checks establish equality for all coordinate assignments on the twelve saved slices, while the prose proof establishes the general fixed-n,T theorem.

No supplied, archived, frozen or copied predecessor helper or builder ran, and no repository/Git file was modified. There is no separate frozen reviewer executable/receipt. Width and horizon still select different finite sources and different witness counts; the synchronized variable-width loaders and unbounded history interface remain unpaid and unresolved. The final polynomial-evaluator obstruction is also sound: specializing an alleged polynomial AND evaluator to y=1 would give the bounded nonconstant parity function on all nonnegative integers. This does not rule out existential Diophantine graphs or the fixed-width family proved here.
