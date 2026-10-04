# Independent review: aggregate positive input budget

**PASS; no correction requested.** I read the entire frozen proof, helper and receipt, independently challenged the quantified argument, and wrote a separate exact source/algebra checker. The extension is sound at its declared conditional scope. It does not prove that the actual family supplies the missing carry factor or binary population threshold.

## Authenticated author packet

The reviewed files are `/tmp/complete83_aggregate_input_budget.{md,py,json}`.

| File | SHA256 |
|---|---|
| MD | `803c6d47b503d611a641b456da3887a46a300c55023dfd1e2a7120de5299903f` |
| PY | `07c7acb10810b43f7198a63b2bc465c3a59b5dfde38aa9123eb31d016999c8d7` |
| JSON | `19b5f15b30f99cd6913214eff22366d3417ab4251aa509a018f662e0a5104602` |

All eight dependency byte counts and hashes in the author receipt were independently authenticated. The source-coupled lifting theorem was separately reviewed in `review_complete83_source_coupled_input_lifting.md`; the exact quotient-carry identity and source obstruction were proved in the accepted carry-budget packet. This review checks their uses here, not every native/Pell predecessor proof anew. No author, predecessor, archived or supplied program was executed or imported.

## Mathematical review

For the progression starting at the specified x0, the domain is **nonnegative k**. Its exact positive-slack interval is `0<=k<=floor((S0−1)/ell)`, with `ceil(S0/ell)` elements. The claim does not count possible smaller positive x reached by negative k. At the stated start, the lower exponent bound remains available, and the fixed source period preserves transport throughout this interval. The new assumption S0>0 suffices for the index estimates because these are rederived from positive literal alpha, not from the older small-z bound.

The normalized source map is a residue bijection at every precision. Its difference valuation has no restriction h<=a. The polynomial root is unique and a unit, and a deficient prime therefore gives exactly one congruence class modulo `p^(3a−c_p)`. If the normalized source value is divisible by p, it cannot satisfy this root condition: the constant term is a unit. Thus no additional deficient-prime solutions are lost by imposing the unit root. At nondeficient primes there is no input restriction.

The CRT least representative k0 is consequently the smallest nonnegative member of the required class. The criterion `k0<=Kmax` is exact for that class. In contrast, `Hreq<=Npositive` is the exact guarantee that every possible least residue fits. The note correctly distinguishes these two statements and does not call the latter necessary for a particular root.

At each prime, the identity `c_p=a+tau_p+e_p` gives

`max(3a−c_p,0)=2a−min(tau_p,2a)−min(e_p,max(2a−tau_p,0))`.

The capped denominator, both gcd formulas and the integrality of C0/A follow. A cap cannot be replaced by an uncapped gain once a prime has already supplied its entire required precision. The exact aggregate modulus permits some individual deficient primes to require more than a digits of input precision.

For both shapes, `q>=A²/3` when A>=3. Under S0>q/2 and aggregate gain at least6ell, one has `ell*Hreq<=A²/6<=q/2<S0`; this implies the uniform interval guarantee. The larger-z construction makes the stated margin eventual with fixed compiler constants, since its cost is of order n*Q^(3/2), below q of order Q². This growth argument supplies slack only. It supplies neither quotient carries nor a binary population bound for the enlarged z.

The conditional completion therefore uses two distinct unresolved requirements: a fitting CRT representative (or a sufficient aggregate bound), and the input-invariant binary population threshold. The original small-z two-primary theorem is not used to assert the latter for these enlarged representatives. No automatic odd-primary success, full source zero, rejected-input zero or universal83 result follows.

## Fresh independent evidence

The new reviewer uses the emitted source only as inert data and independently expands its selected interface:

- A 23-row actual ancestor union is evaluated as exact sparse integer polynomials after substituting the full input progression and compensating slack. It proves C=z, W=0, the exact exponent increment, R independent of k with its constant z term retained, and the literal transport polynomial. The 83-row/18-witness interface is guarded. This is not a full 83-row evaluation or a renewed degree audit.
- 269,793 individual CRT residue classes are tested around exact slack endpoints. There are 3,384 tested interval/modulus pairs where a particular class fits but the uniform guarantee fails.
- 5,652 capped-exponent cases include saturated tau and extra-carry values. Separately, 1,281 new binomial records with odd r from1001 through1801 compare direct base-p addition carries with exact binomial valuations and both aggregate gcd identities; 610 have Hreq>A.
- 8,686 bounded integer checks corroborate the two shape estimates and the sufficient aggregate threshold.
- The r503 local illustration is independently reconstructed by Newton lifting followed by the actual exponential residue permutation. It gives root9 modulo49, least k0=25 and u155. A separate coefficient recurrence sums all504 terms modulo `2*42³` and obtains zero.

The last illustration remains local. Its least input increment is150, exceeding q42; it cannot satisfy the actual positive slack there. For an abstract progression with that same root class, the sharp slack threshold would be S0=151, while the all-residue guarantee would require289. These endpoint numbers clarify the distinction without constructing a source tuple.

The all-size proof was checked mathematically; these finite cases only corroborate it. No huge Pell tuple or actual compiler instance was evaluated, and no repository file was changed.

## Frozen reviewer artifacts

| File | SHA256 |
|---|---|
| `/tmp/review_complete83_aggregate_input_budget.py` | `39573671201e93ea92fa0eea6e51ced1498eb3ff6efa4efee4248c485cd19f8a` |
| `/tmp/review_complete83_aggregate_input_budget.json` | `8214c945ff014ea48d1be6c59abbab50b9be9d5b16e74a839b60c85085711b8c` |

The fresh writer, normal exact replay, and optimized-Python exact replay from `/` passed before freeze. The helper and receipt record their own execution and mathematical scope explicitly.
