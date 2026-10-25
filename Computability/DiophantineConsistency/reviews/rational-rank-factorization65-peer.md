# Independent peer review: rational rank factorization65

**Result: pass within the stated rational-leaf circuit metric.** The new
65-gate evaluator computes exactly the complete parent integer polynomial,
pointwise, for the same fifteen inputs and the same fixed coefficient tuple.
It does not establish a 65-gate evaluator with only integer constant leaves.
Its exact degree remains 157. No blocking mathematical or implementation
issue was found in this scoped review.

The reviewer independently read every line of
`research/rational-rank-factorization65/{README.md,audit.py,polynomial.json,AUDIT.json,source/parent66.json}`.
The reviewer did not author or modify those files. The review includes manual
algebra and graph inspection, followed by both read-only audit commands after
inspecting the entire auditor. This reviewer previously authored the separate
complemented47 finite controller verifier, not this rational65 proposal.

## Exact identity and whole-graph inheritance

Write `qm=beta*J`, `q=qm+1`, `G=qm*(q-F)+alpha`,
`U=MF/beta`, and `W=(MC-MF)/beta`. The name W avoids the already-used
auxiliary-norm abbreviation V. For every fixed nonzero beta,

```text
qm*((q+1)*(G+U)+W)
 = qm*(q+1)*G + (qm/beta)*((q+1)*MF+MC-MF)
 = (q²-1)*G + J*(q*MF+MC).
```

Both equalities hold identically in the Laurent coefficient ring with beta
inverted. The final expression is in the ordinary integer polynomial ring in
all fifteen witnesses and the four original integer coefficient ports. No
division by a witness, positivity assumption, intended-root restriction,
congruence, or cancellation of a potentially zero witness is used.

I checked all rows of both literal DAGs. The removed six-gate rank tail is
replaced by exactly the five stated gates. The retained prefix, the entire
suffix, both occurrences using R, all six factors and the final subtraction
of Delta are unchanged. In particular q2 remains live because q3 still uses
it. The auditor's explicit prefix/suffix equality checks correctly express
this substitution cut. Equality of the complete rank therefore composes to
equality of the whole output polynomial, and to the same zero set on every
integer assignment. The positive-domain equivalence follows immediately.

## Operation metric and integer output

The old six-gate tail uses three multiplications, two additions and one
subtraction. The new five-gate tail uses two multiplications and three
additions. The full independently inspected ledgers are:

| Circuit | Multiplications | Additions | Subtractions | Total |
| --- | ---: | ---: | ---: | ---: |
| Integer-leaf parent | 38 | 15 | 13 | 66 |
| Rational-leaf evaluator | 37 | 16 | 12 | 65 |

Every declared leaf and operation is reachable from the final output. U and
W are fixed rationals compiled from the same coherent four-port tuple. Their
construction is free only under the explicitly stated circuit convention.
The integers MC and MF have not become additional witness variables. The
output remains the original integer polynomial even though intermediate
registers may be rational.

The displayed integer-leaf alternative
`J*((q+1)*(beta*G+MF)+(MC-MF))` costs six gates after G and hence only ties
66. The narrow register-rescaling obstruction is also valid under its stated
restrictions: fixed witness leaves force the q, qm and G scales to one, so
the same one-gate sum `G+U` forces U's scale to one. The parent's
`1<MF/beta<2` excludes an integer U. This is not a lower bound for arbitrary
integer circuits, and the proposal does not claim one.

## Independent degree derivation

Let `q0=beta*J`, `k0=eta+zeta`, `E0=w*s*q0^4`, and
`c0=k0*s*q0^3`. Witness degree is one; coefficient-port degree is zero.
Then the leading forms satisfy

```text
ell0 = k0*w*s²*q0^7,
S0   = i*k0²*w²*s^4*q0^14,
V0   = f²*k0*s*q0³*T.
```

The potentially misleading main-norm cancellation can be seen without the
auditor. If `Z=X+gamma*H`, then

```text
N1=(a*c+Z)²-(a²+H)*c² = 2*a*c*Z + Z² - H*c².
```

The degree-22 terms cancel identically. The unique surviving highest-degree
contribution is `2*E0*c0*(4*gamma*E0)`, of degree18. Thus the complete factor
degrees are `22,18,62,7,2,46`, and multiplying their leaders gives

```text
-8*q0^91*h*gamma*i^4*k0^13*w^13*s^26*T²*f^4
  *(w*(q0-F-alpha)-z*q0).
```

Its 56 terms agree with the auditor. The coefficient of
`J^92*h*gamma*i^4*eta^13*w^13*s^26*T²*f^4*z` is `8*beta^92`, nonzero for
every nonzero beta. The final subtraction of Delta, of degree12, cannot
cancel degree157. This proves the exact degree after specialization, without
assuming the syntactic degree bound is attained.

The auditor's sparse Laurent addition/multiplication and leading-form
propagation implement these arguments correctly. When full cancellation of
a gate's provisional leader occurs, it evaluates that gate exactly to recover
the actual leader. The sole reported such cancellation is N1, whose full
323-term expansion drops from apparent degree22 to degree18.

## Executable verification and source bindings

Both commands completed successfully with identical reported results:

```sh
python3 Computability/DiophantineConsistency/research/rational-rank-factorization65/audit.py --check
python3 -O Computability/DiophantineConsistency/research/rational-rank-factorization65/audit.py --check
```

Each reported 65 operations, rational leaves, exact degree157, the same integer
polynomial, and four rejected negative controls. The auditor uses explicit
exception checks, so `-O` does not remove its gates. It imports only the
standard library; JSON and compressed coefficient files are read as data.
The `--check` path writes neither circuit nor receipt.

The frozen parent matches the preserved radix55 candidate byte-for-byte. All
four complete compressed and raw coefficient hashes match the same original
binding, with 242484 total raw bytes. This authenticates the old tuple, rather
than certifying a new tuple or changing MF's once-shifted source convention.
The exact generated packet and evidence match the saved JSON bytes.

Reviewed file SHA-256 values, relative to
`research/rational-rank-factorization65/`:

| File | SHA-256 |
| --- | --- |
| README.md | `75b858aaeb302dac8e7b9100ba1506195aa8bc6c0d6366df06ffefc592fa5fa3` |
| audit.py | `aae7db319e20367041f2faea19ded4d500c4b18a6ad34d3c07fcfba62acb522e` |
| polynomial.json | `b7a89884c0330d23b5995dd293c77b0cc24fcaaf9cea85053a207daf1aafff67` |
| AUDIT.json | `5fe10e8d4aad62afab5e5a7919fd4377197e5dea6d3a3bff604c5d91e1a5cf46` |
| source/parent66.json | `058c48168f242f3b9aae8fd86cbe6d2b0f6fb1f336ae8082567a5edb24528066` |

## Complemented47 specialization and limits

**Yes: the identity, 65-operation rational-leaf ledger and exact degree157
specialize unchanged to the coherent complemented47 tuple.** For that tuple,
set `U47=MF_source47/beta47` and
`W47=(MC47-MF_source47)/beta47`; `beta47>0` suffices for the algebra and the
nonvanishing degree witness. The resulting evaluator is pointwise equal to
the **complemented47 parent P66 polynomial using those exact same ports**.

This does not identify the radix47 polynomial with the radix55 polynomial:
changing the tuple changes the parent polynomial. The saved rational65
packet and audit bind radix55; a separately published47 packet must bind47
coherently. Its Con(ZFC) semantics would transfer from its own established47
parent by the identity, with exactly the parent's calibration and proof
scope. The rank identity supplies no missing native/Pell/refutation theorem.

This review establishes local algebra, graph inheritance, the claimed
rational-leaf operation count, exact degree, deterministic audit behavior
and existing55 tuple byte authentication. It is not a new formal-kernel or
internal-ZFC proof, a global-minimality result, a byte-size reduction, a new
integer-leaf record, or authorization to promote either equation page.
