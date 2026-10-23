# Wave-eight review and target change

Reviewed 23 October 2026, following the owner's pointer to placement commit
`beb0192cb8dc36f78c369c080f2adfbc1887a486`. The six original archives arrived
at `7331974b69`; their placed packages are 54–59. This review supersedes the
wave-seven target selection while preserving its checked milestones.

## Decision

**Adopt package 59's free-coordinate, degree-separated adjunct as the primary
nine-variable target:** nine strictly positive integers, **473 live binary
operations**, exact reported degree **1,910,404**. Its separate natural-domain
version costs **480 operations** at the same degree. The actual recommended
file is
[`nine_free_adjunct/generated/split_116_positive.json`](con-zfc-diophantine-forms/59-degree-separated/nine_free_adjunct/generated/split_116_positive.json).
The older `nine/` family in the same package is a comparison construction.

Relative to the previous package-52 target, this saves 75 operations
(13.69%) and reduces degree by 87.68%. It dominates every reviewed
nine-positive point from waves seven and eight on those two measures.
The number of unknowns is unchanged. This is a finite-catalogue comparison,
not an optimality theorem.

Retain **package 54 as the smaller-coefficient option**. It binds a complete
`2^429959` native tuple to actual equations, improving the former compact
`2^590069` binding. Its 490-operation, degree-9,461,300 nine-positive form
also improves the former package-52 target. Package 59 instead retains the
larger original31 tuple, with radix `2^1064921`; its better degree and
circuit size do not establish a coefficient-size improvement. The bindings
must remain whole and separate.

**Subsequent concrete improvement:** the same split/free-coordinate
architecture has now been regenerated with each entire compact tuple,
including all fixed leaves and its recalibrated threshold. Both instances
retain 473 operations and degree 1,910,404. The preferred current
instantiation is [compact54-sharp](candidates/split116-compact/compact54-sharp/README.md):
215,492 native raw bytes, compared with the delivered 59's 533,099.
The twelve live derived fixed leaves total 1,672,725 raw bytes. A factored
coefficient bound improves the first compact54 binding by one raw byte;
its radix floor is halved and threshold scale divided by 256. These byte
counts describe stored constants, not an expanded polynomial. The delivered
59 files remain the reference release; the new instances are separately
sealed artifacts with ordinary source-interface compatibility and finite
replays, not new Lean consistency endpoints.

Package 57 is also a useful compact-tuple alternative: its 499-operation,
degree-2,628,944 point uses 295,388 native payload bytes, compared with
59's 533,099 and 54's 215,492. These counts measure the four native ports,
not every derived fixed leaf or expanded polynomial coefficient. The
working priority remains nine natural/positive variables, then arithmetic
operations, retaining coefficient and degree alternatives explicitly.

Finish and preserve the package-52 proof checkpoint. Its literal
multivariate polynomial now has a checked nine-natural-zero equivalence
with its actual 31-input source, under the four published port-size bounds.
This is useful reusable work, even though the numerical target has changed.
It has not discharged authentic native calibration or the internal ZFC
equivalence, and the direct finite-sum evaluator has not been assigned the
shared circuit's 548-operation count by a Lean theorem.

## Comparison

Degrees below are the delivered exact-degree claims, supported by replayed
finite certificates. The independent DAG audit recomputes operations and
liveness; it does not infer exact degree from naive gate propagation.

| Package / nine-positive variant | Operations | Degree | Disposition |
|---|---:|---:|---|
| 52 interior regular | 548 | 15,502,748 | Previous target; formal checkpoint retained |
| 53 calibrated | 738 | 7,344,328 | Superseded numerical target |
| 54 regular, simple majorant | 490 | 9,461,300 | Smaller-coefficient option |
| 54 shifted packed, quotient majorant | 564 | 4,400,764 | Smaller-coefficient degree/cost alternative |
| 54 packed, quotient majorant | 598 | 4,399,820 | Smaller-coefficient lower-degree alternative |
| 55 fast / majorant | 604 / 630 | 6,692,108 / 5,671,669 | Dominated on degree and operations |
| 56 free coordinate | 560 | 4,686,812 | Important new reusable arithmetic adapter |
| 57 separated degrees | 499 | 2,628,944 | Strong intermediate; dominated by 59 adjunct |
| **59 free-coordinate adjunct** | **473** | **1,910,404** | **Primary target** |

Other domains retain distinct tradeoffs:

* Ten unrestricted integers: 54's **513 / 25,838,224**, 59's
  **533 / 8,469,528**, and 57's **544 / 8,317,400** are nondominated on
  operations/degree. These use the additional Sun bridge, which is not
  formalized here. They are not nine-integer results.
* Twelve positive integers: 57's **89 / 258** and **94 / 242** improve the
  incoming 108 / 897 point. They also dominate 59's 102 / 316 and
  58's 114 / 629 single equations. Multiple-equation systems have their
  own counts and are not substituted into this comparison.
* Thirteen positive integers: 57's **83 / 132** and 59's adjunct
  **91 / 126** are separate tradeoffs. The thirteen-unrestricted-integer
  59 construction is another domain: **518 / 11,543,632**.
* Fifteen positive integers: the 51 **66 / 157** point survives. The
  selected short frontier also includes **67 / 125**, **68 / 101**,
  **69 / 91**, **70 / 80**, **71 / 78**, **72 / 64**, **73 / 54**,
  **74 / 46**, **75 / 44**, **79 / 30**, **88 / 26**, and **90 / 24**.
  The last three are package 58's integral-root carriers. In particular,
  58 reduces the reviewed fifteen-positive degree minimum from 44 to 24
  at a higher operation count. These are existence reductions with
  different quotient coordinates, not automatically identities of the
  checked normalized P76 polynomial.

## Why the new primary equation is smaller

Package 59 separates constant, linear and quadratic source degrees:

```
Gs = D2(B)*(ell+g)^2 + D1(B)*(ell+g) + D0(B).
```

Two invertible row operations leave 89 weighted records and permit
same-degree extraction at 22 targets with maximum input weight 116.
Cross-degree labels may coincide because the three degree channels are
evaluated separately. This replaces the fully padded quadratic product in
package 52. The source certificate covers 22,544 same-degree interactions.

The adjunct then incorporates package 56's free positive carrier `C` and
shorter outer carry rank. The rank is

```
L = b*B^2279,
R = L*(Scode+Tcode+1)-Scode-1,
N = 2^17079501*b*B^1201.
```

The population threshold is recalibrated exactly; deleting the leading
block alone would not preserve the test. The proof first establishes
positive source words for all outer assignments, then obtains the actual
weak cap `g<4*b*B^116` from ratio soundness. It proves
`Scode+Tcode<L` on that branch before decomposing the binary blocks.
The zero-carry threshold includes the boundary `b=1`; the low mask then
rules out a final zero rather than imposing an unsupported restriction.

The free-carrier finalizer uses
`E0=J*(n+(b*w)^2)+Q>0` before recovering positive margin. Strict majorants
recover that margin before integer-root extraction; it then restores the
old carrier range. Completeness proves the newly chosen final witness is
strictly positive using `(b*w)^2+Q/J<2*D<V1`. These ordering details are
essential to reuse the numerical Jones theorem without extra assumptions.

## Source and formalization boundaries

The authoritative package-59 source is the expanded `parent_source.json`
used by its channel certificates. Its inherited `source_system60.json`
copy is identical to our package-52 copy, but that does **not** identify
the two authoritative positive source predicates. Exact expansion finds
21 matching rows and a transport difference of `beta*J` in row 15.
Writing the old quotient as `z_old`, the package-52 quotient is
`z=z_old-1`. The substitution preserves the residuals algebraically;
the positive domains require the inherited canonical-witness bound
`w>q>F`, which forces `z_old>=2`. An arbitrary-port positive bijection
does not follow merely from the copied source file. The old31 coefficient
binding and its ordinary source proof are coherent with this convention.

Reusable checked components include the actual Jones numerical ratio
theorem, arbitrary-position low-mask decoding, exact CRT
reparameterization, strict Pell majorants, margin-first root extraction,
generic coefficient/convolution bounds and the native arithmetic
elimination. New Lean obligations are:

1. Bind the authoritative source and its row operations, preserving the
   transport quotient's actual domain.
2. Check the three literal kernel tables and same-degree extraction.
3. Formalize the sparse `+1` signed-borrow decoder and its uniform range
   bounds, rather than substituting the old dense half-base test.
4. Prove the shorter-rank population identity and its exact threshold.
5. Generalize the ratio/finalizer adapter to free `C`, the normalized
   margin and the quotient shift, then bind the literal counted circuit.
6. Close the authentic whole-tuple native compiler/K215 calibration and
   the separate internal ZFC derivation.

The separate [compact candidate family](candidates/split116-compact/README.md)
now supplies those complete bindings, materialized signed fixed leaves,
recalibrated thresholds and byte-identical rebuilds under two Python
versions. The sharp package-54 tuple uses height `2^864014`, radix floor
`2^864026` and threshold scale `2^6912197`; package 57 uses `2^1182955`,
`2^1182967` and `2^9463725`. All 89 actual weighted coefficients were
checked for each tuple, along with the four adapted replay programs.
Lean now checks the generic split extraction, sparse borrow decoder,
population calibration, quarter-base bounds and free-carrier ratio
adapter. The generic binomial-to-source-coefficients contract now derives
all degree, population, quarter-base and word-range obligations internally.
See [SPLIT116_FORMALIZATION.md](SPLIT116_FORMALIZATION.md) for
the exact completed contracts and remaining assembly obligations.

No newly delivered package supplies an end-to-end Lean certificate or
object-language ZFC derivation. Finite replay does not supply these missing
unbounded theorems. The current closed `ExplicitZFC` and `NativeZFC`
equations remain the externally certified consistency endpoints.

## Validation

The review extracts the original ZIPs from arrival commit `7331974b69`
into scratch directories, retaining their release manifests and omitted
identical members. The canonical placement deliberately deduplicates such
members; missing placed copies must not be mistaken for absent source
material or repaired inside the delivered tree.

Full normal release replays passed for **54, 55, 56, 57, 58 and 59** under
Python 3.12.13. The declared NumPy/SymPy dependencies were available for
59. Package 59 passed all 25 stages and 74 byte-identical rebuilds;
55 passed 13 stages and 18 rebuilds; 57 passed all 13 reproduction steps;
58 passed all seven checks and 11 byte-identical circuit rebuilds, also
under optimized Python. Package 56's driver exercises its arithmetic
components normally and under optimization. Intentional optimization
rejections are policy checks, not successful optimized mathematical
replays.

[`review_wave8_frontier.py`](tools/review_wave8_frontier.py) independently
audits 80 selected wave-seven/eight literal circuits, including every
primary candidate above. It checks topology, complete gate/input liveness,
operation counts, reported-degree transcription and SHA-256. Its normal
and optimized runs agree; the result is
[`wave8-circuits.json`](reviews/wave8-circuits.json). This scope excludes
degree proof, native coefficient semantics and global minimality.

The coefficient/source and arithmetic reviews are recorded separately in
[PROPOSAL_REVIEW_WAVE8_ARITHMETIC.md](PROPOSAL_REVIEW_WAVE8_ARITHMETIC.md),
and replay/source-packing details in
[PROPOSAL_REVIEW_WAVE8_QUADRATIC.md](PROPOSAL_REVIEW_WAVE8_QUADRATIC.md).
The free-carrier, reduced-rank and source-domain review is
[PROPOSAL_REVIEW_FREE_SPLIT.md](PROPOSAL_REVIEW_FREE_SPLIT.md).
Compact replay receipts are retained for
[54/57/59](data/wave8-review-54-57-59.json) and
[55/56/58](data/wave8-review-55-56-58.json).
