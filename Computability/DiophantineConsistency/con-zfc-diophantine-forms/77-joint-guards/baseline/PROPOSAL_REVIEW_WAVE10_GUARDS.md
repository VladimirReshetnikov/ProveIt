# Wave ten review: guards, congruence carriers, and root transfer

The four archives below were reviewed directly from arrival commit
`9513bd88ce`. Their sealed trees were not repaired or edited. All eight
full finite replays passed: four archives, each in normal and optimized
Python modes. This supports adding several frontier points, but it does
not close the native calibration or internal object-ZFC proof obligations.

The current local nine-positive **443-operation, degree-1,845,940**
candidate (450 operations on natural coordinates) remains the low-cost
baseline. The determinant package's **478-operation, degree-1,379,730**
equation is a separate, lower-degree alternative. The more substantial
structural gains in these four packages are the **38-integer quartic**
and **eleven-positive, degree-325, 113-operation** equation. None is a
single winner under variables, degree, arithmetic cost, and numeral size
together.

## Arrivals and finite replay

| Arrival ZIP | SHA-256 | Authenticated manifest files | Full replay phases |
|---|---|---:|---:|
| `con-zfc-residue-orientation-root-transfer-2026-10-23.zip` | `d5b6132c121146e2eed696639ae582ad591bdedf53ae5353e868a2a50fc561b5` | 147 | 6 per mode |
| `con_zfc_calibrated_determinant_guards_2026-10-23.zip` | `5dff4015859932441af06b338c03ffb437c773aab1c69cf0dabb26ff10ad7f97` | 143 | 10 per mode |
| `con_zfc_congruence_and_sextic_2026-10-23.zip` | `37126eddde42680636daaa9a2982937757b3e3b83e37b8514435233c4d2b2867` | 116 | 10 per mode |
| `con_zfc_guard_reanchoring.zip` | `06e5919615b12d45f829bd7e3e398594c1725fa55b629c58d96f34829e8cdf83` | 191 | 11 per mode |

The review first authenticated every listed manifest entry against the
unmodified extraction, then inspected the Python runners and subprocess
calls. The finite mathematics uses the standard library, with no network
calls or removable acceptance assertions found. TeX/PDF rebuilds are
separate and were not run. Every replay used a separate working copy under
`/tmp/proofs62ff-wave10-build-setup/runs/`, with CPython 3.12 at
`/tmp/proofs62ff-wave7-review-venv/bin/python`. This avoids conflating gzip
container differences across Python versions with the raw numeral values.

The residue package command is `python verify.py`, or
`python verify.py --optimized`. The other three use
`python verify_all.py`, or `python -O verify_all.py`. All exited zero.
The residue driver also authenticates its release itself and runs its
components inside a further temporary copy; the other runners regenerate
receipts and some payloads in their working copy. The saved
[replay receipt](PROPOSAL_REVIEW_WAVE10_GUARDS.json) records archive hashes,
mode, elapsed time, exit status, and complete stdout hashes. Raw logs remain
in the scratch directory. The replays check finite identities, dimensions,
operation ledgers, coefficient recipes/bindings, degree certificates, and
source pins. They are not checks of an unbounded compiler theorem.

## Domain-preserving comparisons

The following are the literal metrics of these four arrivals. Integer
entries are unrestricted; positive entries quantify only strictly positive
integers. Operations count every live binary `+`, `-`, and `*`, including
scalar multiplication and squaring, with fixed numeral leaves and register
reuse free. Named registers do not add quantified variables.

| Construction | Domain | Variables | Exact degree | Operations |
|---|---|---:|---:|---:|
| Residue, direct orientation | integers | 40 | 4 | not optimized |
| Residue, eliminated parent | integers | 34 | 6 | not optimized |
| Residue, eliminated parent | integers | 29 | 8 | not optimized |
| Determinant guard | integers | **38** | 4 | not optimized |
| Determinant guard | integers | **32** | 6 | not optimized |
| Determinant guard | integers | **27** | 8 | not optimized |
| Congruence carrier, sextic | integers | 34 | 6 | not optimized |
| Reanchored compact sextic | integers | 34 | 6 | not optimized |
| Root transfer | positive | 11 | **325** | **113** |
| Root transfer | positive | 12 | **84** | **103** |
| Determinant package, centered companion | positive | 12 | 110 | **102** |
| Reanchored, centered product | positive | 12 | 110 | 105 |
| Reanchored, centered SOS | positive | 12 | 164 | 104 |
| Reanchored, adaptive carrier | positive | 13 | 30 | **92** |
| Root transfer, adaptive carrier | positive | 13 | 30 | 94 |
| Congruence inside strong root | positive | 13 | **28** | **98** |
| Retained product coordinate | positive | 14 | **24** | **101** |
| Determinant package, composed nine | positive | 9 | **1,379,730** | **478** |
| Same composed nine, translated | natural | 9 | **1,379,730** | **485** |

Among these arrivals, root transfer's 30/94 is dominated by reanchoring's
30/92 at thirteen positive variables. The 28/98 form remains a degree/cost
tradeoff. At twelve positive variables, 110/102 and 84/103 are both useful;
the two reanchoring twelve-variable forms are dominated by these points.
The determinant integer forms reduce variable count at fixed degree,
but the compact reanchored sextic has a smaller numeral payload. A positive
domain must be translated explicitly before comparison with natural or
integer zero sets; no nine-integer result is implied by the nine-positive
entry. These comparisons cover the four reviewed arrivals and the named
existing baselines, not the other four simultaneous wave-ten arrivals.

## Mathematical review

**Residue orientation.** The new integer soundness argument deliberately
permits both signs of `X` until it has proved `X = +/- 2^R` and odd `R`.
The restriction `X = 3*X3-1` then selects the positive branch modulo three.
The recommended direct quartic preserves all original coordinates except
this replacement and deletes the private square-positivity witness. Its
393 symbolic-port monomials compare with 388 for the parent; this saves a
variable without claiming smaller expansion. The alternate restriction
on `J` and the scale preserves a monic `X` definition and licenses the
sextic/octic eliminations. Completeness for those restrictions uses the
canonical native family, not every old zero. The signed first-norm
classification, the `p>n` bootstrap, and the exclusion of reciprocal roots
are spelled out before orientation; no use of the deleted positivity
guard was found in that chain. The inherited signed auxiliary step-down
and strong-rank theorems remain essential hypotheses, not finite results.

**Determinant guard.** For arbitrary signed assignments the single new
condition `U*V-(q-U-V)^2 > 0`, with positive scales at least two, does imply
that `q,F,C,alpha` share a nonzero sign. Thus it restores both old
common-sign guards. Completeness has a different form: it regenerates
canonical native witnesses, proves the leading-block bounds
`q/2 <= U < 4q/5` and `q/2 <= V < 3q/5`, then represents the resulting
positive determinant by the ternary positivity form. The proof explicitly
controls lower dummy digits and convolution carries; it does not apply
these canonical bounds to an arbitrary source zero. This distinction
avoids a false assertion that the old and new zero sets agree at the same
coordinates. The source-34 tuple and the two scale leaves are all fixed.

The determinant's cost is material: its six main numerals occupy 615,883
raw bytes, including 83,404 additional bytes for powers of two. The exact
pure `J^4` coefficient has 6,924,100 bits. This is a lower bound on maximum
expanded coefficient height, not a certified maximum. Its symbolic-port
expansions have 628/586/707 terms for the quartic/sextic/octic. Therefore
38/4 is a variable-count improvement, not an overall expression-size
minimum. The finite checks reconstruct the whole source-34 tuple and
these scales; no mixing with the compact positive tuple is licensed.

**Root transfer.** The twelve-variable construction absorbs the strong
root into the first transport carrier. Its majorant covers both recovered
root signs and its strengthened transport multiplier gives a positive
inverse coordinate. The eleven-variable extension uses a three-root norm.
Its proof establishes positive, pairwise distinct radicands and a
nonzero signed sum before using rational-root extraction. The elementary
extraction formula has nonzero denominators because coincident
radicands have been excluded. After the two integral radicands give
integral roots, the third root's reduced denominator divides the transport
denominator `M`, while its square divides `Q-1`; prime support in the
strengthened strong multiplier gives `gcd(M,Q-1)=1`. This closes the
otherwise serious denominator gap. The choice order is explicit: select
a strong Pell pair with the required divisibility by a finite matrix-order
argument, reconstruct an auxiliary pair, then compute the transport
weight and its positive inverse. The unit-product finalizer uses residual
square classes modulo four, not assumed residual nonnegativity. No local
logical gap was found in these arguments on read-through; the weighted
carrier and named normalized native/Pell interfaces remain unformalized
dependencies of the final small equation.

**Fixed congruence and reanchoring.** In the thirteen-positive congruence
construction, the normalized strong norm first makes its rational root
integral, recovering `q = beta*(3*j+1)+1` before native index bounds are
used. The positive coordinates `F,alpha,C` already supply the simplex
guard. The adaptive main congruence then recovers the exact Pell index
before `q | X` and transport positivity; its proof retains the possible
gcd factor three. Completeness supplies a positive shifted strong root
and positive first-transport coordinate with explicit estimates. The
fourteenth coordinate is an exact product graph, with inverse `E=X*Y`.
Its sextic uses a retained square relation to justify the cubic
replacement; it is a zero-set restoration identity, not cancellation
valid on arbitrary assignments.

Reanchoring changes the two common-sign guards to equivalent common-sign
products and reselects their positivity witnesses. It makes the transport
monic in the eliminated coordinate. The compact sextic adapter separately
checks the whole compact tuple against the inherited native interface,
actual-rank tuning, odd-scale, and population/parity promises. It is not
just a replacement justified by four size inequalities. Its 295,388 raw
tuple bytes are smaller than the 532,479-byte source-34 tuple; it retains
the same 34-variable sextic skeleton and has 437 symbolic-port terms.
The other new 34-variable sextic has 368 symbolic-port terms with the
larger source-34 tuple. No exact scalar circuit comparison was supplied.

## Calibration and next implementation

All four arrivals correctly distinguish their ordinary unbounded
mathematical proofs from their finite verifiers and from the repository's
Lean/object-language obligations. The ordinary claims compose with
identified native compiler, Pell, and literal K215/refutation interfaces.
They do not supply a Lean proof of the authentic optimized native
calibration or an encoded object-ZFC derivation. They also do not remove
the need to establish the exact object-ZFC consistency predicate in the
requested internal biconditional. Statements in their README tables
should be catalogued with this proof boundary attached.

For current implementation, retain the completed generic/native baselines
and the shared checker arithmetic work; those address the actual formal
gap without depending on a new small native theorem. As parallel small
arithmetic targets, the determinant guard's universal signed soundness
lemma and the three-root rationality/integrality lemma are sharply scoped
and reusable. Formalizing a new nine-variable complete equation before
its native calibration would improve an external candidate while leaving
the same internal obstacle. The new 38/4 and 11/325/113 entries should be
preserved as explicit alternative targets, rather than described as an
already formalized replacement for the closed consistency equation.
