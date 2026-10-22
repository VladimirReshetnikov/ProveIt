# Provenance, compiler binding, and verification scope

## 1. Immutable source snapshot

The upstream repository is
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt),
at commit
`cdd582bec13f908df3711fa9e05d1ddac368a5db`.
All 92 imported files in `vendor/` are exact copies from this commit.
`vendor/manifest.json` gives every original repository path and SHA-256
digest. During packaging, every imported file was also authenticated against
the Git blob ID recorded at that path in the pinned commit. No imported
proof note, table, program, license, or notice was edited.

The flattened filenames make the proof packet convenient to browse. Original
relative links inside the imported files retain their upstream meanings;
they have not been rewritten. To resolve such a link, use the original path
in the manifest and this immutable URL prefix:

```text
https://github.com/VladimirReshetnikov/ProveIt/blob/cdd582bec13f908df3711fa9e05d1ddac368a5db/
```

The package's new `source/`, `artifacts/`, `checks/`, and `proofs/` files are
separate from these unmodified imports. The vendor Python files are source
references, not a newly assembled executable copy of the upstream project's
entire dependency tree. The standalone reproduction commands use the new
standard-library programs under `source/`.

## 2. The exact contradiction machine

The original table is
`Computability/BusyBeaver/Research/ZFC/candidate-k215/k215.tm`.
The copies `source/k215.tm` and `vendor/k215.pinned.tm` are byte-identical.
Their SHA-256 digest is

```text
fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090
```

It has working states 0 through 214, two tape symbols, a two-way infinite
blank tape, start state 0, and halt target 215. Each of its 430 rows gives
`state read write direction next`. Both possible directions are genuine
left/right moves. `vendor/KDense215.lean` contains the literal `rows215`
definition of precisely this machine. Packaging compared all 430 transition
actions in that Lean definition with the text table; every action agreed.

The main imported endpoint is
`SetTheory.BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation`,
with statement

```lean
BlankHalts machine215 ↔ BProv ZFCax_s [] Form.fBot
```

The same module proves `nonhalting_iff_zfc_consistency` by negating the
equivalence. The imported `KEndpoint215.lean`, `KDense215.lean`,
`KDenseBridge.lean`, `KTable215.lean`, `KEndpoint.lean`, `KSource215.lean`,
`KBoot215.lean`, and `KSites215.lean` expose the endpoint, literal table,
renaming, blank initialization, and source/simulation interfaces.
The Rocq endpoint is also included as `vendor/CorrectDense215.v`.
These selected files do not constitute the complete Lean or Rocq build tree.

The pinned `K215-verification-README.md` records upstream Lean and Rocq
verification. It distinguishes those external proof-assistant results from
an internal PA derivation or a formal proof represented in ZFC syntax.
The pinned `K215-ordinary-proof.md` separately supplies the ordinary
mathematical argument formalizable in ZFC, expressly concluding

```text
ZFC proves: Halt(K215, blank) iff not Con(ZFC).
```

The present construction uses that ordinary theorem and the explicit
Diophantine compiler theorem. It does not assert that a fresh complete
Lean/Rocq build was run for this archive, or that the new polynomial
equivalence was kernel checked. No unconditional consistency or nonhalting
claim is part of the construction.

## 3. Imported mathematical proof spine

The imported notes have distinct roles. Historical operation counts in their
titles describe their own sources and must not be substituted for the counts
of the new fixed-marker systems.

| Role | Principal retained sources |
|---|---|
| A finite run from local constraints | `EXPLORATION_FIXED_UNARY_TABLEAU.md`, `EXPLORATION_HELICAL_UNARY_TABLEAU.md`, `EXPLORATION_THREE_CELL_PERIOD_LIFT.md` |
| Stationary first transition and fixed marker windows | `FIXED_RAW_UNIVERSAL_81_PROOF.md`, with its 82/84 predecessors |
| Native copy fields, period alignment, and marker uniqueness | `FIXED_RAW_UNIVERSAL_78_PROOF.md`, its 80 predecessor, `FIXED_RAW_UNIVERSAL_77_PROOF.md`, `EXPLORATION_CYCLIC_MARKER_BIJECTION.md` |
| Reusing the main Pell power as the temporal shift | `FIXED_RAW_UNIVERSAL_76_PROOF.md`, `EXPLORATION_FIVE_ADIC_DUMMY_CONTROL.md` |
| Modified half-binomial masks and the retained complete compiler | `complete75_half_binomial_compiler.md`, `FIXED_RAW_UNIVERSAL_75_PROOF.md`, `pell_kernel_half_binomial42.md` |
| Pell rank, congruence, and sign lemmas | `PELL_RELAXED_AUXILIARY_PROOF.md`, `PELL_SIGNED_PROOF.md`, `PELL_COMMON_WITNESS_PROOF.md`, `PELL_DOUBLED_INDEX_PROOF.md`, `HALF_PARAMETER_PELL_92_PROOF.md`, `EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` |
| Positive-coordinate elimination, normalized strong equation, and smaller scale | `complete75_positive_elimination.md`, `complete75_coupled_index_linear88.md`, `complete75_normalized_strong87.md`, `complete75_asymmetric_scale_tradeoffs.md` |
| Literal scaled-normalized and ordinary polynomial interfaces | `complete86_factored_first_root.md`, `complete86_transport_quotient_shear.md`, `complete85_auxiliary_bezout_projection.md`, `complete84_scaled_strong_output.md`, `complete85_reduced_auxiliary_degree.md`, `complete86_ordinary_auxiliary_projection.md`, and their retained reviews |
| Signed auxiliary quotient and integral strong-root reconstruction | `complete84_signed_quotient_absorption.md`, `complete84_signed_quotient_soundness_scout.md`, `review_complete84_signed_quotient_soundness.md`, `complete92_norm_unit_guard.md` |
| Restoring a split positive main-root coefficient | `complete75_gamma_dominance_elimination102.md` |

The exact four upstream JSON instruction arrays used by the fixed-marker
transformation remain in `vendor/`. The new proof of that transformation and
its independent review are in `proofs/FIXED_MARKER.md` and
`proofs/INDEPENDENT_REVIEW.md`. The compiler definitions and their elementary
specialization to K215 are in `proofs/COMPILER.md`.

The signed-quotient review explicitly restricts its conclusion to valid
compiler numerals. In particular it uses the native mask's residue modulo
four. The present construction supplies the complete compiler recipe;
arbitrary positive replacements of its coefficient ports are not allowed.

## 4. Exact finite program and window order

`source/compiler_k215.py` defines a deterministic machine with 436 states,
six tape symbols, and all 2,616 transition entries. The full table is also
exported as `artifacts/folded_machine.json`. Its six initial control states
are followed by the 215 positive-side and 215 negative-side simulation
states. A finite unary input is erased, then the exact blank K215 machine
is simulated on a folded tape. The accepting state is absorbing and every
unspecified branch enters an absorbing nonaccepting state.

The initial transition writes the origin symbol 2, stays in place, and
enters a distinct nonhalting state. For a positive unary length `l`, the
erasing prefix reaches the encoded blank K215 start in `2*l+2` transitions.
The one-sided tape restriction and local transition correspondence have a
direct invariant proof in `COMPILER.md`; the finite checks cover 5,160
individual folded-transition cases and seven input lengths.

The older complete76 exposition chooses a semidecision machine for the even
image of its queried set. Our erasing machine accepts every finite unary
length exactly when K215 halts. The proof only queries the distances `2*x`,
corresponding to unary lengths `2*x+2`; acceptance at other distances is
irrelevant. Equivalently, apply the proof to the set of `x` for which this
particular machine accepts at distance `2*x`. At `x=1` the initial tape has
four ones, and the erasing prefix takes ten transitions.

The finite tile alphabet is ordered as follows: the vertical boundary, the
horizontal boundary, the ordinary symbol/head combinations, then the four
initialization phases L, I, Q, R. It has 2,628 elements. The local predicate
is the pinned helical predicate on that alphabet. The membership checks
omitted from the standalone predicate are tautologies for these enumerated
tiles. In particular, the horizontal boundary flag propagates only between
nonvertical-boundary cells; copying the earlier globally propagated flag
would give the wrong helical semantics.

The window list begins with Start, then End. Subsequent windows enumerate
valid axial crosses `(center,left,right,down,up)` lexicographically, then
the four corner indices `(nw,ne,sw,se)` lexicographically, excluding the two
already listed markers. Each resulting window is stored in row-major order

```text
(nw, down, ne, left, center, right, sw, up, se).
```

Here down is the row at time offset -1, and up is the row at time offset +1.
The labels for the four corners do not change this explicit positional
definition. The coefficient construction allows any ordering of the allowed
windows after the two distinguished markers. Its copy fields use this exact
row-major order, with clause index `1+(3*r+c)*a+s`, and exponents reversed
in both spatial indices as specified in `COMPILER.md`. This matches the
upstream generic `compile_windows` definition.

There are exactly 43,126,116,188,949 valid axial crosses. Since the local
predicate ignores the corners, each cross has exactly `2628^4` extensions,
giving

```text
k = 2057035525715746135339455744
```

distinct permitted windows. Moving Start and End to the beginning and
omitting their later occurrences preserves that cardinality. The cross
counter evaluates the finite sum by grouping incoming-head states, rather
than enumerating this enormous set.

## 5. Fixed coefficient choices and permitted padding

The standalone compiler does not claim to reproduce the upstream default
choice of the *smallest* adequate radix. It makes two explicitly permitted
padding choices. First, it chooses the clause radix `A=2^92`, satisfying
`A>k+1`, with 92 a multiple of four. Thus `A=1 mod 5`, so the optional
high-term correction can be evaluated exactly without enumerating the
windows. Second, it rounds the bit-field width upward to a power of five
using the conservative coefficient-mass bound proved in `COMPILER.md`.
The no-carry inequalities require lower bounds on these radices; they are
preserved by these larger choices.

The resulting fixed layout values are

```text
b = 5^42 = 227373675443232059478759765625
L = 5^43 = 1136868377216160297393798828125
d = b*L = 5^85
  = 258493941422821148397315216271863391739316284656524658203125.
```

The high-term correction is zero because `2*DC-DR = 2 mod 5`. There is one
ignored dummy position. Its extra bit is retained, as required by the
modified half-binomial mask. The six original fixed ports are

```text
Bm1             = B - 1
Kconstant       = DC + B*DR
twice_cell_bits = 2*d
inner_bits      = b
MC              = MC_old - 2*R^dummy_first
MF              = MF_native + B - 1,
```

where `R=2^b`, `B=2^d`, and `MF_native=MF_old+4`. In particular, exporting
the old cached mask values or omitting the `B-1` adjustment of the source
port MF would give a different, unsupported polynomial. The fixed-marker
specialization adds the determined numeral `W0=2^b*B^2`.

Every coefficient is specified by finite sums with explicit finite bounds,
using the concrete transition table and window order. No unknown program
index, proof-search stopping time, Diophantine witness, or existential
coefficient selection remains. These are compressed definitions of fixed
integers. The astronomical decimal expansions and the complete window list
have not been materialized; no claim about their practical enumeration is
made.

## 6. Additional packaging audit

Besides the reproducible checks already recorded in
`artifacts/compiler_checks.json`, packaging performed the following
independent source-binding checks:

* All 92 vendor files matched the pinned commit's Git blob IDs, and their
  SHA-256 digests matched the manifest.
* All 430 literal K215 actions matched `KDense215.rows215`.
* The actual imported upstream helical predicate was compared with the new
  predicate on all `18^5 = 1,889,568` axial crosses of the retained small
  fixture. Both accepted exactly 121,165 crosses, with equal counts for
  every center tile.
* The same two predicates agreed on 20,000 deterministic sample crosses
  using the actual 2,628-tile K215 alphabet.
* Recomputing the full compressed coefficient recipe produced an object
  identical to `artifacts/coefficient_recipe.json`.

Inspection also checked the Start/End ordering, row-major copy coordinates,
zero-clause padding, four anchors, dummy position, shifted native masks,
and the sufficient radix bounds against the pinned compiler formulas.
No discrepancy was found in this finite specialization. The fresh checks
do not replace the inherited unbounded arithmetic and tableau proofs, or
convert those ordinary mathematical proofs into proof-assistant
certificates. `proofs/INDEPENDENT_REVIEW.md` states the separate review scope
of the new fixed-marker and strong-root transformations.

## 7. Attribution and inherited terms

`vendor/K215_NOTICE.txt` is the exact original `candidate-k215/NOTICE.md`.
The name change is only for packaging; its contents are unmodified. Its
scope statement describes the original allocation packet, while the later
verification README supplies the compiled endpoint status.

The archive also retains the exact root ProveIt license, the K215 copies of
the ProveIt and Andrew James Wade licenses, the normalized-source and
original-245 notices, the source pins, and the immediate partial-selector
and command-permutation attribution chain. These are recorded individually
in the manifest. Inherited notices credit the underlying machine,
calculus, compiler, checker, and proof developments within their own stated
scopes. They are not replaced by attribution for the present Diophantine
specialization. No new license or relicensing of third-party components is
asserted here; consult the retained original texts.
