# Choosing the next equation from the recent proposals

Reviewed 23 October 2026, through wave-7 placement `6d375f2d2d`, merged at
`d869b0ddbf`. The review includes all eight new packages 46–53 and compares
them with the wave-5/6 proposals and the current checked construction.

## Decision

**Switch the small-nine formalization target to package 52's interior-regular
equation:** nine positive integers, 548 live binary arithmetic operations,
reported exact degree 15,502,748. Its natural-coordinate version costs 551
operations. It improves the former package-45 target on degree, operation
count, and native coefficient size, while retaining the existing Jones
ratio theorem. Its conservative carry construction requires fewer new
arithmetic lemmas than the lowest-degree alternative.

Keep **package 53's calibrated equation** as the next degree target, rather
than discarding it: nine positive integers, 738 operations, degree 7,344,328.
It introduces a sparse signed-borrow decoder and a calibrated popcount
threshold. Those are substantial new correctness obligations, but the
proofs reviewed here address them without an apparent circular bootstrap.
Its near-square finalizer is useful immediately for the shared development.

The working comparison prioritizes nine natural/positive coordinates, then
arithmetic circuit size, while retaining the nondominated degree tradeoffs.
This is a research choice, not a theorem that one equation is simplest under
every measure. Future proposals can change the target. A replacement must
have a complete coefficient binding, a checked source-to-refutation bridge,
and the required internal ZFC proof before replacing the certified endpoint.

`ExplicitZFC.expression` and `NativeZFC.expression` remain the closed,
externally certified equations. The selected numerical proposal does not yet
have their end-to-end Lean certificate. Changing an exponent in the old
Jones theorem cannot supply that certificate: its source encoding changes.

## The surviving nine-variable choices

All degrees in this comparison are the proposals' exact-degree claims,
supported by their replayed finite certificates. Counts were independently
recomputed from the literal circuits. Every row has nine strictly positive
integer variables; none asserts an unrestricted-integer result.

| Candidate | Operations | Degree | Use |
|---|---:|---:|---|
| [52 interior regular](con-zfc-diophantine-forms/52-sparse-pell/nine/generated/nine_174_interior_regular_positive.json) | 548 | 15,502,748 | First replacement target |
| [52 interior shifted](con-zfc-diophantine-forms/52-sparse-pell/nine/generated/nine_174_interior_shifted_positive.json) | 603 | 10,486,092 | Degree/cost compromise |
| [52 interior packed](con-zfc-diophantine-forms/52-sparse-pell/nine/generated/nine_174_interior_packed_positive.json) | 655 | 10,127,484 | Further degree tradeoff |
| [53 calibrated](con-zfc-diophantine-forms/53-selective-quad/nine/generated/calibrated_positive.json) | 738 | 7,344,328 | Lowest reviewed degree |

These four points are mutually nondominated on degree and operations. Every
reviewed nine-positive point in packages 46–51 is dominated by at least one
of them. The natural-coordinate versions of the three package-52 rows add
three operations; package 53 adds six. Package 52 uses the whole compact
native tuple with radix exponent 590,069; package 53 retains exponent
1,064,921. This coefficient advantage strengthens the package-52 choice.

## Other domains and measures

* **Ten unrestricted integers:** the surviving reviewed degree/cost points
  are package 52's 582 / 50,822,936 and 637 / 34,378,296, and package 53's
  659 / 21,111,400. All require Sun's additional ten-integer theorem. These
  are separate targets from nine natural or positive variables.
* **Eleven positive integers:** package 52 gives 113 operations at degree
  954, improving package 50's 115 / 954 and package 53's 117 / 958. Its
  shifted two-equation system costs 108 operations, maximum degree 952.
* **Twelve positive integers:** package 52's 108 / 897 improves the previous
  112 / 901 point. Its shifted three-equation system is 102 / 888.
* **Fifteen positive integers, fewest operations:** package 51 has a new
  66-operation circuit at degree 157. It saves one operation over P67 but
  adds two degrees; neither dominates the other. Its stronger auxiliary
  congruence requires a new completeness proof, not a tuplewise identity
  in the old quotient coordinate.
* **Fifteen positive integers, lower degree:** package 47's 75 / 44 is a
  useful target. Its clean 76 / 44 version has a purely local minimum-norm
  proof against the ordinary-strong gap system. Its connection to the
  normalized P67 family uses an inherited relaxed-rank argument. These
  are different coordinates and, in places, different whole coefficient
  tuples. The current normalized-family 76 / 64 theorem does not already
  certify them. Packages 46 and 51 also save one operation at degree 68;
  packages 51 and 53 give 72 / 80 through different arithmetic adapters.
* **Coefficient size alone:** package 46's separate parity-anchor adapter
  reports radix exponent 429,959 and 215,492 raw coefficient bytes. It is
  not bound to the selected main equation. Transplanting its individual
  ports into package 52 or 53 would invalidate the binding; a new complete
  adapter and all coefficient-dependent bounds would have to be proved.

The detailed positive/Pell and quadratic reviews are in
[PROPOSAL_REVIEW_POSITIVE.md](PROPOSAL_REVIEW_POSITIVE.md) and
[PROPOSAL_REVIEW_QUADRATIC.md](PROPOSAL_REVIEW_QUADRATIC.md).

## What changes in the Lean work

The reusable core now follows the proposals instead of optimizing only the
old generic quartic source:

1. Selective quadratic extraction with arbitrary weights and row targets.
   Only used pairs must be isolated against **all** possible pairs. Intervals
   may overlap if no foreign term hits a selected target.
2. Instantiate the finite support certificates and bind the actual native
   quadratic rows. A finite support certificate alone is not the native
   compiler theorem.
3. Prove the source's range, digit-mask and binomial-divisibility contracts.
   Package 52 can initially reuse dense carry padding. Package 53 also
   needs signed-borrow normalization and its different block length `L`
   and ratio threshold `N`.
4. Formalize the near-square majorant/finalizer, retaining the proved
   numerical Jones ratio interface, and close the native source-to-K215
   bridge. Keep the separate object-language ZFC internalization work.

The general extraction theorem and the literal 46/52 active-pair isolation
certificates now pass Lean. `SelectiveCertificate52.coeff_rows` checks the
regular-target coefficient identity for every coefficient family on the
certified support. `NearSquareFinalizer.exists_value_zero_iff` also checks
the two-root finalizer against square tests, divisibility and positive
margin. `MinimumNorm` checks the local ordinary-strong 75/76 minimum-norm
equivalences. These are specific new formal milestones, with standard
axiom audits; the complete released circuits and semantic bridges remain
separate obligations.

The small-source compiler and the object-language proof remain the major
semantic obligations. None of the new proposals supplies a new end-to-end
Lean/Rocq certificate or an actual internal ZFC equivalence derivation.
Ordinary proofs described as formalizable in ZFC do not discharge that last
requirement; [OBJECT_ZFC.md](OBJECT_ZFC.md) records its exact status.

## Reproduction and review limits

The original arrival ZIPs at `4b4349064a` were extracted into scratch
directories. The placed trees intentionally omit byte-identical duplicate
members and some ledgers, so they are not complete replay packages.
No delivered manuscript, coefficient, or circuit was rewritten.

Full original-release replays passed for packages 46, 47, 48, 51, 52 and 53.
Package 52 authenticated 330 file hashes and 132 source blobs and passed all
11 authored checks under Python 3.12.13. The parallel positive review also
records focused 49/50 checks.
Packages 51 and 52 needed Python 3.12 for strict gzip-byte reproduction;
their Python 3.13 runs failed only that packaging comparison. Package 53's declared
NumPy/SymPy dependencies were installed in a temporary environment.

The independent standard-library script
[`review_proposal_frontier.py`](tools/review_proposal_frontier.py) checks
topology, liveness and counts for 38 literal circuits without importing any
delivered program, and records byte hashes and degree/cost dominance in
[`wave7-circuits.json`](reviews/wave7-circuits.json). Its degree entries are
explicitly reported metrics; it does not infer exact degrees from a naive
walk through cancellations.

The replays check finite data, coefficient bindings, exact algebraic and
degree certificates, and implementations of the displayed formulas. They
do not establish consistency, replace the universal mathematical proofs,
or certify the unbounded compiler and object-language interpretation.
