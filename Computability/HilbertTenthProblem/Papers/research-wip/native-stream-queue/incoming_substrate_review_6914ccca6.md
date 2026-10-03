# Review of three new computational-substrate reports

The three relevant archives arriving in commit `6914ccca6` contain useful
explicit Diophantine compilers. None establishes a smaller universal
arithmetic-operation count. Review found two concrete input-validation
defects in the van Kampen software, including a corrupt polynomial export,
one mutable-input defect in the low-level Heisenberg API, and two
opportunities to reduce the delivered certificate constructions.
The established universal polynomial bound remains **87 operations**.

This review concerns the new archives, separately from the
[earlier review of three report collections](imported_substrate_review_20261002.md).
The delivered archives are preserved unchanged. Three reviewers read the
respective manuscripts and code, replayed the supplied tests in scratch
copies, and checked selected primary dependencies. Integration review
independently checked the key algebra, reproduced both software defects,
and added the [source-pinned checker](incoming_substrate_review_6914ccca6.py)
and [receipt](incoming_substrate_review_6914ccca6.json).
These are mathematical reviews and finite checks, not formal verification,
a general solver, or an exhaustive literature-priority audit.

## Sources and scope

The immutable arrival contains:

- [Arithmetic van Kampen Certificates](https://github.com/VladimirReshetnikov/ProveIt/blob/6914ccca6/docs/incoming/arithmetic_van_kampen.zip),
  especially the exact free-group chart, area-budget and proof-DAG compilers.
- [Three Commutative Phases Are Diophantine-Universal](https://github.com/VladimirReshetnikov/ProveIt/blob/6914ccca6/docs/incoming/three_commutative_phases_research.zip),
  especially the three Heisenberg subgroup maps and their exact fibers.
- [Infinite Quantum Runs, Finite Diophantine Certificates](https://github.com/VladimirReshetnikov/ProveIt/blob/6914ccca6/docs/incoming/Infinite_Quantum_Runs_Diophantine_Certificates.zip),
  especially the inverse certificate, moment recurrence, and forbidden-word
  reduction.

The receipt pins each archive and every member by SHA256. The checker reads
the archive from `docs/incoming` or, if subsequent intake retires it, from
the tracked arrival commit. Other archives in the same delivery concern
unrelated subjects and are outside this review.

Concurrent placement commit `2a04b60f2` subsequently retired these archives
and imported their code into the maintained
[group-theoretic collection](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/group-theoretic-substrates/README.md)
and [quantum collection](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/probabilistic-quantum-and-continuous-computation/README.md).
This review's tested repairs are now also applied to the maintained
[van Kampen module](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/group-theoretic-substrates/code/03-van-kampen-van_kampen.py)
and [Heisenberg module](../../../../../SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/group-theoretic-substrates/code/05-three-phases-heisenberg_compiler.py).
Their bytes match the independently tested patched sources below. Normal
review replay both reproduces the original defects from Git history and
checks that the maintained source prevents them.

| Construction | What is explicit | Boundary for universal operation minimization |
|---|---|---|
| van Kampen proofs | Quartic integer certificates for fixed area budgets and fixed proof-DAG shapes; four-coordinate exact free-group conjugators | Area or proof shape still determines the number of witnesses. No numerical universal presentation, ordinary-input loader, or fixed-size unbounded proof decoder is supplied. |
| Three Heisenberg phases | Every specified quadratic system compiles to three free abelian subgroups, with a bijection of solution and factorization fibers | Fixed universal subgroups are obtained by starting with MRDP and a fixed circuit. The reverse compiler recovers the original arithmetic; the new group structure alone is not an operation saving. |
| Quantum loops | Complete quartic natural certificates for finite-dimensional, time-homogeneous aggregate statistics, independent of execution duration | These aggregate statistics are computable by rational linear algebra. Undecidability concerns an unbounded finite-word support question, whose fixed arithmetic decoder is not constructed here. |

## Software findings and tested fixes

### Floating conjugators can corrupt the exported polynomial

In `arithmetic_van_kampen/code/van_kampen.py`, `unchart` at line99 does not
require exact integer entries. `validate_dag` at line343 accepts the float
identity as a fixed conjugator. `PolynomialSystem.export` at lines234–236
then converts rounded SymPy coefficients with `int(coef)`.

The complete reproducer is:

```python
r = 'ab' * 30
nodes = [Node('leaf', word=r),
         Node('fixed_conjugate', (0,), matrix=(1.0, 0.0, 0.0, 1.0))]
compile_dag(nodes, [r]).export('bad.json')
```

The exported polynomial has no witnesses and four residuals. All four
vanish exactly at the boundary

    (79026329715516207267840, 32733777552734746050560,
     32733777552734746050560, 13558774610046710972416).

Its determinant is **−69402857361589764505112412160**, rather than1.
The true exact relator matrix has determinant1 and different entries.
This is a compiler input-validation defect, not a counterexample to the
mathematical theorem on its exact integer domain. Reject noninteger matrix
entries before arithmetic and reject noninteger polynomial coefficients
instead of coercing them at export.

### The zero-budget numeric checker accepts an empty boundary

In the same source, `budget_residuals` at line192 returns before validating
the zero-budget boundary. Its matrix subtraction truncates through `zip`:

```python
budget_residuals(['abAB'], BudgetWitness([], [], [], [], ())) == []
```

A caller checking `not any(residuals)` therefore accepts a record with no
boundary matrix. Extraneous zero-budget arrays are also ignored. Require
four exact boundary entries and the correctly empty arrays before returning
the four identity residuals. The valid symbolic zero-budget compiler is
unaffected. The review checker reproduces both findings against the original
pinned source, so later repairs do not erase the evidence.

### A mutable Heisenberg row can desynchronize the compiled maps

The three-phase module's frozen `QuadraticRow` validates Python lists but
discards the immutable tuples returned by its validation helper. A caller
can therefore mutate an accepted coefficient list after compilation:

```python
linear = [1]
row = QuadraticRow(0, linear, [0])
c = compile_quadratics(1, [row])
linear[0] = 2
```

Now `c.evaluate([1])` gives2, while the compiled three-phase factorization
still targets1. This is a lower-priority Python-constructor issue: the
documented JSON path already normalizes its vectors to tuples and is
unaffected. Snapshot the validated linear, diagonal, and cross-term
containers in the frozen constructor. The general fiber theorem for an
unchanging exact quadratic system remains valid.

The [van Kampen guard patch](van_kampen_exact_input_guards.patch) and
[Heisenberg snapshot patch](heisenberg_immutable_rows.patch) are supplied
as reviewable repairs to extracted source copies and are also applied to
the maintained modules. The historical archives and the
checker's original counterexamples remain immutable. Both patches were
applied to private copies and passed the complete respective author suites
with unchanged mathematical test counts. Focused checks covered 68 malformed
van Kampen calls and 108 Heisenberg mutation/type cases. Integration review
independently applied both patches and confirmed the reported counterexamples
are rejected or prevented while valid inputs still work.

From an extracted package directory, apply its patch with `patch -p1`
and standard input redirected from the corresponding repository patch file.
Then run `python code/verify.py`; the van Kampen verifier additionally accepts
`--receipt /tmp/patched-van-kampen-receipt.json`. These commands modify only
that extracted review copy. The expected patched Python SHA256 values are:

| Source | SHA256 after applying its patch |
|---|---|
| `code/van_kampen.py` | `8c3eb6cb858fba47525422b95514ee52739b38d79883ff18f523a2c2a22f5dae` |
| `code/heisenberg_compiler.py` | `495eb191fe878d8c83cb4adfcb14c4b8654a2191e94c45ce5afe7d67aae9f341` |

## Arithmetic reductions derived from the reports

### An integer selector sphere and the first matrix elimination

The [guarded selector-sphere compiler](van_kampen_selector_sphere_projection.md)
implements the following reduction against the actual pinned source and
stores complete parent and successor polynomials for 15 source forms.

For a nonempty table of s relators and budget m>=1, the van Kampen source
allocates q=2s+1 label selectors per cell, including an identity label. Its
original allocation is `(2s+13)m−4` integer witnesses and `(2s+11)m`
quadratic residuals.

Keep the 2s nonidentity selectors and impose only

    sum(e_j²) + (sum(e_j)−1)² − 1 = 0.

Over the integers the only zeros are the zero vector and the positive
coordinate vectors: the sum of the displayed squares is1, and a negative
coordinate vector fails the second square. Restore the omitted identity
selector by `e0=1−sum(e_j)`. After that substitution the sphere residual is
exactly the sum of the original Boolean residuals; each `e(e−1)` is
nonnegative on integers. Thus no cancellation conceals a bad selector.

Also `P0=I` forces the first helper matrix `V1=U1`; substitute it and remove
its four coordinates and four defining residuals. Combined, the allocation
becomes **`(2s+12)m−8` witnesses and `10m−4` residuals**, still of degree at
most four after the sum of squares. For one relator and one cell this is
**6 witnesses /6 residuals**, down from **11 /13**. Projection and the stated
restoration give a bijection of full integer zero tuples. No integer
arithmetic-operation schedule is charged by these allocation counts.

Its fresh replay passes 180 signed off-zero corrections, 90 full zero
round trips, 90 corrupted boundaries, 19,530 selector cases and 150 malformed
calls. Root integration review independently checks 12 source forms,
96 corrections and 48 malformed packets.

### Three matrix equations for the canonical quantum inverse

The [guarded three-equation compiler](quantum_three_equation_inverse.md)
implements the following canonical reduction with seven complete exported
inverse-core polynomials. Each export pins a fixed rational input matrix T.

The report uses `A=I−T` and the four equations

    AG+P=I, GA+P=I, AP=0, GP=0.

They can be replaced by

    AG+P=I, AP=0, PG=0.

The product order in **PG** is essential. The first two imply `A²G=A`,
so `rank(A²)=rank(A)`. Consequently the kernel/image splitting exists.
In a basis with `A=diag(0,B)`, B invertible, those equations force the
bottom blocks of G to be `0,B⁻¹` and P to be `diag(I,0)`. Then `PG=0`
kills both top blocks of G. This gives precisely the original unique
group inverse and projection, including at singular A. Matrices with a
nontrivial zero Jordan block admit no solution.

Simply deleting `GA+P=I` while keeping `GP=0` would be wrong: with
`A=diag(0,1)` and `P=diag(1,0)`, every `G=[[0,t],[0,1]]` satisfies those
three old equations. The new product order removes this free parameter.

Keeping the report's canonical rational encoding, the dense source has

    multiplications = 3D³, additions/subtractions = 3D³−D²,
    rational wires = 6D³+2D²+2, pins/equalities = 4D²+2,
    natural witnesses = 66D³+9D²+14,
    quadratic residuals = 54D³+6D²+10.

At D=4 this is **4,382 witnesses /3,562 residuals**, down from **5,790 /4,730**.
It saves D³ rational multiplications and D³ rational additions while
preserving the unique natural extension of each correct rational interface.
These rational-circuit counts are not an integer-polynomial operation bound.

Its fresh replay rejects 10,187 single-coordinate mutations and 52 malformed
calls. Independent cross-review confirms the proof, literal source, counts,
degree and natural uniqueness, with nine rational similarity examples,
72 complete SOS comparisons, 78,125 canonical-wire cases and 118 malformed
calls. Root integration independently checked five emitted inputs and
35 malformed packets. Neither this wrapper nor its count includes the full
moment compiler or an unbounded measurement-word decoder.

If only existence is needed, canonical rational wires can instead be
replaced by `n=p−m,d=h+1` with three natural coordinates, omitting both
wire normalization and gate-product sign normalization. Positive
denominators still justify every cross multiplication. This deliberately
loses uniqueness and gives the derived formulas
`V=3W+5a+3m`, `R=4a+3m+e`. Combined with the three-equation inverse they
become `V=42D³+D²+6`, `R=21D³+2`. These optional formulas describe an
existence-only construction; they are not claimed as reproduced exports
or as a universal bound.

## Mathematical conclusions and universality limits

The van Kampen chart, inverse-crossing equations, literal allocation
counts and specified proof-DAG optimum were checked on their integer
domains. Its dyadic grid has exponential expanded area but a linear number
of product gates in that particular proof calculus. This is not an optimum
over all Diophantine representations. The exact chart agrees with the
[primary Sanov exposition](https://arxiv.org/abs/1605.05226), and the
height proof uses the bounded-conjugator lemma in
[Cornulier–Tessera](https://arxiv.org/abs/1310.5373).

The three-phase construction uses the integral identity
`xy=binom(x+y,2)−binom(x,2)−binom(y,2)`. Its product equations force
`y=x`, `r=Lx`, and `u=binom(Lx,2)`, so the claimed fiber bijection is an
explicit algebraic fact. The reverse quartic restricted to this unique
extension is `sum(F_j(x)−t_j)²`; equivalently, doubling the final residuals
would give four times that sum. Eliminating the extra coordinates recovers
the original quadratic system and supplies no new universal compression.

The proposed three-subgroup result addresses the question actually stated
in [König–Lohrey–Zetzsche, Remark6.7](https://arxiv.org/abs/1507.05145):
their Theorem6.6 supplies four fixed abelian subgroups in a fixed Heisenberg
power, and the remark asks about three subgroups in polycyclic or nilpotent
groups. The new construction fits those quantifiers. It does not assert
three cyclic subgroups of one three-dimensional Heisenberg group. Review
found no theorem-level defect in the checked proof; this does not establish
historical priority or replace independent refereeing.

The quantum report correctly separates three predicates. Fixed-dimensional
aggregate stopping statistics have rational certificates. A fixed geometric
clock preserves the zero probability of each legal completed finite word;
that support-existence predicate remains undecidable by the cited
[Eisert–Müller–Gogolin theorem](https://arxiv.org/abs/1111.3965).
In contrast, a uniformly computable external schedule can encode
nonhalting into an exact probability answer, preventing a uniform
existential graph. These are different quantifier patterns. The report's
all-moments interface certifies a finite recurrence, not free evaluation
at an arbitrarily supplied moment index.

## Executed evidence and replay

The supplied van Kampen suite reproduced 13,121 reduced-word checks,
83,521 chart tuples, 3,615 valid and 10,845 corrupted area certificates,
441 dyadic grids, the area2^200 example, and its symbolic/DAG checks.
The quantum suite reproduced **33,708 assertions**, including **31,892**
single-coordinate mutation rejections; all five example JSON files were
byte-identical to the delivery.
The three-phase suite reproduced **190,826 exact assertions**, including
its signed exponent cases, small-box search, and modular certificates.

The independent integration checker additionally records:

- both van Kampen defects and the full false boundary;
- the accepted mutable Heisenberg constructor counterexample;
- the maintained repaired sources, nine malformed-input rejections, valid
  zero-budget and large-relator cases, and nested coefficient snapshots;
- 512 randomly generated quadratic normal-form checks, 512 canonical
  factorization checks, 512 off-zero quartic identities, and 844
  within-phase commutations checked using ordinary 3x3 matrix multiplication;
- all four original quantum exports checked through the supplied independent
  standard-library verifier;
- 4,375 two-dimensional matrix assignments comparing the three- and
  four-equation inverse zero sets, including singular and nonsemisimple
  cases, and the explicit wrong-product-order counterexample.

Run from the repository root with Python and SymPy available:

```sh
python Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/incoming_substrate_review_6914ccca6.py
```

Use the full path when outside the repository root. Normal execution
recomputes and compares the receipt; `--write` regenerates it. Finite cases
support the source audit. The arguments above, with the imported reports'
stated hypotheses, justify the general constructions.
