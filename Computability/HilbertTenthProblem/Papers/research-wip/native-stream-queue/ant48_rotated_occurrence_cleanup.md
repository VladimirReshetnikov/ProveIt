# Removing zero arithmetic and repeated expressions from the ant rotations

The complete [new component](ant48_rotated_occurrence_cleanup.json) has
**7,818=3,930M+3,888A operations**, saving **68=20M+48A** beyond the
[frozen six-block component](ant48_rotated_occurrence_sharing.md).
It computes the identical24 output polynomials over all integer assignments
of the957 occurrence coefficients for each of four kinds and the scalarY.
It adds no coordinates, equations or literals. Every new row is live.

The total saving from Report48's original24 independent Horner arrays is
38,214 operations. Composing with the disjoint
[nine-M endpoint reuse](periodic_ant_endpoint_reuse48.md) saves38,223 in
all, giving derived complete two-/one-input grammar counts
**14,620,711 /14,620,721**. The complete multimillion-operation source is
specified by substitutions into the inherited grammar; it is not newly
emitted or hashed. The current universal84 bound remains unchanged.

## Exact successor and identity proof

The helper authenticates the full predecessor source/proof/receipt and the
endpoint-reuse receipt with SHA256. They are read as bytes and JSON, never
imported or executed. The new receipt includes all7,818 arithmetic rows,
the24 named output wires, all3,829 inherited input bindings and a transcript
of every removed operation. Existing frozen artifacts remain unchanged.

Process the parent component in topological order, replacing each operand
by its current alias. The following identities are valid in every commutative
ring and are applied literally:

* x+0=0+x=x:32 parent addition rows disappear;
* x*0=0*x=0:four parent multiplication rows disappear;
* two additions or multiplications with the same unordered pair of aliased
  operands have the same value:32 repeated rows reuse an earlier output.

The zero is the parent's already proved and paid expression1-1. It is not
an independent variable specialized using an additional equation. The parent
coefficient arrays have three zero slots per kind; the complete zero-folding
transcript identifies all affected rows. The common-expression lookup only
shares identical operator/operand keys, with no numerical fingerprinting or
probabilistic equality decision.

Induct on parent rows. Each surviving output has its parent's polynomial;
each removed output aliases either that same polynomial at a previous row
or the known zero expression. Every named output therefore retains its
polynomial. Sorting the two inputs of a multiplication uses commutativity,
which is valid for the integer-polynomial representation. All aliases point
to ports or strictly earlier rows. The resulting output dependency closure
contains every emitted row; no further dead-row deletion is needed.

The zero binding is now the sole unused component input and is removed from
this component interface. Its producer stays retained and paid in the complete
parent prefix, which also uses zero elsewhere. The new3,829 inputs are exactly
Y and the3,828 occurrence coefficients. No global liveness claim follows from
the component's local liveness check.

## Independent exact coefficient check

A separate interpreter in the new helper reconstructs every emitted row as
a sparse polynomial inY, linear in the independent occurrence coefficients.
For each kind a, block choice b in0..2 and phase in{0,288000}, it checks
coefficientwise against the independently stated formula

    sum(s=0..956) T[a,s] Y^((480-b-s-phase/600) mod960).

All24 outputs have957 terms, so22,968 exact term identities are verified.
The residue notation fixes a nonnegative integer exponent; it is not an
identity Y^960=1. The output identity holds atY=0,1,-1 and every other integer.
Ninety-six finite-field output evaluations at four bases supplement this
coefficient proof. They are not the basis of the equality claim.

## Paid component and complete grammar ledgers

| Component | M | A | Total |
|---|---:|---:|---:|
|Frozen six-block source|3,950|3,936|7,886|
|Zero arithmetic removed|4|32|36|
|Repeated expressions removed|16|16|32|
|New emitted source|3,930|3,888|7,818|
|Original24 full Horner arrays|23,016|23,016|46,032|
|Saved from original arrays|19,086|19,128|38,214|

The unchanged24 products and22 phase-sum additions remain paid, so the
whole rotated stage becomes3,954M+3,910A=7,864. The fused spatial source
becomes53,893 gates. Retain the14,563,366-gate prefix and the other main
parts, and optionally apply the disjoint endpoint deletion:

| Complete inherited grammar | M | A | Total |
|---|---:|---:|---:|
|Two inputs, rotation cleanup only|5,952,034|8,668,686|14,620,720|
|One input, rotation cleanup only|5,952,038|8,668,692|14,620,730|
|Two inputs, also endpoint reuse|5,952,025|8,668,686|14,620,711|
|One input, also endpoint reuse|5,952,029|8,668,692|14,620,721|

These are inherited complete-grammar ledgers plus exactly checked deltas,
not newly generated full-stream hashes. The original24 products, two phase
sums, all other source rows, declarations and the entire finalizer remain.
Induction through those unchanged consumers preserves the whole polynomial,
its465/467 positive witnesses, one final equation and inherited exact
degree2,304,000. The physical/simulation and number-theoretic dependencies
have the scopes recorded in the [ant intake](review_periodic_ant40_48_intake.md).

## Replay and limits

The [bounded helper](ant48_rotated_occurrence_cleanup.py) uses explicit
exceptions and exact receipt text comparison under normal and optimized
Python. From any working directory:

    python3 /absolute/path/ant48_rotated_occurrence_cleanup.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/ant48_rotated_occurrence_cleanup.json

Use `--output NEW_FILE` to create a new receipt. No archived Python, old
builder, full occurrence compiler, ant simulation or enormous coefficient
integer is executed or materialized. This exact local simplification does
not establish optimality or a new universal-polynomial operation record.
