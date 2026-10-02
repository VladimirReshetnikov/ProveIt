# Paid copy-selector prefixes give395 universal operations

The [literal source](tseytin_copy_prefix395.py) saves four multiplications
in the [399-operation compiler](tseytin_adjacent_coefficients399.md),
giving **395=182M+213A**,381 certificate operations, five comparisons,
62 positive witnesses, one fixed positive program parameter, ordinary
positive input and degree at most4712. The separate-power form costs397
and has degree bound4752. The [receipt](tseytin_copy_prefix395.json)
contains all four complete product/SOS schedules.

The whole polynomial and supplied coordinates are identical to the parent
on every integer assignment. This is an arithmetic rewrite of the current
fixed C2 encoding. No letter or delimiter code, native field, endpoint,
query loader or program recipe changes. Universality transfers from the
complete parent, with its same valid program slices. The overall75/87
record is unchanged; no global arithmetic optimality is claimed.

## 1. The existing prefixes compute the weighted copy sum

Let h_i denote the supplied selector hat `Shat_i`,0<=i<6. These are the
six copy tiles, with offsets1,...,6 in the fixed encoding. Both affine
updates use the already shared weighted expression

    W=h_0+2h_1+3h_2+4h_3+5h_4+6h_5.

The parent computes it using five fixed-numeral multiplications and five
accumulator additions. Independently, its selector checksum already pays
the five prefixes

    selector_sum__4=h_0+h_1,
    selector_sum__5=h_0+h_1+h_2,
    ...,
    selector_sum__8=h_0+h_1+...+h_5.

Therefore the exact integer identity

    W=6*selector_sum__8−selector_sum__7−selector_sum__6
       −selector_sum__5−selector_sum__4−h_0             (1)

uses only one multiplication and five subtractions. Each h_i has
coefficient6 minus the number of subtracted prefixes containing it,
namely6−(5−i)=i+1. The proof does not assume Boolean selectors, positive
coordinates, a checksum equation or a particular scale.

The source changes `linear0_coefficient__50` from6h_5 to the single
paid product6*selector_sum__8. It reuses the five accumulator names
`linear_sum__380` through `linear_sum__384` for the five successive
subtractions in(1). It deletes exactly the four now-private products

    linear0_coefficient__46=2h_1,
    linear0_coefficient__47=3h_2,
    linear0_coefficient__48=4h_3,
    linear0_coefficient__49=5h_4.

Thus **four multiplications disappear**, while the number of additions
and subtractions combined is unchanged. Multiplication by6 remains
charged. No arithmetic instruction is hidden in a supplied coordinate
or a precomputed variable coefficient.

## 2. Privacy and complete polynomial identity

In the canonical parent, each of the five coefficient registers is read
only by its own weighted-sum addition. Each of the first four accumulator
registers is read only by the next addition. None is an active interface,
comparison, supplied coordinate or native factor. The rewrite checks these
exact consumer sets and all15 literal prefix/coefficient/accumulator rows.
It accepts only the entire canonical399 parent, so a caller exposing
one of these private values is rejected.

The final weighted-sum register `linear_sum__384` has exactly the same
value by(1). Every subsequent register therefore has the same value,
including both affine updates, chronological transports, packed words,
all12 native/exponent factors, the query residual and every finalizer.
Only the reused coefficient register and the first four accumulators
change their intermediate meanings. `restore_registers` gives the exact
old private values, including the four erased products, as diagnostic
polynomials in the six supplied hats. It adds no witness or source gate.

All positive domains and every supplied parameter and witness are
unchanged. The complete zero set, including its positive part, is
identical under the identity map on coordinates. This statement holds
even at invalid program coefficients; the interpretation as a universal
ordinary-input relation retains the parent's valid program recipe.

The already paid prefixes are independent of the update coefficients.
A topological sort places the shared product before the subtraction
chain, and the checker verifies declaration order and complete output
liveness. There is no cycle or deleted external consumer.

## 3. Counts, degree and reproducibility

| Form | Certificate | Comparisons | Witnesses | Polynomial | M | A | Degree bound |
|---|---:|---:|---:|---:|---:|---:|---:|
|Merged product|381|5|62|395|182|213|4712|
|Separate product|380|6|62|397|182|215|4752|
|Merged SOS|381|5|62|395|182|213|9396|
|Separate SOS|380|6|62|397|182|215|9288|

Every changed register is a nonzero degree-one linear form in the
supplied selectors. The final weighted form is the same polynomial.
The complete retained degree dictionary is unchanged; both actual
main-norm cancellation graphs and the factored native index are untouched.
The same conservative universal degree bounds therefore apply to all
four schedules. Exact expanded degree is not claimed.

`build(merge_units=True)` emits the default. `rewrite(old)` requires
the full canonical parent. The polynomial, degree and ledger APIs require
the full canonical successor. Historical parent records preserve their
old private meanings; all active interfaces are unchanged.

Run `python tseytin_copy_prefix395.py` to recompute and compare the
receipt; `--write` regenerates it. The checker expands(1) into the exact
coefficient vector[1,2,3,4,5,6]. It checks192 complete retained-register
and manual private-restoration maps (96 signed),384 whole-polynomial
identities (192 signed),12 zero-selector contexts, all four complete
operation/degree/liveness ledgers and44 rejected mutated callers.
These arbitrary-integer fixtures supplement the polynomial proof;
they are not materialized giant Pell zeros.

Author generation and a separate fresh default replay pass. All three
local links and the trio's whitespace check pass. Root independently
reviewed the full proof and source and replayed the receipt, with no
findings. Its separate interpreter checked256 complete parent and manual-
finalizer output identities(128 signed), including basis-vector selectors,
all four opcode/output-closure ledgers and both retained degree dictionaries.
