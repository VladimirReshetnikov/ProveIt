# The degree-1,158,228 equation in1,065 operations

This nine-positive circuit is **the same polynomial** as the arriving
radical-majorant equation, evaluated in **1,065 live binary operations**
instead of1,753. It saves688 operations (39.2%) and retains the exact degree
**1,158,228**, all nine inputs, and the complete original31 coefficient tuple.
It is a lower-degree alternative to the440-operation degree1,845,940 form
and the475-operation degree1,379,730 form. No global optimum is asserted.

## Reuse the existing quadratic register

The parent already computes

```
D=(A²-1)C²+1,       hence A²C²=D+C²-1.
```

Its radical majorant is a654-term integer polynomial in `A,C,i,Z`.
Repeatedly replace `A²C²` by `D+C²-1` in those monomials. Every replacement
lowers the A exponent, so this finite calculation terminates. After
collecting coefficients it has **312 terms** in `A,C,D,i,Z`, at most
linear in A. Evaluate the collected polynomial by shared Horner steps in
the fixed order `Z,i,C,D,A`. The full equation then needs1,068 operations.
The three shared-product/rank simplifications described in
[`gap2082-shared-products`](../gap2082-shared-products/README.md)
reduce it to1,065.

D is a polynomial abbreviation already present in the parent circuit;
it is not an additional unknown or a new constraint. The replacement
preserves the exact majorant value, rather than choosing a different
bound. All polynomial exponents remain fixed natural numbers, and the
literal DAG contains only binary addition, subtraction and multiplication.
Squares and multiplication by a fixed numeral are charged; integer leaves
and register reuse are free. All nodes and all inputs are live.

## Exact identity and mathematical scope

The independent check first verifies the parent's literal D relation as a
free integer-polynomial identity in A,C. It then expands the **actual new
DAG** at the five earlier registers A,C,D,i,Z and substitutes that D
polynomial. The result equals the actual parent DAG's654-term majorant
exactly, coefficient by coefficient. This check imports neither the
reduction table nor the Horner generator as an identity assumption.

Every other retained gate has the original operation and corresponding
operands, up to ordering commutative operands. Every new node must be
covered by this remap or the local polynomial calculation. Induction over
the original circuit proves equality of the complete output. The second
receipt checks the three further savings independently by four local ring
identities and another complete remap. Consequently the final circuit has
exactly the parent's polynomial and positive zero set.

The arriving ordinary proof and exact-degree argument are retained as
[`source/PARENT_PROOF.md`](source/PARENT_PROOF.md). Its654-term majorant
and positive-coefficient defect certificates justify the uniform strict
root bound; that unbounded argument is inherited without alteration.
The complete parent release replay, in normal and optimized Python, passed
all eight stages per mode and reproduced all170 archive members byte for
byte. See [the nine-variable review](../../PROPOSAL_REVIEW_WAVE11_NINE.md).
This is not an end-to-end Lean or encoded internal-ZFC proof.

All fixed leaves are reconstructed from the authenticated whole original31
ports at
[`31-sun10/coefficients`](../../con-zfc-diophantine-forms/31-sun10/coefficients/README.md).
The recipes and source/layout hashes are unchanged. Sixty assignments over
three primes compare the output and retained named values with the actual
fixed integers. These are diagnostics in addition to the exact identities.
Changing the new majorant's final multiplication to addition is rejected
by the identity check without changing its number of gates.

An independent SymPy integer-polynomial audit also verified both stages,
the original arrival bytes, full topology and liveness. Its receipt is
[`radical-d-peer-review.json`](../../reviews/radical-d-peer-review.json).

## Provenance and replay

The parent JSON, full radical table, original proof and notices are copied
as inert data from `con-zfc-radical-guard-descent-2026-10-23.zip`, arriving
at `c1a102936aca437e9999530a0111e6ddab56dc6d`.
Archive SHA256:
`ccb67b2ddaf49287079d9f4758915c8866db12008eb656ecaf6c34b81a5ef084`.
The parent/table SHA256 values are hard-coded in the generator and recorded
in `REVIEW.json`. They match the original ZIP members, including after
the parent release replay. Historical relative references in the copied
proof/notice refer to that archive; its source71 prefix proof is also in
the repository's package71.

From the repository root:

```
python3 Computability/DiophantineConsistency/tools/build_radical_d_shared.py --check
python3 -O Computability/DiophantineConsistency/tools/build_radical_d_shared.py --check
```

The standard library suffices. Without `--check`, the tool regenerates the
seven JSON artifacts; `MANIFEST.json` records their deterministic bytes.
No compiler or Lean process is invoked.
