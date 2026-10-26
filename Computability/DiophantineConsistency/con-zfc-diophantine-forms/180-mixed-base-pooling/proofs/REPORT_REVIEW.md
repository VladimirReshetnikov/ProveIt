# Independent review of the final report

Date: 25 October 2026. Review performed by a separately assigned
AI-assisted mathematical reviewer. This is not outside human refereeing.

## Scope and conclusion

Reviewed `report/report.tex`, the generated results, request and pivot
tables, and the corresponding standalone TeX presentation. The new
unweighted reciprocal-pooling theorem and its application to the
authenticated 216-coordinate source are mathematically sound under the
explicit inherited canonical-Pell and height interface. No unresolved
error was found in the new theorem, its zero/unit/signed-base cases, or
its integral recovery of singleton and aggregate witnesses.

The first integrality step alone would be insufficient for mixed signs.
The report correctly retains the second step: multiply the rational
leading sum by the product of the nonzero bases; bound the correction
strictly below one; then use the common sign of its summands. The budget
`(s+1)b+ceil((s+1)/2)+1 <= W` follows from the displayed bound and gives
the stated uniform `s<=14,r<=64` corollary. The actual five-block,
seventeen-request case satisfies it. The signed Pell congruence uses an
invertible integer matrix and needs no unstated sign or parity premise.

Zero-base terms have modulus -1 and are integral before they are removed
from the proof. Recovering the old witnesses before invoking the old
bootstrap avoids a circular nonzero-base argument. Negative indices at
unit bases are permitted; the nonnegative-index conclusion is restricted
correctly to nonunit bases.

## Polynomial specification

The report supplies every source residual, the exact deleted row and
coordinate lists, all seventeen request ports and affine offsets, the
actual block-index partition for each endpoint, and complete monic-pivot
lists. The recursive acyclic substitution rule therefore specifies a
fixed integer polynomial without an unspecified Diophantine compiler.
The main 207-coordinate polynomial has exact degree 22 because the new
private quotient has coefficient equal to minus a degree-ten product of
moduli. Its sum-of-squares leading term cannot disappear.

The smaller endpoints use the stated exact monic-elimination lemma. The
general elimination method is correctly attributed to the earlier work;
its new use here is a measured composition with the pooling theorem.
Their finite circuit and projection certificates are covered by the
separate projection audit, not by an assertion that this prose review
has re-expanded all final polynomials.

Two presentation issues identified during review were corrected: the
intermediate `m-X+AY` is now denoted by Delta rather than overloading the
request table's `D=X-AY`; and the uniform-count sentence explicitly
concerns the two budget inequalities, not all theorem hypotheses.

## Attribution and calibration boundary

The text credits package 158 for same-base pooling, package 168 for the
consecutive-base reciprocal predecessor and proposed orientation idea,
package 172 for the literal source and inherited calibration, and package
152 for generic elimination. It makes no literature-wide priority claim.

The local matched comparison is appropriate: the same 95 core pivots plus
three ordinary modulus eliminations and two monic K eliminations give
the 116-coordinate control, against 112 coordinates at the same degree
24 after fusion. Thus four coordinates, rather than all of the larger
historical improvement, are attributed to the new cross-base argument.
The 143-coordinate octic is explicitly described as a generic-elimination
companion that does not require the new cross-base theorem.

The report states the ordinary source-calibration dependency and names
its finite-refutation interfaces. Those source and proof files are
retained. It distinguishes formalizability in ZFC from a new Lean/Rocq
kernel check and does not claim to have proved either Con(ZFC) or the
absence of integer zeros. This review validates the new transformation
and its stated composition boundary; it is not a new proof-assistant
verification of the inherited source calibration.

The coefficient-height discussion also distinguishes literal circuit
integers from expanded coefficients. The acknowledged worsening of the
degree-64 height bound prevents an unsupported Pareto-dominance claim.

## Verification associated with this review

`verify_independent.py` independently checks the four raw pooling
artifacts coefficient by coefficient at each circuit residual, verifies
the abstract final sum of squares, authenticates the source/frame and
private-row interface, and checks exact degrees and actual variable
dependence. Both ordinary and optimized Python runs passed.

`check_theorem.py` passes 246 exact cases covering signed parameters,
zero and unit bases, negative indices, repeated/noncoprime moduli,
corrupted outputs and witness recovery. Its small-height negative control
now computes the literal report example: A=10, moduli 18 and -22,
numerators 9 and 11, reciprocal sum zero, and both divisibilities false.
These finite checks support implementation review and do not replace the
unbounded theorem or the inherited calibration.
