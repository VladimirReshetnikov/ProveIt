# Later Library supplement: corrected comparison and attempted synthesis

This review concerns a **Library supplement**, not the main repository snapshot. The restored archive has SHA-256 `7c21ff5d05ef52c754399a6e62f37ac7622baa6e82a702d855bfb68d82fc1a4a`, Library ID `libfile_299513832b988191a5114e109ffe62dd`, and extraction directory `con_zfc_pell_congruences_2026-10-23`. Its transport proof cites the older repository source snapshot `cf4a5218a5a4e4358d3f5314151b6b05d4aa384e`; this must not be confused with the current main review pin.

## What was inspected and checked

Read the complete transport/PROOF.md, the CRT and centering sections of report/report.tex, certificates/INDEPENDENT_MATHEMATICAL_REVIEW.md, the four literal transport JSON packets, and the preliminary strong-rank stage of the inherited residue-orientation proof. No upstream Python was executed.

The newly authored check_library.py parses only arithmetic JSON expressions as inert AST data. It authenticates the actual six coefficient bytes from the frozen round12 low-degree binding, verifies their residues equal the supplement's claimed fixed ports, specializes each unknown to its supplied integer slope times one indeterminate, and computes the resulting polynomial coefficients by exact convolution modulo1000000007. It checks the supplied nonzero top coefficients directly, not by random samples. All four checks pass:

- 20 integers, degree20,8 rows;
- 19 integers, degree28,7 rows;
- 18 integers, degree32,6 rows;
- 17 integers, degree88,5 rows.

This is exact coefficient replay, not a replacement for the symbolic upper bounds or the unbounded equivalence proof. The inspected formulas and mathematical proof account for those upper bounds and the witness transformations. Complete literal hashes and computed degrees are in LIBRARY_CHECK.json.

## Corrected comparison

Against this supplement, the frozen round12 points20/20,19/32,18/88 are **not new frontier improvements**. The first repeats a metric pair, and the latter two are dominated. They may be retained as simpler alternative derivations without a CRT dependency, but must not be advertised as beating all available prior work.

The round12 **21-integer degree16** point remains distinct and useful. The Library supplement does not list a point that dominates it. Its proof uses only polynomial restorations plus a reversible auxiliary-norm row operation after the existing parent, whereas the CRT family additionally invokes a preliminary Pell rank lemma to establish its arithmetic inverse.

## Why the CRT ordering is sound

The preliminary signed argument gives |c|=psi_b(p), |f|=chi_b(m), and p divides m, before auxiliary rank recovery or either quotient is used. The Pell identity and divisibility sequence imply c² divides f²-1, hence f is its own inverse modulo c. Therefore

V=-c mod f and V=-R mod c

are parametrized exactly by

V=fcT-f²R-c.

The reverse restores o=cT-fR and j=(V+R)/c; the latter is an integer by the proved square congruence. This is not the incorrect stronger subprogression f²(cT-R)-c, and it does not presuppose the later conclusion p=R. The read preliminary source theorem matches the asserted dependency order. This review does not independently reprove every inherited Pell theorem.

## Centered auxiliary-norm combination

The supplement's20/20 rank-register chart has a=E+Y, Y=(2v+1)q³, R as a retained coordinate, k=R+1+hE, I=(2r+1)c², and V=fcT-f²R-c. Its centered auxiliary row is

A=V²+(1-I²)y(2V+y)-1.

Retain a as an additional coordinate and retain the scale row a-E-Y=0. Replace A by

Ared=V²+[1-Delta(f²-1)]y(2V+y)-1.

The exact difference is Ared-A=S*y(2V+y), where S=I²-Delta(f²-1). Thus keeping S=0 proves reversibility. Here V has degree3, Delta(f²-1) degree4, and Ared degree8. Other rows stay within degree8. This constructs another21-variable degree16 chart, but **does not improve the frozen21/16 metric**. It also inherits the CRT dependency, so it is not promoted as a simpler replacement.

Without the retained a, Delta has degree8 and Ared rises to degree12, worsening degree20 to24. Without the retained rank register, V has degree7 and V² alone has degree14, retaining the degree28 obstruction. These explicit degree calculations explain why straightforward composition of the newly centered norm with the Library CRT chart does not yet improve its19/28 or18/32 points.

No better completed metric was obtained from this supplementary pass. The frozen originals were left unchanged; this addendum supersedes only their comparison against the earlier available sources.
