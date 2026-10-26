# Joint Pell certificates and coefficient sharing for ZFC consistency

Research iteration 23 for Vladimir Reshetnikov and ProveIt, 26 October 2026 UTC.
Start with the native TeX/PDF research article in `report/`.

## Extract every ZIP part

Extract ALL numbered `ConZFC_Joint_Pell_Certificates_Round23_2026-10-26_part*.zip`
archives into the same parent directory. They have disjoint entries under one
common release folder; no part alone is complete. Each ZIP is at most 4,000,000
bytes. `PARTS.json` lists every part and its files. No further source download
is needed for the declared verification plan.

## Main constructions

The four direct equations are quartics in unrestricted integers:

| Endpoint | Variables | Residual squares | Collected terms | Coefficient height |
|---|---:|---:|---:|---:|
| Dimension | 209 | 149 | 5,278 | 70,368,744,177,664 |
| Principal | 210 | 150 | 5,276 | 16,777,216 |
| Balanced | 211 | 151 | 5,401 | 65,537 |
| Low-height | 212 | 152 | 18,381 | 5,200 |

The principal improves the incoming 210-variable polynomial's support and
height at unchanged dimension and degree. The balanced point improves all
three displayed size measures over the incoming 214/5699/91679 companion.
The 209-variable point pays a higher coefficient height for fewer variables.
The 212-variable point does NOT dominate the earlier height-4096 or height-2304
constructions. These are explicit tradeoffs, not a global minimum.

The reciprocal and exact projection branch supplies unrestricted-integer
polynomials with pairs (variables, degree) of (138,8), (114,16), and (113,16).
Their full collected coefficient counts are 12,099, 127,818 and 1,030,202,
respectively. The latter two have exact expanded height
16,250,018,885,420,533,678,080. The 138-variable height is
1,125,899,906,842,624. The million-term equation is supplied as a complete
ordered coefficient collection, not merely an unspecified expansion.
The new joint theorem's matched control and the separately optimized sparse
alternative are distinguished explicitly in the report.

The coefficient-height-one branch supplies 15 quartics, all with constant one
and nonzero coefficients only +1 or -1. The minimum selected dimension is
484, with 24,131 terms. Examples include 489/17,729, 493/17,058, 531/12,020,
533/11,985, 599/8,279, 695/7,135 and 696/7,113 (variables/terms).
Each of the nine previous Round22 selected points has a strictly dominating
new point. All complete literal arrays and their source pullbacks are included.

The two new TEN-STRICTLY-POSITIVE-INTEGER polynomials have exact degree/operation
pairs 202/99 and 190/120. These lower the degree at additional arithmetic cost;
they are not ten-unrestricted-integer claims. Both retain the coherent whole
Start-only4127 four-coefficient tuple, totaling 97,046 raw bytes. Exact leading
forms prove the claimed degrees after substitution of the actual fixed tuple.
No new unrestricted-integer eleven-variable result is claimed in this round.

## Reproduce

With Python 3.10 or later and the standard library:

    python3 -B verify_release.py

For the complete inventory only:

    python3 -B verify_release.py --integrity-only

The default executes every step of `VERIFY_PLAN.json` in a disposable copy,
including full deterministic height-one rebuilds. It checks source bindings,
exact identities and coefficients, inverse maps, graph liveness, deliberately
corrupted controls, source reconstruction, native coefficient decoding and
normal/optimized Python. Keep optional output receipts outside this sealed
folder, for example `--output ../round23-replay.json`.

The research-release audit may reuse the completed full isolated height-one
normal/optimized replay through an exact file-hash binding. Such reuse is
explicit in its receipt and is not described as a fresh rerun on the later
sealed extraction. All other final extraction checks are recorded separately.
The user's default verifier does not take this audit shortcut.

## Proof and verification boundary

The ordinary unbounded arguments, composed with the identified inherited
C222/ZF/ZFC or native/refutation calibration, prove within ZFC that absence
of zeros in each stated domain is equivalent to syntactic Con(ZFC). They
neither assume nor prove consistency and do not restrict proof codes to
externally standard integers. Finite replay authenticates the supplied
artifacts; it is not a replacement for those ordinary unbounded proofs.

There is no newly compiled end-to-end Lean/Rocq certificate, external human
peer review, global simplicity lower bound or claim of historical priority.
See `CLOSURE_MAP.md` for retained source interfaces, exact historical relocation
and the distinction between selected dependencies and comparison-only metadata.
