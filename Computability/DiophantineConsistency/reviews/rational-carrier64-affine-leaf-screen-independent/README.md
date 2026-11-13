# Independent review: bounded affine rational-leaf screen

**PASS for the explicitly bounded finite screen.** The screen uses the
pinned 64-row graph and four integer source ports from the
`one-page-reversed-carrier65-2521` coefficient package, not the maintained
current14 port values. We independently rehashed compressed and raw port
bytes, parsed them as big-endian integers, verified the three moduli are
prime and beta is invertible in each, and checked the modular values of
`Urank=MF/beta` and `Wrank=MC−MF`. The source DAG is topological, all 64
rows are live, and reserved fresh-node names do not collide.

The checked family substitutes one target intermediate row by a fixed leaf,
an earlier-node alias, `x+c`, `c−x`, `c*x`, `c*x+y` or `c*x−y`, with x,y
chosen among earlier values. It tests equality with that intermediate row at
four samples for each prime, then counts reachable graph rows after removing
dead nodes. It does not enumerate arbitrary replacements that agree only at
the final output. The new c is a fifth fixed runtime leaf, independent of
witnesses, with unconstrained bit size and free construction/storage; the
four existing leaves and literals 0–4 are also free. Its residues are
inferred separately in each field. The screen's conclusion applies only to
rational coefficients with well-defined reductions at all selected primes;
a denominator divisible by one is outside the stated exclusion.

Independent combinatorial checks confirm 64 targets, 64 fixed-leaf and
3,488 alias queries, 10,400 one-gate and 416,896 two-gate queries, assuming
the receipt's verified zero-scale conditions. The 124 pre-liveness survivor
count concerns only affine-gate forms, not alias/fixed-leaf matches. No
recorded candidate has fewer than 64 live rows. The positive control really
has `(x+1+2)*y=(x+3)*y` and the reported liveness reduction from three to
two. The updated author screen reran with observed exit 0 and byte-identical
stdout; the retained outer observation records session 67386 exit 0, which
this review did not directly witness. Independent [check.py](check.py)
reproduces these checks and the screen; [result.json](result.json) is its
exit-0 output. No Lean was run.

This is finite modular evidence only. It does not prove any nontrivial
characteristic-zero identity, a general operation lower bound, or a result
for fixed current14 ports. It excludes neither coordinated multi-row changes,
nonlinear or differently structured replacements, multiple extra constants,
changed witnesses nor equivalence only at zeros. Sampling can leave false
positive matches; none was promoted to an exact candidate here.

Frozen author screen SHA-256
`4a11bfec6db2a1cee0d87f71c02fe7cd04f27385001e906cf84616c05201f2fe`,
result `edd8cbe67b46296ee9b9ae91fd5bbab95a5f09810e5e3dd10ef195d591198638`,
outer observation `05ed6feb7b30c05634538a285b0722cbd5d2064944aea42bcbd8ddfbe82577b9`.
Independent checker SHA-256
`4dcdda3eda6bb58b2970a0bc2393e48c5594c34999e07227d60dce90f39b33a2`;
result SHA-256
`26211f45b5a2b5928836005540cd44b67782d66a484c0832a003a463c5a87b4a`.
