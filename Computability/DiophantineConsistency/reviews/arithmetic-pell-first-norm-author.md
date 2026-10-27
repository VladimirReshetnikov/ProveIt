# Actual internal first norm: author record

27 October 2026. ROOT authored this240-line main and38-line Checks.
Independent mathematical challenge is clean; independent fresh replay is
pending. All final proof text, Checks, planner and executed driver were read
before compilation. Only accepted ArithmeticPellCongruences is imported.

This addresses the actual first norm x²=1+Q(Q+1)k² used in
NativePellBootstrap.source_first_classification. With Q=q+1, a=2q+3,
d=(q+1)(q+2), descent uses the concrete unit(a,2). The proof first excludes
k=1 by consecutive-square bounds. Hence k>=2, which gives2x<=ak;
the norm gives2dk<ax and(q+1)k<x. Both natural subtractions defining
u=ax-2dk and v=ak-2x are justified. The inverse identities and norm
preservation give u>0,v<k and the same norm at(u,v).

A genuine bounded-universal Sigma1 order induction then classifies every
internal solution by time<=k in the represented sequence at parameter2q+1,
with x=xcoord(time) and k=2*ycoord(time). Both directions, actual evenness,
positive index for k>0, and the arbitrary positive Q wrapper are proved.
The latter uses Q-1 only after proving1<=Q. Classification plus the actual
recurrence residue quotients yields x=1+2Q*r and k=2*time+4Q*s.
No external fundamental-unit/parity oracle or standard-natural index is used.
Checks cover the zero ordinate, impossible ordinate1, arbitrary positive Q,
actual evenness and simultaneous index/residue witnesses.

The exact reused closure is98 custom modules,95 Foundation,383 artifacts,
38 boundaries with114 companions, zero prerequisite refresh. The cache plan
SHA256 is `36f362df517bfdd4d3ba06176005ce2d85e7b2591700b18a67a85fc69f009c66`.
The driver checks648 inherited pins, every selected source header, exact
reachable DAG and497 actual first artifact providers. The durable freeze
separately authenticates3,287 observations across1,430 distinct paths.

There are two retained attempts. The first main fails on four API/inference
details: ambiguous lt_irrefl, an opaque local base in simp, and two addition
order mismatches. The correction qualifies the lemma, unfolds the local base,
and gives explicit commutativity-compatible inequalities; all mathematical
statements, source imports and caps remain unchanged. The second fresh pair
passes cleanly in10.868s/2.050s. The main log is empty and all eleven reports
use only propext, Classical.choice and Quot.sound. Both runs use pinned
Lean4.32, -M6000 -j1 -DElab.async=false, one thread, private explicit
LEAN_PATH, fresh regular outputs and the512MiB reserve. No prerequisite
or Foundation compiler runs.

| Module | Source SHA256 | Object SHA256 |
|---|---|---|
| ArithmeticPellFirstNorm | 92a06ab9e3439136fd7c14639e6314093e16a6027f5995834abbb7573eedd011 | b2fb2b6e30c5ad6883c5daa6c06a76b91375a6e4e7a4c82afffe00be3bcb23d8 |
| ArithmeticPellFirstNormChecks | a929efefd0979ee66b6fcc3e0f0521c95aaae54bd39fbf1dd32701995054d2ed | 2bca2fd12cf766f92c58f02d2782512d2bc75d477628ddb4dbd6c8a612339a94 |

Final private provider: `/tmp/arithmetic-pell-first-norm-author-wgmv68ny/lib`.
The [author packet](arithmetic-pell-first-norm-replay.json) has SHA256
`6021f74a093d33437e5090de9b7f109aa10625ff05307f38c3f63bb4f68122f1`;
the29-file [manifest](arithmetic-pell-first-norm-author-replay/FILES.json)
has SHA256 `550490a12ec108970af9d45e44bfb73e1c02e1c59a2a567090813cd7faa9c8f5`.
Both attempts retain complete sources, commands, logs, timings, providers,
drivers and metadata. This does not identify time with(R+1)/2, construct
all simultaneous carrier witnesses or prove the equation's PA/HA theorem.
