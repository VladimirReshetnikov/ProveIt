# ROOT-authored internal squared-ordinate seed

Author pair passed on 27 October 2026. Independent peer source review and
fresh replay remain required before promoting this as independently accepted.

For c=ycoord(R,a), the new theorem proves c² divides ycoord(R*c,a) and
constructs positive f,i with f²=1+delta(a)*(i*c²)² when R>0. The index is
explicit, R*c; no arbitrary-modulus Pell divisibility witness, standardness,
finite pigeonhole or cofinal seed is supplied. Genuine Sigma1 induction
gives even-block natural quotient witnesses; one addition and the norm
give the odd-block identity; internal parity of c supplies divisibility.
The structural divisibility theorem also retains R=0. The remaining outer
and auxiliary simultaneous witnesses are not proved here.

## Source and object pins

- Main, 105 lines:
  `c12b5f7c746ee1df1d111814b10db039049992f6b8d2cc3b8f8857cfd95510d8`.
- Checks, 30 lines:
  `d85e05e4a73068fc22283c91bcada322c872e229512aee9f7954b159acb40fd2`.
- Main object:
  `76f5a3d2fe6f118be216894486ee08f4831e8e47aa17286202020e3e8d46c2d4`.
- Checks object:
  `4f33b310f3f84793ab637096efdf55f69b596137cf694ef75cfc6b20e0a8f12c`.

The accepted author provider is
`/tmp/arithmetic-pell-squared-seed-author-xir_6cvz/lib`.
Main/Checks pass in 7.282/1.917 seconds, with silent main, no warnings,
and four reports using only propext, Classical.choice and Quot.sound.

The sole import is ArithmeticPellPeriodicity. The read-only audited scope
is 99 cached modules, 95 Foundation, 384 custom artifacts and 38 external
boundaries with 114 artifacts: 498 actual first providers, zero refresh.
Source headers, exact reachable imports, all providers and compiler pins
were checked around the capped fresh builds. All commands used
`-M6000 -j1 -DElab.async=false`, one Lean thread and reserve guards.
Both inputs were read and snapshotted before each first command.

Two attempts remain preserved. The first has one final normalization error
in strong_seed: simplification did not unfold the local c abbreviation.
The second makes that equality explicit before rewriting the proved norm;
there are no statement, import, mathematical-scope or cap changes.

The [author packet](arithmetic-pell-squared-seed-replay.json) has SHA256
`7c0e54bd7a003d21fe54dc66216e025e549e410e90547ab1f33e48ad69618f40`.
The [25-file evidence manifest](arithmetic-pell-squared-seed-author-replay/FILES.json)
has SHA256 `a72448ab814f6eeb1fc06cb8dece3771311e1ab0628da40bf336203b89ddf1eb`.
The freeze rechecked 5,809 comparisons over 2,291 paths, authenticating
historical working-source pins against the corresponding input snapshots.
Immutable terminal metadata uses regular hardlinks; fresh proof objects
are separate compiler outputs. The outer packet and this receipt are
separately pinned outside the manifest to avoid cyclic hashes.
