# Internal Pell classification: independent peer review

26 October 2026. **PASS; no finding or source correction requested.** I read
all final main/Checks sources, the author receipt, proposal, preparation
inventory and exact executed driver before replay. I also read the complete
accepted ArithmeticPellRecurrence source, Foundation HFS.PRF construction,
and the actual Sigma1 order-induction contract in Schemata. I authored
neither of these two new Pell leaves. My earlier work on other Pell clients
and cache authentication is disclosed; the recurrence's independent review
was performed by a different agent and is retained with this evidence.

The target is exactly the natural arithmetic norm
x*x=1+(b+1)*(b+3)*y*y with base b+2 in every IΣ1 model. The source does not
silently replace an internal element by an ordinary Nat or assume a
classification witness. `positive_x` follows from norm positivity;
`x_bound` proves the polynomial cap needed for the later bounded universal.

For y>0, the proof establishes d*y<(b+2)*x and x<=(b+2)*y before defining
the natural differences u and v. The inequality (b+1)*y<x then gives v<y.
Both exact inverse recurrence equations follow by adding and cancelling
nonnegative expressions. The polynomial identity a*a=d+1 justifies those
cancellations without treating natural subtraction as signed subtraction.
The reverse norm-step lemma likewise cancels a common sum; it assumes no
converse Pell theorem. The resulting smaller solution is genuine and has
positive first coordinate.

The induction invariant universally quantifies x only up to
(b+2)*y+1. Its antecedent norm is polynomial and its conclusion uses the
accepted represented coordinate graphs, so the actual definability
obligation is Sigma1. The proof calls Foundation's Sigma1 order induction,
not unrestricted induction on model elements. At y=0 the norm/positivity
and bound force x=1 and index0. At positive y the index from the smaller
ordinate is advanced once, and its new bound follows from time<=v<y.
`norm_iff_index` proves the reverse direction directly from the accepted
recurrence norm. No uniqueness, cofinality, carrier congruence or arbitrary
discriminant classification is claimed.

Checks retain arbitrary b,x,y in the model, expose every descent field,
cover the zero-ordinate case and audit all six public endpoints. The imports
contain no external Pell classification or standard-Nat solution oracle.
The current result is an all-model arithmetic theorem; it is not presented
as a new object-language HA derivation or the final equation equivalence.

I independently reconstructed the selected import DAG, including Init and
meta imports, and reauthenticated the entire previous plan plus the
accepted recurrence source/object. The exact scope is96 cached modules,
95 Foundation,381 artifacts,38 explicit package boundaries and114 boundary
companions. All33 author-manifest files were checked, including the two
failed development attempts; failed source snapshots were not used as
final inputs. The peer evidence contains687 distinct pinned paths, checked
before and after the commands. Historical package/provider qualifications
remain inherited; no dependency or Foundation module was rebuilt.

Fresh private provider:
`/tmp/arithmetic-pell-classification-peer-ugrz4njr/lib`.
Both invocations used the pinned Lean4.32 binary, original absolute source
paths, `-M6000 -j1 -DElab.async=false`, one thread, an isolated LEAN_PATH,
and fresh regular nonsymlink outputs. Main passed in8.838s, peak
1,837,212KiB RSS; Checks in2.125s, peak1,786,412KiB RSS. Main diagnostics
are empty. All six axiom reports match the author exactly and use only
propext, Classical.choice and Quot.sound. Both objects are byte-identical.
There were no peer compiler/preflight failures. Final free space was
1,785,954,304 bytes, above the512MiB guard. No source or shared object was
modified and no Git operation was performed.

Source pins:

- Main `93cb97fababdd4a1aac7766e5be1d35b3af69b52e4a7ac23726f2c6c42ec8f73`.
- Checks `398daaff4b69ea0902cd89f0d63143e21dc4db945be717c6d8cf919795b203c5`.

Object pins:

- Main `29fc853c66cbea0cd892ad5a38fb1c708388b80c2a448965fef25822c10ffb5e`.
- Checks `558399a4ff004d67bd9c492e0a2996abd5fe548ee46bf3c9eb80980862118179`.

Author summary `f2931133005fcba1a929c6202a295b13216fea76420aaac6a6e4a663d645ee90`.
[Independent replay](arithmetic-pell-classification-peer-replay.json)
`6794e6e051a46a6bfa737b164ed78cb029789a8438bdb428ef9ca148a440b31f`.
[Thirteen-file evidence manifest](arithmetic-pell-classification-peer-replay/FILES.json)
`1e3c68df8eeec1a2b2af1ee71b18f5954f58d70e24462cb1f60db3c99541d19d`.
The bundle preserves the exact executed peer driver, inputs, author packet,
cache plan, source snapshots, commands, logs, timings and terminal state.
