# Generalized auxiliary Pell seed with an extra multiplier

[`ModelBAuxiliary.lean`](ModelBAuxiliary.lean) is an exploratory model-level
result, not a 69-operation converse, compact coefficient calibration, or
object-level iPRA derivation. In an arbitrary `IΣ₁` model, for `b>0` and
`R%4=3`, write `c=ycoord R a`. The theorem constructs positive model elements
`f,i,T,u,y` and sets `I=delta a*(b*i*c*c)` such that

```
f*f = 1 + delta a*(b*i*c*c)*(b*i*c*c)
y = ycoord R (I-2)
xcoord R (I-2) = I*u
(u+c)%(f*f) = 0     (u+R)%c = 0
f*f*c*T = u+c+f*f*R
I*I*u*u+y*y = 1+I*I*y*y.
```

It also fixes `u` to the odd-index quotient and proves the corresponding
absolute-difference equality. Its proof combines the independently reviewed
[strong seed with multiplier](../thirteen-model-strong-seed/README.md) with
existing arbitrary-model phase, quotient-residue, and positive-quotient
lemmas. The selected positive `y` is the magnitude of the negative signed
ordinate that the eventual thirteen-coordinate construction intends to use;
the theorem here does not yet prove its sign congruence or construct the
positive literal carrier coordinate `m`. Graph expression transport,
phase-split2471 full-port calibration, and the internal iPRA theorem remain
separate obligations.

## Exploratory compilation

Session 85924 observed overall exit 0 for a shell `&&` chain that compiled
`ArithmeticPellSquaredSeed`, `ArithmeticPellAuxiliarySeed`, and then this
source, in that order, against one coherent author parent plus the locally
compiled strong-seed dependency. The final theorem printed
`[propext, Classical.choice, Quot.sound]`, without warnings or `sorryAx`.
The chain's observed success implies each command in it returned zero, but
its individual child exits were not separately recorded. A subsequent paired
replay and its [independent artifact audit](../../reviews/thirteen-model-auxiliary-seed-independent-audit/README.md)
are described below; the audit does not supply missing child observations for
this earlier exploratory chain.

[`replay.py`](replay.py) prepares separate author and peer suffixes over the
[independently audited strong-seed pair](../../reviews/thirteen-model-strong-seed-independent-audit/README.md).
It rechecks that parent audit before and after, compiles the two needed source
modules and the auxiliary theorem on each side, and checks exact direct
imports, sources, object hashes, recorded child exits and axiom reports.
Session 70281 actually exited 0 and printed
`PASS_PAIRED_THIRTEEN_AUXILIARY_SEED 3907252c1f418da6ab71b3321c0659312cef6072f3f2191a45cd893ad52505b0`.
The [receipt](replay-receipt.json) records six Lean child exits, six direct
dependency-check exits and identical object hashes for corresponding modules.
The [terminal observation](terminal-observation.json) records the actual outer
exit; there were no warnings or `sorryAx` in the suffix compiles.

The replay requires a fresh `/tmp/ipra-thirteen-aux-seed-pair-*` output path,
uses `-M4000 -j1` and 240-second per-module timeouts, and refuses optimized
Python. Package-transitive/dynamic ancestry and the original Foundation
wrapper's unobserved exit remain inherited from the parent evidence.
