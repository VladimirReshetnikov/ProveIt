# Internal Pell classification: frozen author checkpoint

26 October 2026. **Author pair PASS; independent review pending.** ROOT
fully read the complete new main/Checks, proposal and executed driver,
including every later source correction, before compilation. The only
main import is the independently accepted ArithmeticPellRecurrence main.

For every IΣ1 model and every b,x,y, `norm_iff_index` proves

    x*x=1+(b+1)*(b+3)*y*y
      iff ∃ time≤y, xcoord time b=x ∧ ycoord time b=y.

This is classification of arbitrary internal solutions, not just ordinary
natural solutions or a conditional theorem supplied with an index. The
forward theorem first proves x>0 and x<=(b+2)y+1. For y>0 it constructs
the justified natural differences u=(b+2)x-d*y and v=(b+2)y-x, proves
u>0,v<y, the same norm and both exact inverse recurrence identities.
Polynomial identities and positive-square comparison establish every
subtraction bound; the arithmetic model is not assumed to be a ring.
The reversible norm-step proof cancels a common positive-polynomial sum.

`solution_index` uses genuine Sigma1 order induction on y with invariant
`∀ x<=(b+2)y+1, norm → ∃ time<=y, coordinates`. Its bounded universal and
represented coordinate graphs have an actual definability certificate.
No unbounded predicate induction, external Pell classification or ordinary
Nat induction replaces the internal argument. The zero-ordinate branch
forces x=1; the descent branch adds one to the smaller internal index.
The reverse direction uses the accepted recurrence norm theorem directly.

Checks expose the arbitrary internal witness, the zero-ordinate endpoint
and every descent field. Six axiom reports contain only propext,
Classical.choice and Quot.sound. The literal carrier congruences and
cofinal simultaneous witness construction remain separate work.

Exactly96 prerequisites are reused:95 Foundation modules/380 artifacts
plus the accepted recurrence main, for381 artifacts total,38 external
names and114 boundary companions. The new plan extends the exact prior
source/header inventory and selects the accepted independent recurrence
provider explicitly. No dependency or Foundation build ran.

Three attempts are preserved. Attempt1 exposed local positivity/API,
addition-commutativity and inequality-orientation elaboration issues plus
a simplifier linter. Attempt2 left one addition-inequality orientation.
Attempt3 passes both leaves without diagnostics. The mathematical target,
imports and caps are unchanged, and no failed object is accepted.

Final provider: `/tmp/arithmetic-pell-classification-author-5g_vrtpf/lib`.
Pinned Lean4.32 commands use `-M6000 -j1 -DElab.async=false`, one thread,
fresh private regular outputs, explicit LEAN_PATH and a512MiB reserve.
Main passes in8.002s, peak1,847,372KiB RSS; Checks in1.765s,
peak1,792,460KiB RSS. Main output is empty; Checks has only six reports.

Main source: `93cb97fababdd4a1aac7766e5be1d35b3af69b52e4a7ac23726f2c6c42ec8f73`.
Checks source: `398daaff4b69ea0902cd89f0d63143e21dc4db945be717c6d8cf919795b203c5`.
Main object: `29fc853c66cbea0cd892ad5a38fb1c708388b80c2a448965fef25822c10ffb5e`.
Checks object: `558399a4ff004d67bd9c492e0a2996abd5fe548ee46bf3c9eb80980862118179`.
[Replay packet](arithmetic-pell-classification-replay.json) SHA:
`f2931133005fcba1a929c6202a295b13216fea76420aaac6a6e4a663d645ee90`.
[33-file author manifest](arithmetic-pell-classification-author-replay/FILES.json) SHA:
`df0386eb33ddeb4485cf197ffe1b10309882fff619cdb957d844e8b80a1113fa`.

The internal discriminant family is exactly the polynomial (b+1)(b+3)
with base b+2. This does not assert a classification for every possible
Pell discriminant. Carrier congruences, index restrictions, cofinality,
machine/source calibration and the actual PA/HA equation equivalence
remain open. No displayed equation or PDF was modified.
