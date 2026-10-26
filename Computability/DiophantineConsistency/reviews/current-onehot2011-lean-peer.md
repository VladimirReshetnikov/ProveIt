# CurrentOneHot2011 independent composition review

**Verdict: PASS.** I read all106 lines of the root-authored module and all43
lines of its focused checks, verified the announced frozen hashes, checked
every premise against its supplying theorem, and freshly replayed both
files. No mathematical or binding issue was found. No source changes were
requested or made.

This is an independent review of the root's composition. I authored its
earlier `CurrentEarlyPadding2011` dependency, so this receipt does not claim
an independent authorship-separated review of that dependency itself.
Its complete source and the count/staircase sources were reread to audit
the composition's order of inference.

## Exact source binding

| File | Lines | SHA256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/CurrentOneHot2011.lean` | 106 | `45e9cd33fb50e4fc16f524948fc2f68a4dfbd334dd64e7fda114b3c55946842c` |
| `Lean/DiophantineConsistency/CurrentOneHot2011Checks.lean` | 43 | `09dba01a70674dcfb8a3f0aaec309f29e89a56f40b03e7bbaf2974a2e0e62eba` |

The hashes were checked both before and after the replay and were unchanged.
The four direct source imports were also pinned:

| Dependency | SHA256 |
| --- | --- |
| `CurrentCount2011.lean` | `efb3403e3abc771a73f388be6adfdc90263902c8f8303d47fc933beb1fcc5f86` |
| `CurrentEarlyPadding2011.lean` | `13dd5214cba3f9d704e4617b3e1140353aaa4cc18c0fd02170153a308160c3ea` |
| `CurrentPhaseParity2011.lean` | `3abd1bc07fe430892871e13b0b066a689ef74854a45bc725ee73bfe349325eb7` |
| `CurrentPolynomialWindow2011.lean` | `db64a1e9130d09d606f3262781be9a4c0d70db1a9cdb7482cd74ecc0ddf0b730` |

## Premise and circularity audit

`middle_rotation_bound` derives the actual temporal-digit bound1024 from
Booleanity and `W % 47 ≤ 10`. It uses the full Boolean rotation identity,
so there is no omitted quotient contribution or supplied alignment premise.
`middle_rotation_mod` derives divisibility by16 from `7 ≤ W % 47`, retaining
the exact shifted source. Its proof only needs the weaker lower bound4,
which the stated bound7 correctly implies.

`literal_count_le_one` supplies `MiddlePadding` with the actual function
`paddingUnit c b`, rather than an arbitrary witness whose physical meaning
is assumed. All three full483 conclusions of `padding_bindings` match the
definition of `MiddlePadding`: the two-unit bound, normalized residue at
offset63+j, and the actual bit-three mask test. The Boolean word, support,
carry bound, local equation, high mask and cell base are identical in both
calls. The two phase assumptions are introduced only inside the middle-phase
branch requested by `count_le_one_of_middle_padding`.

The early padding reset uses the unconditional coefficient-tail bound and
temporal bound1024. It does not invoke the conditional one-selector reset.
Thus the dependency order is not circular: Boolean support and a globally
bounded carry give the early padding residues; these bound the483-prefix
count by3; Booleanity bounds the remaining459 selectors; and the actual
clause low mask then gives at most one selector. The count theorem's other
phase branches cover0..6 and11..46 without padding. All clause terms remain
bound to the actual normalized convolution, including incoming carry,
selector1's bare contribution, and the unaligned temporal source.

`physical_count_le_one` converts the actual selector sum through the proved
physical permutation into the literal sum over positions0..941. No abstract
tile indexing or physical ordering is substituted by assumption.

`facts_count_phase` first obtains this count at every base of residue0.
Only afterward does it apply the origin-marker parity theorem. That theorem
receives the same word, carry, normalized digits and actual temporal shift,
plus the count at base0 and the already restored `c 0 = 1`. Consequently
fractional phase zero is derived, rather than used to prove its own count
premise. No occupied-cell or decoded-label statement is needed.

`polynomial_zero_count_phase` starts with only positivity of all14 actual
coordinates and zero of the literal fixed-port polynomial. The imported
window theorem constructs one source, one positive length and one coherent
triple of word/carry/digit functions. The final existential retains exactly
those same objects and their complete `Facts` record. No separate source,
mask, count, phase, or native-calibration premise is introduced. The exact
rank-based temporal exponent is preserved.

## Focused checks and scope limits

The first check invokes the endpoint directly with
`Carrier65.polynomial CurrentWindowCarry2011.ports`, confirming the complete
fixed-port binding through the displayed polynomial abbreviation. The
second proves that the origin cell has exactly one selector: the derived
upper bound is combined with the actual forced origin digit1. It does not
extend that lower bound to other cells. The last check keeps `W/47` as an
explicit cyclic shift after fractional phase is removed.

Despite the module's short name, its general count result is **at most one**
selector per cell. Empty nonorigin cells remain possible at this stage.
The packet does not prove whole-field alignment, all-cell occupation,
decoded tile labels, Wang matching, machine semantics, or a consistency
equivalence. These are explicit subsequent obligations, not hidden premises
of this endpoint.

## Independent fresh replay

I created `/tmp/current-onehot2011-circuit-peer/DiophantineConsistency`,
symlinking available prerequisite entries while excluding every
`CurrentOneHot2011.*` entry. The reviewed main file was compiled to a new
object there. The checks were then run with this temporary namespace first
in `LEAN_PATH`, so they used the independently rebuilt main object. No
shared source or compiled object was overwritten.

```sh
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentOneHot2011.lean \
  -o /tmp/current-onehot2011-circuit-peer/DiophantineConsistency/CurrentOneHot2011.olean \
  > /tmp/current-onehot2011-circuit-peer-main.log 2>&1
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env bash -c \
  'export LEAN_PATH="/tmp/current-onehot2011-circuit-peer:$LEAN_PATH"; exec lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentOneHot2011Checks.lean' \
  > /tmp/current-onehot2011-circuit-peer-checks.log 2>&1
```

Main: PASS,3.86seconds,3258276KB peak; no diagnostics. Checks:
PASS,3.29seconds,3249628KB peak. The fresh main object SHA256 is
`5b9132972c548497471e9991017c162e207c9c147bcf501b06636bf1f4b9221f`.
All four reported endpoint axioms are only `propext`, `Classical.choice`,
and `Quot.sound`. Neither reviewed source contains `sorry`, a new axiom,
or `native_decide`.

This replay freshly checks the two reviewed files against existing
prerequisite objects. It does not claim a fresh rebuild of their entire
dependency closure. Numeric enumeration was unnecessary for this composition
review and was not performed. No commits were made.
