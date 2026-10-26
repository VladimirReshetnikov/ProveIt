# Independent review: 3,776/3,671-integer direct quartics

**Accepted at the ordinary mathematical level.** I found no gap in the
private signed-quotient replacement, sign-orbit normalization, ordered
lower-bound inference or subsequent monic projections. Complete normal
and optimized default release replays pass. The low-height points remain
useful historical tradeoffs and motivate applying wire retention to the
much smaller current source. No composition is claimed materialized by
this review. All incoming and frozen files are unchanged; Lean is paused.

The archive is
`docs/incoming/ConZFC_Direct_Quartics_3776_3671_2026-10-23.zip`, SHA256
`91baf0ee4c8bf277f5caa2e735052474a68688557126463090db74e21063b7a7`.
It has 101 members; all 100 `SHA256SUMS` entries match. Scratch is
`/tmp/proofs62ff-quartics3776-review`.

| Endpoint | Integer variables | Rows | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| Recommended retained/projection | 3,776 | 2,015 | 4 | 20,194 | **47,959** |
| Fewer-variable affine/projection | 3,671 | 1,942 | 4 | 26,271 | 3,835,369,234 |
| Fully retained guarded | 7,058 | 5,297 | 4 | 24,277 | **1,992** |

The 3,671 point is now dominated by the frozen 891-integer point in
variables, rows, terms and height. The 3,776 and 7,058 points are not
dominated by the current 862/891 family because of their substantially
smaller heights. This is a coefficient tradeoff rather than a new
minimum-variable result.

## Private signed quotients are an exact local transformation

The complete two natural parents and all seven copied arithmetic/calculus
files byte-match the previously reviewed `shared-crt-prime-lift` packet.
The affine parent has 3,609 natural coordinates and 2,949 rows. The
retained parent keeps its ordinary affine arithmetic wires.

For each of 221 private pairs, the actual rows have the form

```
u=M*p,    v=M*q,    E+epsilon*(u-v)=0,
```

with p,q,u,v private as specified in the complete certificate and
epsilon=1 or -1. Replace the pair by one unrestricted integer z and
the row `E+epsilon*M*z=0`. Forward, take z=p-q. Reverse, take
`p=max(z,0), q=max(-z,0)`, then u=Mp,v=Mq. The modulus M has
nonnegative affine coefficients in retained natural coordinates, so
both restored products are natural. This proof includes M=0 and uses
no division or nonzero-modulus assumption.

The independent checker verifies privacy, the same modulus, opposite
unit coefficients, complete variable/row partitions, bridge identities
and every transformed residual. Its convenient formal section q=0,p=z
proves the exact integer-polynomial identities; that section is not
misidentified as the natural reverse lift, which uses positive/negative
parts. No signed quotient enters a retained natural gate definition or
modulus. This excludes a hidden sign dependency during natural gate
restoration.

## Sign-orbit normalization is existential, not a false pointwise claim

Each core has 110 explicit diagonal generators. For every core residual
the parity of the flipped variables is the same in all its monomials;
therefore the residual changes by one overall sign. Each generator flips
exactly one semantic pivot and no other semantic coordinate. Pivots are
distinct and unguarded. The generators commute, so any integer core zero
can be moved into the orbit where all 110 pivots are nonnegative, without
changing any guarded semantic value. Zero pivots need no special case.

The two descriptive families concern an unshifted Pell ordinate Z and
its product wire, and a Pell coordinate U with its two now-signed
quotients. These descriptions alone would not justify the transformation;
the certificate checks every original row. The theorem is existence
equivalence after orbit normalization. It does not say the original
zero already had natural Pell coordinates.

Guard equations are preserved during normalization because their original
semantic targets are unchanged, and their fresh auxiliaries need not be
flipped. This establishes a zero of the same guarded system before the
ordered sign proof is used.

## Ordered lower bounds and every restored sign are checked

At a stored step, an exact original row is rearranged as `x*A=B`, with
x absent from A,B. A is proved strictly positive from previously
established lower bounds. The certificate then proves B>=0, B>0, or
B-A>0 to conclude respectively x>=0, x>=1, or x>=2 by integrality.

To check an inequality, substitute `X_i=T_i+L_i` for already proved
nonnegative lower bounds L_i in {0,1,2}, with T_i>=0. Expand exactly.
Every resulting coefficient must be nonnegative and every variable
with an odd exponent must have a known nonnegative sign. Even powers
of unrestricted variables need no sign. Strict positivity additionally
requires a positive constant term. These sufficient rules are valid
for all integer assignments satisfying the earlier bounds; finite tests
and intended arithmetic meanings are not used as premises.

The affine core uses 645 guards, 110 normalized pivots and 2,382 steps;
the retained core uses 661 guards, the same 110 pivots and 4,942 steps.
Every coordinate intended to be natural is recovered, while all 221
signed quotients remain unrestricted. The selection heuristic is not a
minimum-guard proof.

The guards `x=a^2+b^2+c(c+1)` force x>=0 over the integers and represent
every natural x by the three-square theorem applied to 4x+1. The later
signed monic projections substitute into every row, including every
guard. Reverse their complete integer reconstruction first, normalize
the core sign orbit, then replay the ordered sign implications and the
private-quotient natural lift. No signed restoring polynomial is assumed
to preserve nonnegative values. Every accepted substituted residual stays
quadratic and every final sum of squares is an exact quartic.

## The coefficient-height mechanism is reusable

The height-1,992 point retains the ordinary arithmetic wires. Its final
3,776-variable projection uses tiny support caps: affine 2, quadratic 2.
The height-47,959 bound is measured on the fully collected polynomial,
not merely on individual rows, whose maximum coefficient is 68.
The more aggressive affine-source projection saves coordinates but
creates height 3,835,369,234. Thus retaining wires and applying restrained
local substitutions is a concrete way to control the **actual** final
coefficient height; it is not a symbolic rescaling claim.

On our current frozen `projected-factorial-radius/both_source/raw_builder.json`,
an independent raw-row probe measures 1,259 natural coordinates, 1,177
quadratic rows, 3,877 quartic terms, height 427 and maximum row coefficient
8. A fresh actual-row selector finds 161 seeds and 1,098 ordered sign
steps, suggesting a 1,742-integer guarded retained point. These are
prospective counts only in this review; complete new guard and projection
certificates must be materialized and checked before claiming the
composition. The old 110 sign generators and 221 paired-quotient
deletions cannot simply be transferred by names: the current source has
a shared shifted frame and already uses single oriented quotients.

In particular its shifted variable z0 with Z=z0+1 does not admit the
old diagonal Z-sign flip without an explicit affine reparameterization.
Its shared U flip would also require flipping oriented quotient values
that are currently natural. Relaxing their domain would require a fresh
ordinary mixed-domain proof and a new literal certificate; this review
does not silently remove those guards.

## Source pins and scoped replays

All thirteen calibration excerpts match their actual Git blobs, stated
SHA256 values and lengths, at the recorded commits `9a33342a03...` and
`278bc68df1...`. These are the actual named C222/ZF/ZFC interfaces and
arithmetic representation sources; they are not a complete buildable
Lean closure. Both whole natural parent equation files and all seven
upstream files are exactly our earlier reviewed prime-lift artifacts,
including its already justified factorial-supported CRT lift.

After reading the executed scripts, I ran `verify.py --receipt ...` in
normal and optimized Python. Both authenticate all 100 release files,
regenerate both complete frozen natural sources and arithmetic/calculus
audits, regenerate both signed and both guarded intermediates, check
every original-row symmetry and lower-bound step, replay every final
elimination and full quartic coefficient, and reject the supplied
corruption controls. All twelve stages pass in each mode. The optional
slower final optimizer search was not rerun; its complete certificates
were independently replayed, which is what establishes correctness.

Fresh receipts are `/tmp/proofs62ff-quartics3776-review/NORMAL.json` and
`OPTIMIZED.json`, embedded in the separate review JSONs. The additional
`tools/review_quartics3776.py` imports no delivered code: it checks source
and Git identities, full coefficients and every sign-generator parity
against every core residual. No Lean, TeX, historical H10 emitter,
machine search, package installation or network command ran.

The ordinary source/refutation calibration is inherited, not rebuilt
here. This review proves neither consistency nor inconsistency, makes
no global minimality claim and supplies no new internal object-ZFC proof.
