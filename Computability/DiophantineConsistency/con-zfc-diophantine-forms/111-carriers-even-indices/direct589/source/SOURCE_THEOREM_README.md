# Fresh75-predicate integer quartic profiles

This separate research packet starts from the frozen76-predicate parents
and removes only the original scalar guard raw93>=0. Every original raw
body coefficient and metadata record, and every remaining predicate,
is preserved. There is no extra defining wire. The accepted76 profiles,
other candidates, canonical page, common documentation and Lean remain
unchanged. No global optimum or new internal-ZFC result is claimed.

The resulting system has72 original scalar guards and the three unchanged
predicates

    raw656-1 >= 0,
    raw674*raw861 >= 0,
    raw87-2 >= 0.

Each E>=0 uses the quadratic row E-a²-b²-c(c+1)=0 with three fresh
unrestricted integer variables. Both raw94 and raw95 remain directly
guarded. Put f=raw87,N=raw93,r=raw94,s=raw95,C=raw91. Complete original
source rows give

    C=r+s+1, f*C=N+s,
    N=f*r+(f-1)*s+f.

The three retained direct values f-2,r,s are nonnegative, so N>=2
before the initial source-prefix closure. No power or factorial meaning,
nor any sign of C or an auxiliary gate, is used in that recovery. This
restores the only missing one of the61 old initial sign premises.
After supplying a fresh sign triple for N, the accepted76 ordinary
source proof applies unchanged. The reverse map forgets that triple.
The complete ordinary argument is separately sealed in
`research/factorial-radius-output-sign/PROOF.md`.

The profile checker independently collects both original source cuts and
their full eight-row combination, then verifies every coefficient after
the substitution f=F+2. Its displayed nonnegative polynomial is

    N-2=F*r+F*s+F+2r+s.

Thus the early sign is independently re-established before using any
domain interpretation. The new parents have exactly75 predicates, with
60 directly guarded initial semantic signs and61 after that recovery.

## 1. Complete quartics and actual metrics

All polynomials below are the fully collected sums of squares of their
complete quadratic residual lists. Each has exact degree4. The raw
body keeps1259 variables/1177 rows verbatim; the compact body is its
exact667-variable/585-row affine contraction.

| Baseline | Profile | Integer variables | Quadratic rows | Quartic terms | Height |
|---|---|---:|---:|---:|---:|
| Compact | unprojected | 892 | 660 | 4702 | 63905867 |
| Compact | support4 | 633 | 401 | 5581 | 63905895 |
| Compact | support8 | 607 | 375 | 8597 | 2445790974704 |
| Compact | support16 | 605 | 373 | 8692 | 2445790974704 |
| Compact | support32 | 604 | 372 | 10028 | 2445790974704 |
| Raw | retained | 1484 | 1252 | 4948 | 432 |
| Raw | support2_affine1 | 837 | 605 | 3780 | 4750 |
| Raw | support2_affine2 | 692 | 460 | 5539 | 737653 |
| Raw | support4_affine2 | 630 | 398 | 8850 | 737653 |
| Raw | support8_affine2 | 616 | 384 | 8814 | 938261 |
| Raw | support16_affine2 | 609 | 377 | 8823 | 964213 |
| Raw | support32_affine2 | 609 | 377 | 8823 | 964213 |
| Raw | support8_affine3 | 616 | 384 | 8760 | 43849839 |
| Raw | support16_affine3 | 608 | 376 | 8739 | 45769499 |
| Raw | support32_affine3 | 608 | 376 | 8739 | 45769499 |
| Raw | support8_default | 604 | 372 | 9676 | 2445790974704 |
| Raw | support16_default | 604 | 372 | 9676 | 2445790974704 |

The first15 settings match the frozen76-profile configuration list.
They each save three variables and one row at the matched height;
all term counts are freshly collected, rather than extrapolated.
The two additional raw settings allow affine support to use the same
cap as the general support cap. Their604-variable quartics have352 fewer
terms than the matched604-variable compact support32 point, at the same
height. Both construction histories and complete certificates are retained.

The lower-height609-variable point has8823 terms and height964213.
The608-variable point reduces support to8739 terms with height45769499.
These are measured variable/support/height tradeoffs, without a global
minimality or Pareto completeness claim.

## 2. Exact integer inverses precede source semantics

The independent checker imports no optimizer. It checks the complete
source/predicate boundary, every original body row and metadata record,
all75 guarded expressions and every private guard position. It proves
the raw/compact parent zero bijection using all592 original integer
affine restorations. The forward implication checks each actual monic
defining row in dependency order; the reverse implication checks every
substituted original and guard row. No sign assumption precedes this map.

The separately authored projection verifier replays every fresh monic
substitution, deleted defining row, retained coordinate and surviving
constraint over unrestricted integers. No coordinate is discarded as
unconstrained. Every sign guard remains present through its full signed
substitution. The complete75-predicate parent must be restored first.
Only then is raw93's sign recovered by the unconditional row identity,
and a fresh triple reaches the accepted76 domain. The later ordinary
source proofs and nonpointwise comparison-base lift remain separate;
no original q4 positivity or all-natural restoration is asserted here.

The whole quartic is independently expanded and compared coefficient
by coefficient. Arbitrary signed restoration fixtures and changed source,
domain, inverse and quartic controls are additional diagnostics. They
do not replace the complete symbolic inverse identities.

## 3. Reproduction and scope

`SOURCE_PINS.json` authenticates the complete source/proof dependencies
and the immutable407/888 arithmetic archive. Only the producer imports
its reviewed terminal-elimination module. Full equations, projection
certificates and complete sparse quartics are retained for all17 settings;
`CENSUS.json` contains their exact metrics.

```sh
python3 -B Computability/DiophantineConsistency/research/factorial-radius-output-sign-profile/build.py --check
python3 -B Computability/DiophantineConsistency/research/factorial-radius-output-sign-profile/check.py --output /tmp/factorial75-normal.json
python3 -B -O Computability/DiophantineConsistency/research/factorial-radius-output-sign-profile/build.py --check
python3 -B -O Computability/DiophantineConsistency/research/factorial-radius-output-sign-profile/check.py --output /tmp/factorial75-optimized.json
```

This packet provides ordinary source/domain and full finite algebra
research. It newly claims no native refutation calibration, internal-ZFC
equivalence or Lean theorem. Lean remains paused.
