# Batch 191: dominated parameters and three further search reports

Commit `7071e5041ee316d087661b658362feed159901ef` contains useful new ideas,
including a fully calibrated **203-subtree source and a distinct 218-state
machine**. It does not yet supply an accepted 217-state blank-tape machine.
The primary [K218](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k218/README.md)
remains primary. The new [dominated-parameter alternative](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/README.md)
is a promising basis for further allocation work.

| Source | Arrival archive | Main contribution | Accepted machine result |
| --- | --- | --- | --- |
| 148 | `K217_Search_Round_2026-10-20.zip` | H/PW classical basis; three-input compiler; codec transport; crossover decoder | New initialized 217 runtime, but its blank run provably escapes along a ray |
| 149 | `K218_Dominated_Rho8_2026-10-20.zip` | Restrict the fourth axiom parameter to `U≤A` without losing any native theorem | Distinct complete 218-state machine, 203 source subtrees |
| 150 | `ZFC_217_Investigation_2026-10-20.zip` | K/S plus self-vacuity; full fixed-B obstruction; corrected runtime discovery | No smaller accepted machine |
| 151 | `zfc-217-state-search.zip` | Omit a redundant MP stack push; permute command tags; alternate stack coding | Two further complete 218-state variants |

## Placement, provenance and review

Placement **`4a1218d878`** accounts for all **936 members**: 724 new files,
130 existing aliases, 56 batch aliases and 26 archive-only members. New files
comprise 60 root records, 170 code files and 494 data files. The maximum
Windows-prefixed path length is 192. All four ZIPs were retired in that
placement; original layouts, articles, PDFs and delivery material remain
recoverable from the arrival commit. The [placement map](data/intake191-placement.json)
records every member. There are now **151 sources** and still **290 reports**.

The respective source snapshots are `d4e6b1269db24fd3379bd219d90d4ed6f11f131b`
(148, with a later freshness pin), `f8ec6158f3bdc885139ee395ae34fe44c3251b9f`
(149), and `9adcaff0a72486ecc81242e0eca86e428c74879e` (150–151).
They are historical baselines, not the arrival commit. Attribution to the
submission authors, the ProveIt predecessor constructions and the upstream
calculus is preserved. Three historical contextual README versions retain
their original context; their obsolete relative links are not new live indexes.

Each main manuscript and substantive mathematical appendix received an ordinary
source review before execution. The separate dossiers for
[148](intake191-source148-review.md), [149](intake191-source149-review.md),
[150](intake191-source150-review.md) and [151](intake191-source151-review.md)
retain the complete findings, including research branches summarized below.
Source 149 also has an independent second mathematical review. Only selected
reviewed leaves ran on disposable copies. No checksum-manifest suite,
line-ending work, recursive ancestor verification, omnibus wrapper or proof
assistant ran. These reconciliation notes leave delivered bytes and the host
article unchanged. [Recovery and reproduction](intake-191-reproduction.md)
distinguish fresh results from retained evidence.

## The main opportunity: numerical domination

Use the existing native implication `I(a,b)=4P(a,b)`, where P is Cantor pairing,
and the row

```
rho8(A,B,C,U) = ((C→U)→A) → ((A→C)→(B→C)).
```

Source 149 proves that keeping only instances satisfying **U≤A** gives exactly
the same set of derivable natural-number codes. This is stronger than mere
equiconsistency. It closes the earlier conditional `cd59` argument by adding
a depth-three implication context containing U as a subterm of A. Every
implication code dominates both arguments, including the exceptional
`I(0,0)=0` case. A finite schematic derivation then recovers unrestricted rho8.
Substitutions instantiate universally quantified numerical schemata; no
object-language substitution rule or global renaming invariance is assumed.

Two independent forward readers freshly checked the complete **3,728-node**
proof over **5,160 term nodes**. Replacing each unrestricted axiom leaf by this
fixed derived proof preserves the native coding, the private-code-coupled
bundle, MP and GEN. The inherited ZFC calibration therefore transfers directly.

The useful implementation is the common-input order `(c,z,y,x)`:
`U=D+z`, `A=U+x`, `B=H+y`, `C=c`, with incoming counter D and cache H.
GEN uses U before the extra increment builds A. The full command compiler,
explicit NIP counts and cofinal proof-code family establish completeness from
every clean candidate cutoff. This is not justified merely by observing that
the restricted axiom family is cofinal.

Three closed AX splices produce a 206-subtree reference. The final association
has **203 distinct subtrees, 4,751 leaves, depth 45 and zero-run bound 6**.
Its full primitive word and guarded control graph agree with the reference;
all 186 paths outside AX are unchanged. Physical allocation gives 218 working
states and 436 rows. Large native state labels do not count as extra states.

All **eight selected fresh jobs pass**, including both logical readers, exact
source/CFG checks, table reconstruction, canonicalization, independent complete
startup, and the combined startup/runtime proof. The ordinary proof composes
these bridges with the inherited numerical-calculus calibration to establish,
formalizably in ZFC, `¬Halt(M,blank) ↔ Con(ZFC)`. It assumes no consistency
statement to prove the equivalence. This is not a new exact-table Lean or
internal PA endpoint, an unconditional nonhalting theorem, or a minimality claim.

The separate dirty-root and dirty-unpair appendices are retained as research.
The accepted final table uses the clean common-input construction. It does not
depend on arbitrary unproved initial formula data or the failed three-field
machine experiment.

## Other useful theory and coding ideas

Source 148's two three-variable propositional schemata are
`H=(p→q)→((q→r)→(p→r))` and `PW=((p→q)→p)→(r→p)`.
Explicit MP certificates derive Peirce and K, then S. Their ordinary native
transport recovers the original propositional basis for all natural codes.
The associated three-input AX compiler accounts for nine axiom outputs plus
GEN and the saved old top, its changed cleanup, and a cofinal proof-code family.
Its measured 207/209-node sources and zero-run 7 do not improve the machine.

The codec `2^a(2b+1)-1` is accompanied by theorem/refutation transport that
co-translates formula codes and numeric labels, including the literal bundle
and its gate. This is not a claim that raw pairing and addition are conjugate.
Its 13-leaf pair and nine-leaf inverse contracts are useful; the complete
217-node source encounters an unsupported right-CC3 allocation entry.

Source 150 replaces rho8 by **K, S and self-vacuity** `A→Q_A A`, with weak
double-negated and positive-introspection variants. Own-code freshness makes
the row valid under the exact native decoder. A persistence argument recovers
double-negation elimination and rho8. The upper interpretation uses the
inherited IR comparison, rather than treating native K/S as naive syntactic
identities. The full gated bundle remains intact. The fresh finite certificate
has **1,110 nodes and five closed endpoints**. Ordinary equiconsistency is
reviewed; positive/weak self-vacuity source prices are 212/214 subtrees,
5,003/5,097 leaves and zero-run 6. Further shared-source optimization remains
an opportunity, not a demonstrated saving.

Source 151's **omitted successful-MP dummy zero push** removes 19 primitive
leaves. A corresponding compiler cleanup loses its last NIP; other uses of
MP in discard blocks always fail, so they retain their contracts. The exact
native edit is `164/1: 1R98 → 1R114`. It gives a calibrated 218-state variant,
not ordinal trace equivalence. The **DMN** variant swaps MP and DROP command
tags through rows 135/1 and 185/1, and uses the clean seed counter 2. Its
cofinal enumeration proof permits the changed cutoff. Both have fresh complete
runtime and startup evidence and are published beside the primary candidate.

Reversed work-stack pairing, called PUSH16 in Source 151, saves three primitives
at each of 93 pushes. Its arithmetic pair/unpair contracts are proved for all
naturals; the complete best source has 206 subtrees and 4,465 leaves, but the
raw prefix-valid allocation has 229 states and lacks full runtime/startup.
The 204-node merged NIP/DROP proposal has an explicit completeness gap, and the
204-node K/S-only proposal lacks calibration. None is promoted by its source
count alone.

## Crossover and initialization lessons

Source 148 reassociates a closed 30-leaf interval `[4567,4597)` as
`((A,B),A) → (A,(B,A))`, where A/B have lengths 12/6. The raw 218 table preserves
all 4,744 primitives and 6,166 nonhalting guarded ordinal successors, and its
complete startup freshly reaches the old seed at 312,909 steps. Adding the
known delete301 core fold gives a distinct **initialized** 217 table. Its full
fresh runtime succeeds, but its blank run reaches the same proved outward
ray after 85 steps. It is not an accepted blank consistency machine.

The crossover's six-bit predecessor masks are `{6,7,15,38,39,47}`. Their
nearest four-bit suffixes `{1,3,9,11}` are disjoint from the startup suffixes
`{0,5,6,7}`; shorter suffixes do not separate them. This suggests a restoring
four-bit classifier. Such a classifier has not been allocated without extra
states. The current marker relay still fails at its terminal CC2 pattern;
the literal crossover alone does not repair that conflict.

Source 150 carefully corrects a discovery error: the first visit to dispatcher
84 may be an intermediate visit, not a complete primitive return. Fresh replay
of the 166→12 example confirms proper baseline/candidate returns at 596/626
steps, after earlier visits at 150/318. Its raw-frame diagnostic reaches a
different clean seed after 532,731 steps, but fails an admitted CD8-positive
case after 4,738 steps. That failure is not asserted to lie on the blank run.
Source 151 separately strengthens two repairs' failures to their actual first
primitive after the blank endpoint. These distinctions prevent false promotion
from finite startup or dispatcher sampling.

## Obstructions and bounded negatives

The full four-value model for rho8 restricted to **B=C** validates all retained
native rows and the bundle while excluding falsity. Its all-natural recursion
and derivation induction give an ordinary consistency proof; fresh finite
checking confirms 64 restricted instances and 512 retained-row evaluations.
The separate B=0 model is only propositional. The 16-element persistent-negation,
six-element stability and nine-element modal-commutation examples also have
fragment scopes; they do not silently become full set-calculus models.

The stronger gate `c>max(a,b)` attached to the **entire** bundle is already
excluded by Source 142's full countermodel, assuming ZFC consistent when
excluding the requested calibration. Source 150's original review described
only a missing interpretation lemma. The preserved [reconciliation addendum](intake191-source150-gate-reconciliation.md)
corrects that weaker assessment without rewriting the original dossier. A
restriction of the core alone while retaining full vacuity is a different theory.

All large two-row, complemented-marker, source-grammar, allocator and abstract
reachability records remain placed and recoverable. Their domains overlap;
their finite counts are not lower bounds. Source 151's ternary closure requires
initial registers 0 and 4 at least 2 and all others zero, and was not freshly
replayed here. Prefix-valid allocation and source-mask-admitted samples do not
prove arbitrary-natural binary runtime or blank reachability.

The final primary/contextual state-85 fold does **not** directly stack with
Source 149. Nine occurrences of its first source role survive, but the four
occurrences of its second role are absent. The enabling association is already
present five times in the final source. Applying it to the reference gives
205 subtrees but zero-run 8. A [fresh bounded local-fold search](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k218/alternatives/dominated/research/README.md) on the new table
covered 47,306 ordered pairs and 657,944 specifications with no survivor;
its radius-7/fuel-97 scope is not a lower bound. A different contextual sharing
opportunity at native states 69/400 needs helper roles now used elsewhere.
This makes source reassociation plus helper allocation a concrete next task.

## Fresh execution summary

| Construction | Runtime cases | Symbolic rules | Covered rows | Minimum duration | Complete blank startup |
| --- | ---: | ---: | ---: | ---: | ---: |
| Source 148 crossover217 | 6,167 | 1,515,251 | 434 | 12 | Failed: proved ray at 85 |
| Source 149 dominated218 | 6,176 | 1,616,989 | 436 | 13 | 312,605 |
| Source 151 omit-zero218 | 6,142 | 1,511,359 | 436 | 12 | 312,909 |
| Source 151 DMN218 | 6,167 | 1,516,795 | 436 | 12 | 123,776 |

Source 148 has eight fresh selected jobs; Source 149 has eight. Source 150 has
five cheap fresh leaves; its unchanged core runtime was not repeated. Source
151 has two fresh full runtimes and a separately authored selected source,
receipt and dense-startup audit. These runtime certificates range over arbitrary
natural frame parameters through symbolic induction. They are not finite
register tests or proof-assistant kernel results. Raw commands, logs, timeout
bounds and regenerated outputs are preserved, with large exact JSON compressed
losslessly. The [fresh-evidence map](data/intake191-fresh-publication.json)
records publication locations and actual scratch origins.
