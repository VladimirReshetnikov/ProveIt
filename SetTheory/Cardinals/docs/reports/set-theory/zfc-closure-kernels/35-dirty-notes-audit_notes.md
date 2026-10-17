# Literature and provenance audit — 2026-10-16

This note is an intermediate research record for the requested report. It is based on direct GitHub plugin reads, not an independent local Coq rebuild.

## Current verified comparison point

The current public comparison point found is **253 working states**, including initialization, on a blank bi-infinite binary tape. It is public in **open PR #20** to jeff87654/busy-beaver, by **mira-emmy**, not yet in the main-branch README. The main branch still advertises the verified 254-state baseline.

- PR: https://github.com/jeff87654/busy-beaver/pull/20
- Exact head: `0d544f2a2e3c18f12278441a74b7879f31cbe856`
- Branch: `mira-emmy/busy-beaver:zf253-exact-equivalence`
- PR created: 2026-10-15T23:50:55Z; last update observed: 2026-10-16T00:26:00Z.
- Observed status: open, unmerged, mergeable.
- README at pin: https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/README.md
- Literal table: https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/machine/zfc_253.tm
- 253 working states; start state 0; blank 0; separate uncounted terminal 253; 506 transitions.
- Table SHA256: `84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.
- Theorem source: https://github.com/mira-emmy/busy-beaver/blob/0d544f2a2e3c18f12278441a74b7879f31cbe856/ZF/m253/coq/e2e/E2E253.v

### Independently observed CI evidence

The GitHub API check-runs endpoint for this exact head shows success for the zf253 job:

https://github.com/jeff87654/busy-beaver/actions/runs/38829452130/job/116744580063

The actual decoded job log was fetched, not merely the success badge. It reports:

- all 160 source modules built;
- 194 closed assumption reports;
- recursive coqchk passed on 160 roots and all recursive dependencies;
- recursive coqchk duration 225.6 seconds;
- total checking duration 1049.7 seconds;
- peak sampled RSS 1,280,936 KiB.

The log explicitly prints all three endpoint formulas and all three endpoints report closed assumptions. A separate fork workflow also reports success:

https://github.com/mira-emmy/busy-beaver/actions/runs/38829447100

This proves that upstream CI accepted the exact submitted source tree under its stated environment. It does not replace a fresh local reproduction, and should not be described as one.

### The one-state reduction

In original254 labels, the four edits are:

| State/read | Write | Move | Target |
| --- | --- | --- | --- |
| 3/0 | 0 | L | 48 |
| 5/0 | 1 | R | 97 |
| 5/1 | 1 | R | 64 |
| 49/1 | 0 | R | 5 |

Old state8 is deleted. Old state5 shares initialization on0 and a guarded runtime helper on1. It is compact start0. Old dispatcher96 becomes compact33; old terminal254 becomes terminal253. The code is the same abstract enumerator as the baseline.

At literal time312,975 the table reaches dispatcher33, head−17, PC000, header distance40, source-order registers [5,0,0,0,2,0,0,0,0], plus158 spare blocks whose two nonzero values are checked. This corresponds to the unchanged register program's330th configuration. Exact spare data, not just the primary registers, matters.

The 252-state core obtained by folding5→64 has passed runtime contracts but does not come with a successful blank initialization. It is not a competing blank-tape record.

## Baseline254

https://github.com/jeff87654/busy-beaver/blob/main/ZF/m254/README.md

The literal table was designed by Mira-Cult and copied unchanged from their audited 2026-09-30 reduction. jeff87654's contribution is an end-to-end Coq proof.

- Original table SHA256: `d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb`.
- Main merged proof PR16 on2026-10-14; proof commit `c132d7eae8158cd3a9850ea3eb7251158c3dd821`; merge `c5765123923844c8b0ca6ad174a1e932764fdaed`.
- https://github.com/jeff87654/busy-beaver/blob/main/ZF/m254/coq/e2e/E2E254.v
- At current fetch, `Mira-Cult/turing-machines` returned GitHub404 via both README and commits endpoints. Thus rely on the preserved literal table, formal proof, and attribution, rather than claiming access to unavailable original source.

### Exact target and trust boundary

Both253 and254 prove external Coq propositions of the form

`halts tm c0 <-> tprv SIR bot`

and analogues for the library's ZFc and ZFc+AC. Here ZFc universally closes separation/replacement instances; AC is Zermelo's choice-set axiom. Regularity is separately transported by the vendored relative-consistency development.

These are exact finite classical-refutation equivalences. They are stronger than a claim that nonhalting is merely unprovable in ZFC, but they are **not themselves a formalized arithmetization showing ZFC proves the biconditional about its own chosen proof predicate**. PR20 explicitly disclaims an additional internalization claim. A report must either provide a finite proof-transformation/internalization argument and identify its status, or keep that proof obligation open. Coq's “no axioms” output alone does not establish formalizability of an arbitrary CIC theorem in ZFC.

## The minimalist theory already used

Definitions:
https://github.com/jeff87654/busy-beaver/blob/main/ZF/m254/coq/settheory/S_def.v

Equiconsistency:
https://github.com/jeff87654/busy-beaver/blob/main/ZF/m254/coq/settheory/S_main.v

S0 is equality axioms plus CP and the GIC schema; it has no extensionality, regularity, or choice. SIR adds irreflexivity IR. Using ordinary logical notation,

CP:
∀p ∃V [p∈V ∧ ∀x∈V (x⊆V ∧ ∃W∈V ∀z(z⊆x → z∈W))].

GIC(phi):
∀B ∃C [(∀a∈B ∀y(phi(a,y) → ∃y'(phi(a,y') ∧ y'∈C))) ∧ ∀y∈C ∃x phi(x,y)].

IR:
∀x ¬x∈x.

The final `x` in GIC is global, not restricted toB. This is a significant distinction from a standard strong-collection statement.

S_main proves **S0_equicons** as well as SIR equiconsistency. Therefore IR is already known not to be necessary for the theory's consistency strength. It is necessary for the present machine encoding, whose code1 is both Rel(0,0) and falsity, and for soundness of admitted variable collisions. Removing IR without changing the logical endpoint is invalid.

The soundness direction relativizes SIR to constructibleL, using reflection for CP and least-stage collection for GIC:
https://github.com/jeff87654/busy-beaver/blob/main/ZF/m254/coq/settheory/S_sound.v

The other direction interprets ZF via a bisimulation quotient. One must not claim naive equality-by-identical-members identifies objects correctly; the quotient construction is substantive.

## Historical sources and corrections

### Yedidia–Aaronson7910 is a different target

Primary paper:
https://www.scottaaronson.com/busybeaver.pdf
https://arxiv.org/abs/1605.04343

Web refs available to root after reopening:
- `turn0search1` / `turn13view0` / `turn13view1`: author-hosted paper.
- `turn0academia23`: arXiv abstract.

The7910 machine searches a Friedman finite combinatorial statement equivalent to Con(SRP), where SRP is a stronger large-cardinal theory extending ZFC. The paper states this in section3.1, footnote3 (PDF page8). Therefore it cannot be treated as an exact Con(ZFC) benchmark. Its ordinary consistency hypothesis only establishes non-provability of nonhalting; actual nonhalting is calibrated to the stronger theory. A historical table should mark this distinction.

The main jeff README's general sentence that the lineage “has always been” O'Rear's proof enumerator followed by7910 is historically imprecise; only the later O'Rear line fits that description.

### O'Rear1919 and748

Primary repository:
https://github.com/sorear/metamath-turing-machines
https://github.com/sorear/metamath-turing-machines/blob/master/machines/2017-zf-sorear-748/zf2.nql

The README describes NQL, Cantor-paired proof coding, compressed decision diagrams, and the1919ZF proof enumerator; reproducible machine folders preserve explicit .tm and .nql pairs. The name2017 denotes compiler-version policy, not necessarily first construction date. The author-hosted 2020 survey below documents748.

Web ref `turn9view1` is the successfully fetched repository README. It is a primary engineering source.

### Aaronson2020 survey

https://www.scottaaronson.com/papers/bb.pdf

Web ref `turn6view2`. “The Busy Beaver Frontier,” section1 defines the standard blank-tape, bi-infinite, binary, L/R, working-state convention. Proposition3 and section4.2 explain incompleteness/748. This is useful for conventions and historical context; do not use a2020survey for a2026record.

### Later engineering chain

jeff's current README reports Riebel745(2023), Ridenour643→636(2024), Wade588→549→432(2025), then393, and its own361→354→336→335. This chain has primary tables and recent Coq certificates in the supplied repository for393 through335. For a short report, there is no need to reproduce every historical count:7910(different theory),748,393,335,254,253 plus relevant semantic caveats suffice. None gives a global minimality theorem.

## Other current public results not to confuse with the target

- Recently merged PA238 searches Peano-arithmetic refutations, not ZFC. It is irrelevant as a smaller ZFC benchmark.
- Open PR19 (head923f561312adaaad8bd0e6b20a1e17e5f0339d6d) has296states and searches ZFC+Grothendieck-universes refutations. It is larger and has a stronger target.
  https://github.com/jeff87654/busy-beaver/pull/19
- Small weakly universal machines with periodic infinite backgrounds are not blank-tape candidates; the initializer/program information and blank-start semantics must be counted.

## Prior local search boundaries

ProveIt already documents exhaustive finite families, none of which yields a smaller blank machine:

- public253 direct folds:56,196 protected folds, plus504 folds from the excluded old5/84 cases. Sole known runtime survivor is5→64.
- symbol-wise fusion:148,368 candidates, no accepted affine contracts at fuel1000; most failures are fuel or abstraction limits, not semantic refutations.
- nonuniform old107 incoming-edge recipes:504, none accepted.
- local-window macro checks:63,756 ordered state pairs at radius4 and5,64steps per side, no certificates.
- exact-step quotients: singleton classes, not a lower bound on arbitrary halting-equivalent machines.

Files:
Computability/BusyBeaver/Research/ZFC/public253_fold_search.md
Computability/BusyBeaver/Research/ZFC/public253_context_search.md
Computability/BusyBeaver/Research/ZFC/public253_macro_search.md

The report should not repeat these as new findings or turn their limited negative certificates into a minimality claim.


## Independent review of the new checked safe-start and dirty-root results

Prior ProveIt source09 already states the ordinary general safe-boundary theorem. Its point5 combines arbitrary cutoff drainage, a padded first AX command with unused parameter u, `L1_Comp254.blk` quantified over arbitrary retained current theorem/stack, and the invariant for soundness. The new `EnumSafeStart254.lean` is valuable as a checked Lean proof; its underlying mathematical safe-start observation should be attributed to source09 rather than claimed as new.

The additional `DirtyRoot254.lean` theorem genuinely enlarges the covered source-root initial fields. For source register vector `[N,T,W,A,D,H,X,Y,L]`, where A is axiomcode and X/Y are scratches, fetch gives:

- If L=0: n=N, nextproof N'=N+X+1, scratch X'=0.
- If L>0: n=L-1, nextproof N'=N, scratch X'=X.

Let `(u,v)=unP(P(X',Y)+n)`. The virtual clean root has nextproof N', prooflist `P(A+u,v)+1`, zero axiomcode and scratches, and identical T,W,D,H. Actual dirty and virtual clean runs agree exactly after the first read174.

I independently checked this against the actual loops: loop194 copies N into both prooflist and scratch1; loop203 then adds the entire N+X into nextproof, followed by increment. loop115 starts unpairing from the existing scratch pair, loop209 transfers its second coordinate to prooflist, and loop201 adds the first coordinate to axiomcode. This establishes the stated formulas, including the easy-to-miss X carry when L=0 and the persistence of Y through fetch.

I also reviewed the completed `research/theory/BusyBeaver/ZFC/DirtyRoot254.lean`. Its generic `node_transfer` handles a continue1 exit correctly: the common continuation preserves the exact restart register file, so the existing recursive run can be reused. `root_equiv` preserves every structured root outcome and its final register file. `iter_equiv` needs to change only the initial root pass, because its resulting file is identical. No flaw found.

Scope matters: `root_equiv` and `iter_equiv` concern the literal 219-node DAG, all nine AS fields, and the higher-register zero tail supplied by `L2.enc`. They do not assert arbitrary interior-PC behavior or arbitrary tape behavior. `virtual_enum_iff` explicitly names the abstract enumerator and does not supply the separate missing full DAG/enumerator bridge. The agent reports successful Lean compilation and only standard Lean logical axioms; this independent review checked the formulas and proof structure, not a separate local rebuild.

The short-gap runtime252 diagnostic is documented separately in `runtime252_short_gap.md`, with portable reproduction script and JSON. It yields no smaller consistency-equivalent blank machine and no nonhalting proof.

## Independent review of the same-count direction rewrite

Reviewed `research/optimization/optimization_note.tex`, `verify_direction_variant.py`, and `direction_rewrite_certificate.json`. The proposed compact-label row change is `(131,1): (0,L,20) -> (0,R,22)`; it retains253states. The radius2 abstract reachability computation correctly overapproximates the original blank run: write the center, shift, then admit either freshly exposed bit. Its3530configurations establish the advertised disjunctive two-left-cell guard.

The local whole-tape block criterion is sound. At common endpoints, the original run remains reachable, so an invariant proved for the original machine alone suffices. Both block lengths are positive. In the second guard case, the common head at h-3 lies outside the radius2 window, but the final read/write was at h-2; no exterior cell was read or written. Thus equality of all known cells entails equality of whole tapes for arbitrary exteriors. Generic separable-search blocks also stop before executing another modified row, which is the needed compositionality condition.

Reran the standalone verifier against the actual baseline and variant tables. It passed with3530abstract configurations,12 modified-row windows, and case counts8+4. Replay output is `direction_variant_independent_replay.json`. This was a review and a rerun of the supplied standalone checker, not a separate kernel proof or an independently reimplemented checker. No soundness issue found. The597080transition-alternative count and bounded-negative scope are accurately qualified in the optimization note.
