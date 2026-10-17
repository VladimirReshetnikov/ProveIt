# Code254 domain correction and baseline audit

This bundle accompanies the ZFC small-machine research report. It freezes the
ProveIt logic audit at commit
`d74c63b0c8d4f35597f1bd5976d941b9f104f94e`
(2026-10-16 22:04:08 UTC), whose parent is
`6ec2e80dbbe45a99b7812fb5757977307959a51e`.
No remote repository was edited.

## Verified contribution

The original `Code254.c254_complete` has this no-model premise:

```lean
∀ (D : Type) (mem : D → D → Prop), (∀ x, ¬ mem x x) →
  (∀ f, EncBundle f → ∀ e : Nat → D, Sat mem e f) → False
```

This premise is impossible. Take `D = Empty` and the constantly false
relation. Irreflexivity holds, and the axiom-satisfaction condition holds
because there is no environment `Nat → Empty`.
Thus the old implication is kernel-correct but vacuous; it does not give
completeness from the absence of a nonempty model.

The existing `Tarski.alias_complete` does not have this defect: it retains
an environment in the semantic conclusion. The repair simply retains that
same environment in `c254_complete`:

```lean
∀ (D : Type) (mem : D → D → Prop), (∀ x, ¬ mem x x) →
  (∀ f, EncBundle f → ∀ e : Nat → D, Sat mem e f) →
  (Nat → D) → False
```

An equivalent formulation takes `Nonempty D` as an explicit hypothesis.
The new companion proves both forms, using the already available named
calculus and encoding lemmas.

- `EmptyDomainAudit.lean`: core-only theorem proving the bad premise
  impossible for arbitrary syntax and satisfaction, plus equivalence of
  the pointed and explicitly nonempty formulations.
- `EmptyDomainRepair.lean`: exact diagnosis and both useful completeness
  statements for the actual `Code254` definitions.
- `Code254-empty-domain.patch`: minimal fix to the existing theorem.
- `check_lean-code254-order.patch`: add the new module to the serial source
  list before the umbrella. At this pin the list has 52 units but omits
  `Code254`, which the umbrella already imports. The fixed normal list has
  53 units; the optional `NoQuotient254` unit remains additional.
- `Code254-and-checker.patch`: both repository patches together.

The patches are prepared against the frozen commit. If the repository has
advanced, review its current declarations before applying them.

## Kernel verification

Run:

```sh
python3 verify_empty_domain.py --lean /path/to/lean
```

This rebuilds the 11-module logic/repair closure serially into a fresh
temporary directory and separately checks the core-only audit.
It requires Lean 4.32.0. No project oleans or finite-bootstrap cache are used.

The recorded local run succeeded with Lean 4.32.0,
compiler commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.

| Theorem | Kernel dependencies |
|---|---|
| `badNoModel_is_false` | none |
| `pointed_iff_nonempty` | none |
| `original_c254_complete_premise_impossible` | none |
| `c254_complete_pointed` | `propext`, `Classical.choice`, `Quot.sound` |
| `c254_complete_nonempty` | `propext`, `Classical.choice`, `Quot.sound` |

The JSON evidence records every source SHA-256, compiler output and exit
code. `source-manifest.json` maps the vendored source closure to its pinned
repository paths and independently retrieved Git blob SHA-1 identifiers.
The replay driver verifies those Git blob identities before compilation.
The recorded successful run used the exact pinned source bytes, after
removing one demonstrably surplus final newline introduced by the local
download procedure. `git-blob-verification.json` records this byte audit.
`LICENSE.ProveIt` preserves the repository's MIT No Attribution license;
source comments and upstream attribution are intact.

The full 53-unit research checker was not run here. The much smaller
logic closure is sufficient to verify the diagnosis and repaired theorem;
it does not require the large machine bootstrap.

## Current machine baseline

The merged upstream pin is
`297ab8df7e5de329605c3875b4934643b371a5e3`.
Its smallest listed machine is Mira-Cult's 254-state binary blank-tape
construction, with Jeff's Coq proof to finite refutations of SIR, closed ZF,
and ZF plus the selected choice-set axiom.

There is already a publicly available **253-state** reduction by
mira-emmy, based on the Mira-Cult/Jeff machine. At the audit cutoff,
[upstream PR 20](https://github.com/jeff87654/busy-beaver/pull/20) is open
and unmerged, with head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`.
It retains the same program, enumerator, proof calculus and set-theory
transports; its changes concern the literal machine and its simulation.

Its exact table has 253 working states, 506 binary transitions, blank
symbol 0, start state 0 and a separate terminal label 253. Its SHA-256 is
`84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.

The exact-head `zf253` CI result was observed as successful in both
repositories. The upstream run is
[the 2026-10-16 job](https://github.com/jeff87654/busy-beaver/actions/runs/38829452130/job/116744580063).
This audit inspected its status and the theorem source; it did not rerun
the 160-module Coq closure locally.

The Coq endpoint is external finite-refutation equivalence. The source
explicitly makes no additional formalized independence or object-level
internalization claim. A new 253-state result must therefore be attributed
as prior work. A new smaller table must beat 253 working states with its
own blank initializer included.

## Scope and interpretation

The useful levels of evidence are distinct:

1. A finite table has the stated number of states and transitions.
2. A finite initial execution has the stated endpoint.
3. Every execution is simulated by the intended register program.
4. That program enumerates exactly the specified proof calculus.
5. Refutation in that calculus is equivalent to refutation of ordinary ZFC.
6. The requisite equivalence is provable in ZFC under explicit numerical
   codings.

An external Coq theorem establishes the stated external proposition under
its logical foundations. The user requests level 6. A missing Lean port
does not, by itself, rule out an ordinary ZFC proof; equally, a closed Coq
assumption list does not itself provide a proof-code internalization.

The new repair completes a nonvacuous *logical* bridge only. The theory
calibration, enumerator, complete machine simulation and object-level
internalization are still separate. The soundness theorem in Code254 and
the named-calculus completeness theorem were not contradicted.

The repository's 248–252-state reduced-calculus experiments have a known
finite-sort obstruction. Runtime-only and prepared-tape 252-state cores
have a different limitation: they do not include a complete blank
initializer. Complete-logic 268/269/270/279-state controls are useful
compiler measurements but exceed the public 253-state reference.

## Source ledger

`source-ledger.json` records the three user-cited commits, the newer logic
commit, pinned table hashes, exact-head CI results and primary source URLs.
The older milestones are 7910 (Yedidia–Aaronson, a stronger-theory
construction), 1919 (O'Rear, 2016), 748 (the 2017 compiler artifact),
745 (Riebel, 2023), and the later 393/335/254/253 constructions.
The 7910 machine must not be described as having exactly the same
Con(ZFC) target as the direct contradiction-search lineage.

For the report, include this README, the two new Lean files, the patches,
the replay driver, the JSON evidence/manifests, `lean_src/`, and
`LICENSE.ProveIt`. The separately downloaded historical READMEs and
theorem-source snapshots are working references, not required deliverables.

