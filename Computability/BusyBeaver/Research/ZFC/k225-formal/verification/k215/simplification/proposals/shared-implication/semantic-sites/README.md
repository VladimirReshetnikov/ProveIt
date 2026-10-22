# Semantic site contracts for K215

Proposal baseline: ProveIt `2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`.

This package supplies a replacement `KSim.lean`, a reviewable patch, typed legacy
and semantic API clients, and a reproduction script. It advances the already
proposed `SiteSpec` interface from
`k225-formal/verification/k215/simplification/proposals/further-simplifications/runtime_contexts/README.md`
(lines 80–82 at the baseline). The architectural idea is credited to that earlier
proposal; the concrete code and central simulation refactoring here are new.

## What changes

The existing Boolean site checker, its fuel, and `Covered` are unchanged.
`SiteContract M entry Q e` records the exact primitive effect from an arbitrary
entry configuration. `SiteSpec` fixes the entry to the maintained `start Q` and
adds `Q.length <= 48`. Register bounds, branch validity, overflow, gap growth,
and the exact `tgtConf` definitions are preserved.

`checkEdge_sound` converts an existing successful finite check to `SiteSpec`.
`SemanticCovered` supplies these contracts for the actual `walk` and `consume`
results. `semantic_covered_of_allSites` accepts any sound finite leaf checker,
so shared contracts can be introduced for one primitive family while retaining
the existing checks for every other family. The audit includes this mixed case. The new `semantic_halts_iff` consumes semantic coverage and the terminal
row condition directly, without requiring the symbolic evaluator or `BoxLemmas`
as premises. The existing `halts_iff` and other public simulation theorems remain
wrappers with exactly their original types; the old stop theorem also retains
its lack of a `BoxLemmas` assumption.

`SiteContract.prepend` is the integration point for the checked decoder prefix:
a uniform prefix reachability theorem and a positive primitive-and-return
contract compose to a full site contract. Its prefix may take zero steps. The
returning tail must take at least one step, which the reverse-halting induction
requires. The halt branch preserves the explicit terminal-row hypothesis because
the existing finite checker only recognizes state 230.

## What this does not yet establish

This package alone does not prove shared primitive-and-return contracts or
replace the 6,176 K215 branch outcomes. It does not claim a shorter endpoint
build, fewer states, or a fresh complete K215 endpoint audit. The immediate
change grows KSim from 356 to 482 lines: it removes a coupling that prevents
semantic decoder proofs from feeding the maintained simulation. Savings are
expected only when shared primitive contracts replace repeated per-leaf
certificate work. No semantic contract is converted backwards into the old
fixed-fuel Boolean checker; no completeness claim for that checker is made.

## Reproduce

Run, with the repository checkout and Lean 4.32.0 available:

```
python3 verify.py --repo /path/to/ProveIt --lean /path/to/lean
```

The script creates an isolated build under this package, copies the thirteen
required project sources, compiles the baseline plus a typed legacy client, and then overrides only
`KSim.lean` in a second tree. The exact same legacy client and a semantic API
client are both compiled against the changed module. A machine-wide lock and
`-j1 -M12288` keep the build serial. Source, import-object, output-object,
command, toolchain and audit-file hashes are recorded. Only Lean's `Init`
is external; no mathlib is needed. The source checkout is never modified.

The audit checks the complete legacy theorem signatures, the new semantic
endpoint signature, a zero-duration prefix composition, mixed old/new coverage, and axiom reports.
The complete maintained K215 endpoint must still be rebuilt against the changed
module before a production replacement is recorded as endpoint-verified.
