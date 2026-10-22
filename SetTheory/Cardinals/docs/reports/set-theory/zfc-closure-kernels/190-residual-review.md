# Independent K215 architecture and shared-basis review

Review basis: ProveIt commit `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.
All paths below are relative to that checkout unless identified as packet paths.
This note separates fresh source inspection from archived compiler evidence and
from the newly checked, small proof-extension audit.

## 1. The maintained source is the baseline

The phase-twelve Lean endpoint has 179 project modules, 2,129,439 source bytes,
and 41,170 physical source lines. The primary phase-twelve inventory also
includes five decoder-prefix modules, for 184 modules. A fresh independent
hash comparison in this review found that all 184 materialized source files
match that inventory exactly. Traversing the recorded imports from
`BusyBeaver.ZFC.KEndpoint215` independently reproduces the 179-module count and
the byte total. These are source measurements including documentation and
literal data, not compiled proof sizes.

The phase-twelve compiler record describes 15 fresh module compilations and
169 source/import/object-bound reused providers. Both endpoint clients were
compiled afresh. Its separate legacy compatibility run covers 67 project
modules and two clients; the two scopes together contain 199 project modules.
It would be inaccurate to call this a fresh 179-, 184-, or 199-module build.
The raw saved endpoint audit logs report precisely the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound` for the exact halting and
nonhalting endpoint statements. This review read those logs; it did not
recreate their proof objects or repeat the full endpoint compiler run.

The current Rocq `DomRho8.v` is the 22,673-byte version described by
`verification/k215/simplification/phase2/rho8-global/rocq`. Its record has seven
fresh downstream compilations, 230 unchanged reused objects, four closed
endpoint assumption reports, and a focused recursive kernel check of
`K215F.DomRho8`. The full recursive 237-module dense-endpoint audit belongs to
the original baseline and is retained separately. The older
`simplification/rocq/source-bindings.json` describes a 23,678-byte predecessor;
it is not the correct hash source for the currently maintained file.

### A consequential merge distinction

Commit titles refer to a shared implication basis, but that proposal is not
installed in the pinned maintained source. The maintained
`Lean/BusyBeaver/ZFC/Lukasiewicz.lean` remains 28,731 bytes and 524 lines, with
107 private declarations `cd_0` through `cd_106`. The shared-basis versions were
preserved as inert inputs under phase twelve's `upstream-merge/inputs`.
The explanatory `upstream-merge/README.md` explicitly states that the checked
proof sources and producer were retained.

Consequently, adopting a shared basis and checking it against the current
closure is useful additional work. Merely reporting the merge commit as an
already verified production simplification would be wrong. The concept of
sharing the basis itself is prior work in the repository and should be credited
as such; the new two-MP S extension is a further local improvement.

## 2. Independent mathematical check of the two-MP extension

Write implication as an arbitrary binary operation. The current generic core
already proves the following three schemes, called `d34`, `d55`, and `d57`:

\[
 ((p\to q)\to(r\to s))\to((p\to s)\to(r\to s)),
\]
\[
 (p\to q)\to((r\to p)\to(r\to q)),
\]
\[
 (p\to q)\to((r\to p)\to(s\to(r\to q))).
\]

Fix `a`, `b`, `c`, and put

\[
 X=b\to c,\qquad U=a\to X,\qquad
 V=(a\to b)\to(a\to c).
\]

The instance `d57 X c a (a → b)` is

\[
 (X\to c)\to(U\to V).
\]

The instance `d34 X c U V` has that formula as its antecedent. One application
of modus ponens therefore yields

\[
 (X\to V)\to(U\to V).
\]

The instance `d55 b c a` is `X → V`. A second application of modus ponens gives
`U → V`, namely the S scheme

\[
 (a\to(b\to c))\to((a\to b)\to(a\to c)).
\]

There are no hidden order side conditions in these three derived schemes.
The argument works for every carrier, binary implication operation, and
theorem predicate closed under the stated modus-ponens rule. It assumes neither
injectivity of implication nor a falsity constant. No semantic classical
principle enters this extension.

The independent file `audit_work/TwoMPSAudit.v` checks these substitutions in
Coq 8.18.0. Its compilation succeeded and printed `Closed under the global
context`. Its exported theorem explicitly quantifies over modus ponens and
the three schematic premises. This checks the extension's composition; it
does not independently reprove the 58-step antecedent derivation or the
complete machine endpoint. The main packet's shared-core checks have that
separate responsibility.

The result is a two-MP extension of this existing lemma basis. It is not a
claim that S has a two-step proof directly from the raw single axiom, nor that
the whole implicational proof is globally shortest. The earlier shared-core
prototype used five additional MP applications to construct S, including its
exchange helper.

## 3. Source and API review of the new Lean overlay

The independently reviewed overlay is
`root_work/lean_basis/BusyBeaver/ZFC`. It preserves every byte of the current
generic core through `lift_right`, then exports K and Peirce as aliases of
`d12` and `d18`, and adds the two-MP S theorem. The new `ImplicationalBasis`
module specializes the restricted interface using the relation that always
holds. The four public declarations remain in namespace `Lukasiewicz`.
Their types agree with the old `k`, `peirce`, `composition`, and `s` declarations,
up to whitespace. The Tarski bridge section of the old `Lukasiewicz` file is
byte-for-byte unchanged in the smaller facade.

The specialization uses `below x y := True`; its reflexivity and the two
operand-growth laws are immediate. Its restricted rho8 premise is exactly an
instance of the old unrestricted rho8 hypothesis, with argument reordering
`(a,b,c,u)` to `(c,u,a,b)`. Thus the specialization does not strengthen the
unrestricted client's axioms.

| Source group | Maintained baseline | Reviewed overlay | Difference |
|---|---:|---:|---:|
| Generic dominated core | 13,723 bytes / 287 lines | 14,356 bytes / 306 lines | +633 bytes / +19 lines |
| Unrestricted basis and Tarski bridge | 28,731 bytes / 524 lines | 3,740 bytes / 105 lines | -24,991 bytes / -419 lines |
| Combined maintained proof sources | 42,454 bytes / 811 lines | 18,096 bytes / 411 lines | **-24,358 bytes / -400 lines** |
| Endpoint import closure, this overlay alone | 179 modules | 180 modules | +1 module |
| Endpoint source mass, this overlay alone | 2,129,439 bytes | 2,105,081 bytes | -24,358 bytes |

The split into a pure basis and Tarski facade adds one small module. It reduces
source mass and duplicated arguments; it does not reduce module count. This
distinction is useful because import-boundary reduction and proof-sharing
reduction measure different costs. These totals exclude test clients and
verification scripts. Count all three production files when reporting savings.

Within the two implication derivation DAGs, the baseline contains 164 explicit
schematic MP nodes: 58 in the dominated derivation and 106 in the independent
unrestricted derivation. The shared version contains 60: the same 58 plus the
two-step S extension. Including the unchanged `lift_right` inference adapter
gives 165 versus 61. These counts are not expanded proof-term node counts,
minimum-proof bounds, or compilation-time measurements. The unchanged Tarski
bridge is outside that comparison.

`audit_current.py` and `audit_shared_basis.py` reproduce the source and graph
measurements without executing repository scripts or invoking a proof compiler.
Their JSON outputs record the reviewed hashes. Later edits or additional
overlays require rerunning the measurements.

### Fresh focused execution and independent receipt review

The completed focused Lean run freshly compiled 14 baseline project modules
and two typed audit clients, then 15 candidate project modules and two typed
audit clients. The independent final receipt review checked all 33 compiled
sources, output objects, logs, and pre-invocation direct import-object hashes
against their current bytes. It found no failure. The baseline basis client
intentionally imports `Lukasiewicz` where the candidate imports the new pure
`ImplicationalBasis`; all its typed statements and proof bodies are unchanged.
This one import adaptation is recorded explicitly in
`lean_execution_review.json`.

All 18 named axiom profiles appearing in both runs agree, counting the reports
printed by project modules as well as the explicit clients. The three new
core exports (`basisK`, `basisPeirce`, `basisS`) have no global axioms. This
confirms the focused implementation and its consumed interfaces; the full
K215 endpoint is outside this new run. The separate residual review records
its completed 34-project-module runtime closure and one audit client.

## 4. Trust boundary and endpoint preservation

The machine-specific Lean endpoint is the closed theorem

```lean
BlankHalts machine215 ↔ BProv ZFCax_s [] Form.fBot
```

Its nonhalting statement is obtained by applying `not_congr`, giving

```lean
(¬ BlankHalts machine215) ↔ ¬ BProv ZFCax_s [] Form.fBot
```

The Rocq endpoint uses the exact dense machine and the pinned reference's
explicit standard theory:

```coq
Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.
```

The refactor should keep these theorem types, the canonical machine table,
the initial configuration, the derivability predicate, and the numerical
calculus unchanged. It should preserve rather than weaken the unrestricted
numeric `rho8_all`, including the exceptional zero aliases that its existing
adapter handles.

The exposed endpoint theorem establishes a syntactic finite-refutation
equivalence in the external assistant. It should not be described as a newly
supplied internally arithmetized ZFC or PA derivation. The repository expressly
keeps its internal PA endpoint open. This distinction does not weaken the
claimed preserved external theorem; it prevents a change in what evidence the
new packet is said to deliver.

The Rocq environment's three imported utility axioms are not dependencies of
the four closed endpoint reports. Conversely, a Lean helper that prints no
axioms does not remove `Classical.choice` or `Quot.sound` from the downstream
model-theoretic endpoint. Recheck endpoint profiles at integration, and report
focused helper profiles and whole-endpoint profiles separately.

## 5. Prioritized follow-on work

1. **Integrate the shared basis with a synchronized producer.** The
   conservative two-MP extension retains the exact current private derivation
   and original derivation input. This is easier to bind to the maintained
   producer than switching simultaneously to the alternative six-goal proof
   data. Preserve typed clients for both old interfaces and rebuild affected
   consumers before publishing it as a production checkpoint.
2. **Finish residual site contracts by actual coverage.** Existing semantic
   interfaces and arbitrary-frame decoder prefixes are already available as
   proposals. Their value becomes concrete when the finite guards and exact
   full source continuations are discharged for every intended family member.
   Preserve positive physical progress for source steps and exact halt
   classification. A count of 135 potential role outcomes is not a proof that
   6,176 checks have been replaced. Report completed coverage separately from
   the future family-factorization goal.
3. **Give Rocq the same small proof interface.** A closed replacement for the
   numeric domination proof should preserve `DomImp` and `rho8_all` and compile
   the exact `ThmDom` caller. Reconcile generator output and metadata pins,
   then rebuild its seven downstream consumers. A focused Coq 8.18 prototype
   does not substitute for a full Rocq 9.1.0 integration run.
4. **Implement and measure the direct full-seed bridge later.** The existing
   `sharing-interfaces/calculus/DIRECT_FULL_SEED.md` already explains a
   mathematically sound route using a fresh label obtained from the interpreted
   double-negated code. Compiling it could remove the first indiscernibility
   quotient from Lean's lower chain. Its new freshness and named-bundle
   semantics proofs must be counted before claiming net source savings; the
   downstream tagged/bisimulation quotient and classical axioms remain.

The useful next step is to convert these concrete, bounded interfaces into
checked replacements. Further abstract frameworks or new certificate
representations are lower priority until their clients actually become
smaller and their original statements remain verified.

## References used in this review

- `k225-formal/verification/k215/simplification/phase12/README.md`.
- `k225-formal/verification/k215/simplification/phase12/lean/execution.tar.gz`,
  specifically `execution/inventory.json`, the two typed clients, and their logs.
- `k225-formal/verification/k215/simplification/phase12/upstream-merge/README.md`.
- `k225-formal/verification/k215/simplification/phase2/rho8-global/rocq/README.md`
  and `result.json`.
- `Lean/BusyBeaver/ZFC/DominatedImplication.lean`, `Lukasiewicz.lean`,
  `KEndpoint.lean`, and `KEndpoint215.lean`.
- `k225-formal/rocq/rocq-extension/coq/215/Correct215.v` and `CorrectDense215.v`.
- `k225-formal/verification/k215/simplification/proposals/README.md`,
  `shared-proof-core`, `semantic-proof`, and `sharing-interfaces`.
