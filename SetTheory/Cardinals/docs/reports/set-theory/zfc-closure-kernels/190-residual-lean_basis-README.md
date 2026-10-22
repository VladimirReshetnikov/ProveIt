# Shared Lean implication basis with a two-detachment S extension

Baseline: ProveIt `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

This change appends K and Peirce aliases plus a two-MP S theorem to the exact
maintained dominated core, introduces a pure unrestricted basis adapter, and
retains the original Tarski bridge tail. The numerical DomRho8 adapter is
unchanged. All original four public basis theorem types and the Implicational
constructor/projection calling conventions are preserved.

The unrestricted adapter and unchanged Tarski wrapper are inherited from the
archived shared-proof-core proposal. Its previous five-MP S extension is
replaced by the two-MP use of d34, d57 and d55 explained in the report. This
packet does not claim priority for the underlying implicational identities.

## Measurements

The selected proof sources (current DominatedImplication plus Lukasiewicz,
compared with proposed DominatedImplication, ImplicationalBasis and
Lukasiewicz) change from **42,454 to 18,096 bytes**, and **811 to 411 lines**.
The 24,358-byte reduction includes the new module. It does not include
generator/template or audit-client bytes. The new module increases the
endpoint import closure by one under this isolated change.

The shared schema count is **164 to 60 MP applications**, or **165 to 61**
including the unchanged one-MP `lift_right`. The earlier shared-basis proposal
used 63 applications, excluding `lift_right`. These are shared schema counts,
not expanded term sizes or minimality bounds.

## Contents

- `BusyBeaver/ZFC/`: the three proposed proof files.
- `repo_overlay/`: the five repository-relative changes, including the
  synchronized producer and its pinned basis template.
- `integration.patch`: the corresponding patch against the pinned commit.
- `BasisPublicAudit.lean`: exact constructor, projection and public theorem
  clients, independent of the proof-body implementations.
- `DownstreamPublicAudit.lean`: axiom reports for the unchanged semantic and
  numerical clients, including `KCodeDom.cdom_iff_c222`.
- `verification/`: actual baseline/candidate compiler outputs and source
  bindings from the completed fresh checks.
- `source_metrics.json`: selected proof-source measurements.

## Checks completed

The baseline compiled 14 project modules and two typed audit clients; the
candidate compiled 15 project modules and the same two clients. All 33
compilations passed with fresh project objects. The six generic exports and
four unrestricted exports report no global axioms. The ten named public and
downstream client profiles match the baseline exactly. The portable comparison
script also verifies every compiler log digest and the recorded provider-object
bindings. See `verification/result.json` and `verification/axiom-comparison.json`.

The synchronized generator reproduces the proposed core and the unchanged
numerical adapter byte for byte. Its explicit syntax audit checks all six
public targets and 61 MP applications including the lifting rule.

## Reproduce

Use a pristine checkout at the pinned commit, Lean 4.32.0, and fresh output
directories. The source checkout is never modified.

```sh
python3 check_lean.py --repo /absolute/path/to/ProveIt \
  --lean /absolute/path/to/lean-4.32.0/bin/lean \
  --out /tmp/k215-two-detachment-lean
python3 compare_axioms.py --results /tmp/k215-two-detachment-lean \
  --out /tmp/k215-two-detachment-lean/axiom-comparison.json
python3 check_regeneration.py --repo /absolute/path/to/ProveIt \
  --out /tmp/k215-two-detachment-generation
git -C /absolute/path/to/ProveIt apply --check /absolute/path/to/integration.patch
```

The compiler driver checks fresh baseline and candidate source closures and
the typed clients. It uses the shared proof-build lock and does not load
previously compiled project objects. The generator diagnostic checks explicit
MP/guard syntax and exact outputs; it is not a substitute for kernel checking.

The full K215 endpoint has not been rebuilt for this overlay. Adoption still
requires affected descendant builds and the original endpoint clients under
the repository's normal source/object binding policy.
