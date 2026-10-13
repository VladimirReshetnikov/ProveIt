# Integrating the Euler/group terminal extension

This package adds an optional, source-bound certificate of the handlebody
components obtained by cutting along a supplied normal surface. It is pinned
to ProveIt commit:

```
9bacc258bff4b34b4a92b6fa71d290ba5e60ea26
```

The implementation and replay checker use the Python standard library under
the upstream Python 3.10+ contract. Regina is an optional development oracle;
it is not imported by the new production terminal or certificate replay tool.
The article explains the topological theorem, the restricted source compiler,
the deterministic elimination policy, and the remaining complexity questions.

## 1. Review and apply the change

The patch is `integration/euler_group_terminals.patch`. Its complete file
overlay is rooted at `integration/overlay/Topology/UnknotRecognition/fast/`.
Both represent the same eleven-file change:

| Kind | Files relative to `Topology/UnknotRecognition/fast/` |
| --- | --- |
| Six new production modules | `fastunknot/free_group_elimination.py`, `fastunknot/free_group_elimination_verify.py`, `fastunknot/source_cut_group.py`, `fastunknot/source_cut_group_verify.py`, `fastunknot/normal_cut_groups.py`, `fastunknot/normal_cut_groups_verify.py` |
| Three new test modules | `tests/test_free_group_elimination.py`, `tests/test_source_cut_group.py`, `tests/test_euler_group_terminal.py` |
| Two edited production modules | `fastunknot/normal_cut_handlebodies.py`, `fastunknot/normal_cut_handlebodies_verify.py` |

Use a clean checkout at the pinned commit, or create an isolated worktree from
an existing clone. Replace the illustrative absolute paths below with your
own paths. From the clone:

```sh
git worktree add -b research/euler-group-terminals /path/to/ProveIt-euler-group 9bacc258bff4b34b4a92b6fa71d290ba5e60ea26
```

From `/path/to/ProveIt-euler-group`, check the patch before applying it:

```sh
git rev-parse HEAD
git apply --stat /path/to/ProveIt_Euler_Group_Terminals_2026-10-12/integration/euler_group_terminals.patch
git apply --check /path/to/ProveIt_Euler_Group_Terminals_2026-10-12/integration/euler_group_terminals.patch
git apply /path/to/ProveIt_Euler_Group_Terminals_2026-10-12/integration/euler_group_terminals.patch
git diff --check
git status --short
```

The overlay is an alternative installation method for that same pinned
checkout. Copy its `fastunknot/` and `tests/` contents into the matching
directories under `Topology/UnknotRecognition/fast/`, preserving paths and
reviewing the two replaced files. Apply the patch or copy the overlay once.
Neither method is intended to replace an unrelated version of the project.
No changes to packaging metadata or the public command-line recognizer are
required by this extension.

## 2. API and certificate dispatch

The existing API keeps `group_fallback=False` by default. Its prior geometric
path therefore retains its existing behavior. To enable the new terminal
after an inconclusive geometric attempt:

```python
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies

result = normal_cut_handlebodies(
    triangulation,
    coordinates,
    group_fallback=True,
    record_certificate=True,
    max_cycles=None,
)
if result["status"] == "COMPLETE":
    accepted = verify_normal_cut_handlebodies(
        triangulation, coordinates, result["certificate"]
    )
    if not accepted:
        raise ValueError("source certificate replay failed")
    census = result["census"]
```

Here `triangulation` is the existing finite tetrahedral face-pairing object,
and `coordinates` contains seven nonnegative normal coordinates per
tetrahedron. The maintained source validator checks compactness, connectedness,
orientability, the one-torus-boundary contract, normal matching equations and
quadrilateral constraints. It does not prove provenance from a knot diagram.

The direct entry point avoids running the geometric attempt first:

```python
from fastunknot.normal_cut_groups import normal_cut_group_handlebodies

result = normal_cut_group_handlebodies(
    triangulation,
    coordinates,
    record_certificate=True,
    max_cycles=None,
)
```

The certificate schema is `normal-cut-euler-free-v1`. It binds the source
parallelity and boundary traces, the complete cut presentation, the component
freeness proofs and the Euler-checked census. The existing
`verify_normal_cut_handlebodies` dispatcher recognizes this schema and calls
`verify_normal_cut_group_handlebodies`; existing geometric schemas remain
supported. Replay reconstructs the source-dependent data and follows the
supplied proof. It does not rerun the elimination search. A certificate is
produced only when `record_certificate=True` and the result is `COMPLETE`.

### Scope and budgets

`COMPLETE` certifies an **unmarked handlebody census of the entire source cut**,
including binary families of isolated balls. It provides component genera,
counts and the exact Euler check. It does not supply marked successor maps,
geometric handle slides or a standalone unknot verdict. In particular, even
an `all_balls` census requires the separate surrounding recognition argument
and its hypotheses before it can establish a statement about a knot.

The implemented compiler requires product disk parallelity bases. Unsupported
bases, exhausted orbit budgets and a stalled no-growth word policy return
`INCONCLUSIVE`. Freeness combined with a positive second Betti number also
returns `INCONCLUSIVE`. None of these outcomes certifies a knot or a nonfree
group. The Euler guard is essential: freeness alone does not certify a
handlebody when closed summands may be present.

Each of the two enabled fallback stages receives its own `max_cycles`
allowance. Thus `group_fallback=True` can spend up to twice the orbit discovery
allowance of one stage; it is not a single shared global budget. Within the
direct group terminal, the parallelity and moment-boundary steps share that
terminal's allowance. Word processing has its own finite deterministic policy
and is not counted in `max_cycles`. The `check` callback is propagated through
both stages for cooperative cancellation. The replay option `max_operations`
counts the recorded operations specified by the selected verifier; it is not
a bound on all Python instructions, wall time or memory.

## 3. Replay the delivered packets

After integration, run this from the unpacked delivery directory:

```sh
python tools/verify_packets.py --fast-root /path/to/ProveIt-euler-group/Topology/UnknotRecognition/fast --output /path/to/packet_replay.json
```

The default input is this package's `certificates/group/` directory. To check
one archived packet, including the detailed figure-eight example:

```sh
python tools/verify_packets.py --fast-root /path/to/ProveIt-euler-group/Topology/UnknotRecognition/fast --packets certificates/figure_eight.json
```

The tool calls only the existing certificate-verifier dispatcher. It records
packet hashes, schemas, individual results and hashes of the loaded native
source modules. Exit status is zero only when every selected packet verifies.
Empty directories, malformed packets, exceptions and rejected certificates
fail the invocation. Optional `--max-operations N` applies a separate recorded
operation cap to each packet.

Two archived packet layouts are supported: `{source, certificate}`, with
`source` containing `id`, `triangulation` and `coordinates`; and the detailed
`{id, triangulation, coordinates, result}` layout, with a `COMPLETE` result
containing its certificate. The loader rejects duplicate object keys,
nonfinite numbers and floating-point literals. The established exact integer
codec accepts literal JSON integers or explicit signed hexadecimal strings
in the specified integer fields; it rejects booleans and decimal strings as
integer substitutes. The tool neither changes Python's decimal conversion
limits nor expands binary sheet families.

`certificates/euler_defects.json` contains deliberately refused positive-Euler-
defect examples, not accepted handlebody packets. Its dedicated reproduction
tool is `tools/audit_euler_defects.py`. See its `--help` and the article; do not
feed those refusal records to the successful-packet replay tool.

## 4. Tests and development audits

From the integrated `Topology/UnknotRecognition/fast/` directory, run the three
new focused test modules:

```sh
python -B -m unittest discover -s tests -p test_free_group_elimination.py
python -B -m unittest discover -s tests -p test_source_cut_group.py
python -B -m unittest discover -s tests -p test_euler_group_terminal.py
```

For the complete native suite, use the repository's existing discovery gate:

```sh
python -B -m unittest discover -s tests
```

Archived test logs and reproducible audit results are in `results/`. The
independent freeness audit checks explicit substitutions, original relators,
survivor maps, nonabelian finite-group homomorphism counts and selected Regina
recognitions. The native audit compares the archived source cases and literal
Regina cuts where its explicit expansion cap permits. These audits complement
the mathematical proofs; corpus coverage and passing tests do not establish
a general recognition algorithm or a quasi-polynomial runtime theorem.

Optional oracle audits use Regina. The upstream extra specifies
`regina>=7.4.1,<8`; actual audit runtime versions are recorded in the delivered
JSON reports. `requirements.txt` documents this optional installation and
intentionally installs no dependency for production or replay. Do not run the
independent freeness audit with `python -O`, because its assertions are part
of the audit checks. Each audit tool provides explicit source and output path
arguments through `--help`; none requires an implicit checkout location.

## 5. Deferred-forest integration is a separate merge

The preceding incoming deferred-forest package adds `forest_strategy` and
also modifies `fastunknot/normal_cut_handlebodies.py`. This delivery adds
`group_fallback` to the pinned main-branch version of the same file. The two
patches therefore require a deliberate source merge and a fresh combined
test run. This package does not supply or claim a compatible combined patch.

`comparison/deferred/` contains attributed comparison inputs used only in
isolated audit runtimes. It is not an additional production overlay. Its
reported union coverage records what either independently tested path can
certify on those archived inputs; it does not demonstrate an integrated
`forest_strategy` plus `group_fallback` implementation. A later merge should
define the portfolio order, preserve both options and verifier schemas, and
state whether each attempt receives its own orbit allowance or a newly
implemented shared budget.
