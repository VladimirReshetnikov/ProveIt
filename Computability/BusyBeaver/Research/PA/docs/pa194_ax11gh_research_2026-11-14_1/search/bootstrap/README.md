# Bounded bootstrap repair searches

No complete source frame was found. These searches do not establish a general
lower bound, and resource-limited runs are not certified nonhalting.

The base is the earlier 193-state runtime core, whose clean-frame source
contracts do not solve its blank initialization. The frozen native table has
SHA-256 `50f7be44afb63293365270a83111299247d12d140614e4b4c9a52786163acb53`.
The 420-row proposal list combines 346 earlier one-step-neutral proposals
with 74 new two-sided stuttering proposals. Simultaneous proposals are not
automatically valid runtime transformations; any startup hit would still
need the complete source proof.

## Recorded results

| Search | Candidates | Runs | Transitions | Halts | Certified rays | Capped | Frames |
|---|---:|---:|---:|---:|---:|---:|---:|
| Compatible two-row choices | 86,361 | 16,667,673 | 5,299,181,535 | 174,344 | 16,482,658 | 10,671 | 0 |
| Marker-rescue template | 191 | 36,863 | 148,433,302 | 347 | 35,775 | 741 | 0 |

All 193 controls are tried as start states. The first search uses a 500,000
transition bound per run; the second uses 200,000. Both also cap head magnitude
and number of one-cells at 20,000. Frame matching compares the whole finite
tape support, accepts any of the 3,673 source sites, permits arbitrary values
of all nine registers, permits extra header padding, and requires a nonempty
spare list. A certified ray is a monotone cycle reading zero strictly beyond
the current finite support, so it cannot return to a source frame.

The marker-rescue template sets native `122/0 = 0 L helper` and
`helper/0 = 0 R 16`; every helper other than 122 and 16 is tested.

The joint three-row template instead sets `122/0 = 0 R helper`,
`helper/1 = 1 L 16`, and tries every working target, write bit, and direction
for `helper/0`. It excludes 23 arithmetic-box controls and 122 as helpers:
169 × 193 × 4 = 130,468 proposals. The radius-six source contexts and 100-step
positive two-sided reconnection check reject all proposals. This is a local
screen, not 130,468 full blank-start simulations.

## Replay

Python 3 and a C++17 compiler are sufficient. From the enclosing packet:

```bash
python3 search/bootstrap/replay.py --suite all --out /tmp/pa-bootstrap
```

All required input files are bundled. Output goes to the requested directory.
The full pair search can take several minutes depending on the computer.
The recorded `.log` and empty hit files retain the original results. The
smaller `joint_marker_search.log` is an earlier restricted check; the final
complete-template result is `joint_marker_search_all.log`.

## Attribution

The runtime table, whole-frame matcher, and corrected radius-six source
contexts come from the pinned ProveIt packet
`Computability/BusyBeaver/Research/PA/docs/pa_sub194_research_2026-11-13`.
The two-row enumeration and marker templates are new in this investigation.
The earlier proposal pool and the new stuttering pool are distinguished in
the neighboring `state_reduction/` packet. Original notices and licenses are
retained in the enclosing `licenses/` and that packet's `licenses/`.
