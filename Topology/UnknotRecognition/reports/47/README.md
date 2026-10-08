# Toward quasi-polynomial unknot recognition

**8 October 2026 — ProveIt research continuation**

Start with the complete article:

[`unknot_native_orbits.pdf`](snapshot/Topology/UnknotRecognition/research/20261008_native_orbits/article/unknot_native_orbits.pdf)

Its editable TeX source, generated tables, vector figures and Makefile are
adjacent to the PDF. The detailed source, measurement and reproduction guide is
[`research/20261008_native_orbits/README.md`](snapshot/Topology/UnknotRecognition/research/20261008_native_orbits/README.md).

## Main results

- A general classical AHT interval-orbit implementation and separate local-rule
  certificate verifier, with polynomial binary-input complexity.
- A native bridge from actual normal coordinates to aggregate topology and a
  certificate for a supplied normal compressing disk, under explicit ambient
  manifold conditions.
- Exact marked-component incidence via coned orbit queries and Möbius inversion.
- A proved sparse prerequisite-pair restriction for eligible two-meridian
  searches, combined with reusable propagation and sound closed-set pruning.
- Reproducible local and whole-pipeline measurements, including regressions,
  timeouts and comparisons with independent finite geometry and Regina.
- A separate repair of inherited subprocess input loss found by the full tests.

The unrestricted quasi-polynomial recognition theorem is not proved. The
article identifies the remaining surface-search, attachment, representation,
hierarchy-depth and reset obligations, and proposes nine research priorities.
Classical results and unchanged material from the previous continuation are
attributed explicitly. This is research code with written proofs and executable
checks; formal verification and external peer review remain future work.

## Contents

| Path | Contents |
| --- | --- |
| `snapshot/` | Runnable repository subset, preserving original relative paths |
| `integration.patch` | Complete binary-capable change set against the pinned revision |
| `implementation.patch` | Smaller source/test/documentation subset for code review |
| `INTEGRATION.md` | Exact target revision and integration instructions |
| `CHANGES.json` | Every integration path, original hash and delivered hash |
| `MANIFEST.json`, `SHA256SUMS` | Checksums and sizes of the delivered files |
| `verify_bundle.py` | Standard-library integrity check |
| `LICENSE` | MIT-0 license; inherited nested license files are also retained |

The complete patch includes the implementation subset. Apply only the complete
patch for a full integration; the smaller patch is provided to make review easier.

From this directory:

```sh
python3 verify_bundle.py
cd snapshot/Topology/UnknotRecognition/fast
python3 -B -m unittest discover -s tests -v
python3 -B normal_orbit_research/replay_saved_examples.py
```

The recorded environment is Python 3.12.14. Ordinary runtime modules require
only the standard library. Native geometry controls use the Regina distribution
7.4.1 (engine version string 7.4); figure regeneration uses matplotlib 3.10.8.
The full portable suite includes sibling historical oracle packages from
reports 24, 26 and 28. Some unrelated inherited benchmark scripts require Git
history; the three new benchmark drivers and the full tests do not.

Primary raw measurements, large geometry-audit output, representative replay
certificates, initial failure logs, repaired full-suite logs and isolated
snapshot verification logs are all retained in the relevant research and
results directories. SHA256 checks provide integrity checking, not external
authorship or theorem certification.
