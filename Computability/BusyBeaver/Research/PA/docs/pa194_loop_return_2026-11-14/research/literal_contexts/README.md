# Literal arithmetic-context reduction search

This supplement refines the arithmetic-state contexts of **PA194LCG** and
reruns three state-deletion templates. It found **no smaller machine**.

The native table SHA-256 is
`bdbfb392b408dd729899f07ad38de92b86f5d76bbdb87e7a12e5f1137f3d8047`.
All input source artifacts are pinned to ProveIt commit
`8d31445d858761a8f6150c2e5012adae8895e932` or to the accompanying new LCG
construction derived from that snapshot.

Evidence filenames containing `LCFC` retain the construction-stage label for
this exact PA194LCG table; the native hash above binds their identity.

## New envelope

At radius six, the generic window closure has **271,895** configurations.
The literal symbolic source/list analysis gives **49,297**, all included
in that generic closure. For the 23 arithmetic controls, the corresponding
counts are **119,150** and **18,570**. Every working control remains present.

The generator replays all **4,778 outcomes at 3,671 source sites**, including
unary-scan and arbitrary-list interiors, and the exact **57,870-step blank
startup**. The independent literal engine takes 1,105,118 symbolic steps
(maximum 385 per outcome). No arithmetic-box oracle is assumed. The source
and arithmetic calibration to PA remain the separate obligations stated in
the main report.

An implementation check also performed 1,200 full literal command runs,
551,331 transitions in total, with no missing windows. Those finite samples
are not the proof of universal coverage; see `context_envelope_notes.md`.

## Completed bounded searches

| Template | Coverage | Bound | Hits |
|---|---:|---|---:|
| Two-row quotient | 18,721 unordered control pairs | One old step, at most 100 replacement steps | 0 |
| Two-sided stuttering quotient | 18,721 unordered control pairs | At most 12 old steps, 128 replacement steps | 0 |
| Separate incoming-edge replacements | All 193 non-start deletion targets | At most 24 old steps, 256 replacement steps | 0 |

The first two searches made 26,213,260 and 26,387,880 first-action trials,
and checked 174,903 and 177,086 joint row combinations respectively. The
incoming-edge search permits the actual halt label among possible first
successors, and excludes detours through any removed or rewritten row.

The supplement also retains a fresh coarse-envelope quotient run on this
new table and a deeper targeted 83/190 stuttering check. They likewise found
no candidate. These are finite-template results, not minimality theorems.

## Reproduce

From this directory inside the delivered archive, with Python 3 and a C++17
compiler:

```sh
python3 reproduce_context_research.py --output /tmp/lcg-context-replay
```

This regenerates the literal envelope, checks the finite samples, compiles
the three search programs, reruns the primary three templates, and writes a
fresh receipt. It uses the package's `machines/PA194LCG` and
`verification/reference` directories. The symbolic envelope generation is
the slowest step and may take several minutes.

`--reuse-contexts` uses the frozen, hash-checked envelope instead of rerunning
its symbolic derivation; the receipt explicitly records that omission.
`--package PATH` selects the enclosing package when this directory is staged
elsewhere. The output directory must differ from this recorded-evidence
directory.

Original vendor attribution is retained in the enclosing package's licenses.
`joint_return_merge.cpp` is copied from the supplied sub-194 study;
`stutter_merge_contexts.cpp` adds only an optional pair filter to the supplied
AX11GH synthesizer; `edge_delete_contexts.cpp` extends the supplied LC
synthesizer with explicit context input and the actual halt target. The
literal context-envelope collector and its sample checker are new here.
