# K215: smaller proofs and quotient detachment

Research packet prepared for the ProveIt project, 21 October 2026.
Repository baseline: `53269bcab1efc0f82d3022645bd7cf0c22d84959`.

**No verified 214-state machine is claimed.** The positive results are a
checked further simplification of the existing numerical implication proof
and a checked equiconsistent extension of its detachment rule. The physical
experiments document why the first implementation does not improve the state
count.

## Read first

`report.pdf` is the complete research article; `report.tex` and `results.tex`
are its editable LaTeX sources. The report distinguishes prior main-branch
and incoming work, new checked theorems, ordinary arithmetic arguments,
finite regressions, and bounded searches.

| Component | Result | Scope |
|---|---|---|
| `proof_simplification/` | Lean DomRho8: 30,114 → 26,709 bytes; unchanged `rho8_all` and `cdom_iff_c222` | Fresh 13-module local closure; exact generator reproduction and patch |
| `proof_simplification/` | Direct Coq companion, 24,352 bytes | Fresh Coq 8.18.0 compilation and recursive `coqchk`; larger than the 22,673-byte reflected production version |
| `quotient/` | QMP: accept `h / 4 = P(a,b)` from valid `a,h` | Actual numerical decoder; irreflexivity and two distinct elements; all valuations |
| `quotient/` | `Q222 F ↔ BProv ZFCax_s [] Form.fBot` | Lean theorem using the existing upper/lower mathematical calibration, all 110 modules freshly compiled, with 106 exact pinned upstream sources |
| `physical_research/` | 8 quotient source variants and 8 allocator-compatible lowerings | All-natural macro argument and finite full-MP regressions; best raw splice has 210 source subtrees |
| `physical_research/` | 234-state conservative allocation price | Prefix/entry checks only; not an accepted new consistency machine |
| `physical_research/` | 21-table bounded survey | No 214 result in the searched grammar; not a lower bound |

## Reproduce

Python 3.10+ suffices for the data/finite checks. Do not run Python with `-O`.
From this directory:

```sh
python3 verify.py
```

The script checks all archive file hashes and re-runs the finite semantic
and complete-MP regressions in a fresh temporary directory. Use
`--manifest-only` for an integrity check without regressions, or
`--work-dir /absolute/empty/directory` to choose the output location.

A Python PASS is not a proof-assistant kernel check. Each component's README
gives its independent clean build command. The Lean proofs were checked with
Lean 4.32.0; the direct Coq companion with Coq 8.18.0 and `coqchk`.
Toolchains are not included. Exact source inputs and build logs are included.
Full state-search commands are under `physical_research/README.md`; they
are deliberately not run by the default top-level verifier.

To compile the article, use two passes of:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Integration

1. Apply the reduced `DomRho8.lean` and generator patches after checking the
   pinned input hashes. Its principal public theorem is unchanged; the unused
   ancillary `distribution` helper is removed. Preserve a compatibility
   helper if an external consumer requires it.
2. Keep the quotient semantic modules as a research lane. The exact ZFC
   refutation equivalence is proved, but no quotient binary-machine endpoint
   has been supplied.
3. For another short incremental 215-state proof, integrate the existing
   CM215 exact-table adapter from incoming work. Its proof depends explicitly
   on the accepted K215 endpoint. The recommendation and credit are detailed
   in the report; CM215 is not a newly discovered candidate here.
4. Keep the 234-state price and bounded negative searches under research,
   not under accepted candidates. A smaller binary table needs quantified
   runtime and blank-start proofs before it can establish the user's goal.

The original complete 185-module binary-machine endpoint was not freshly
rebuilt in this packet. The separate internal-PA endpoint is not claimed.
No equality of all theorem sets is inferred merely from refutation
equivalence.

## Provenance and notices

Upstream source, candidate tables, generator code, and licenses are preserved
inside their component directories. `NOTICE.md` describes the packet's
additions. `MANIFEST.json` binds every delivered file except itself.
