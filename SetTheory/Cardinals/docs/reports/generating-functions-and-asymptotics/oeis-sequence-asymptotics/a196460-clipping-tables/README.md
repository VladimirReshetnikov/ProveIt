# Zero auxiliary clipping tables

Exact counts and all orders asymptotics of A196460. A standalone, unnumbered
research article dated 4 October 2026.

## Deliverables

- `article.pdf`: the complete 16-page article
- `article.tex`: self-contained LaTeX, byte-identical to `manuscript/article.tex`
- `inputs/asymptotics`: complete accepted proof/source/evidence packet
- `inputs/independent-audit`: complete fresh independent mathematical audit
- `inputs/closure-dependencies`: pinned one-positive-witness and closure proof,
  accepted earlier audit, and their original source manifests
- `tools/`: separately owned presentation-only build and release tools
- `qa/`: preservation inventories, build/visual evidence, and review records

The PDF proves the complete zero-versus-one classification, exact count
C_n=1+a_n, weighted bipartite graph interpretation, all fixed-order P/L/D
expansions and recurrences, explicit uniform tail bound, finite-proxy inverse
error, sharp signed remainders, rarity fraction, and exact threshold inversion
including C_0=2. Two diagrams explain the boundary marks and the thin inverse
threshold interval. It attributes A196460 and the 2023 relational-model source.

The mathematical additions relative to the accepted asymptotic proof packet are
an immediate sharp logarithmic remainder (equation 26) and the rectangular
count C_{p,q} in the further questions. Their short proofs are explicit in the
article and are included in independent manuscript acceptance. The remark on
higher-dimensional closure and one witness restates the retained native proof.
The manuscript makes no convergence, growing-order-uniformity, exact-floor-of-a-
truncated-inverse, novelty, physical, or formal-verification claim.

## Exact identity pins

The standalone and manuscript LaTeX SHA-256 is
`6569cdc99dc96bdf53c819d18ecfccad030771b5a1795b07c7deb02b3e7a901c`.

The accepted PDF SHA-256 is
`2a95d839ec43787f55cd73a7cb8e6a65635210388398f33b30396910cc128910`.

The external manuscript-pin-map SHA-256 is
`f330e99fd48b98ce57b1b205416d98acda22dbff63ca6ab2c0a769919120250d`.

The exact build-dependency-lock SHA-256 is
`01477b108b9576ce8fe0fc3ee516e1c106e684940d335a6fe694c675e5e60f79`.

The final release manifest and source/evidence ZIP have detached pins in the
release receipt supplied alongside the archive. A release manifest deliberately
excludes its own bytes and self-metadata; it does not attempt a circular seal.

## Presentation-only replay

Read `tools/README.md` and all tools before execution. From this release run,
using an absolute fresh output directory outside the release and all protected
source/report trees:

    python3 -I -S -B tools/release.py check-inputs
    python3 -I -S -B tools/build_article.py \
      --pins-sha f330e99fd48b98ce57b1b205416d98acda22dbff63ca6ab2c0a769919120250d \
      --dependency-lock-sha 01477b108b9576ce8fe0fc3ee516e1c106e684940d335a6fe694c675e5e60f79 \
      --require-packaged-match --output-dir /absolute/fresh/build-directory

The exact dependency lock covers 264 recorded TeX/system inputs and seven
interpreter/executable entries. It does not lock shared libraries, Python's
standard library, or the full operating system. A changed environment is
refused, not silently substituted. The bundled TeX source may be used for
ordinary local typesetting separately, but that would not constitute this
locked replay. The owned builder creates a fresh TeX format, disables shell
escape, records all three compilation passes plus the format pass, extracts
text, and renders all 16 pages. `qa/tool-build-initial` retains the complete
successful locked record. Every raster matches the earlier bootstrap exactly.

The scientific code under `inputs/` is inert historical evidence. It is never
imported or run by these presentation tools. In particular this build does not
run source algebra programs, interpreters, physical/trajectory simulators,
saved schedules, or Lean. The recorded numerical evidence is the existing
accepted source and fresh audit evidence, not a newly rerun scientific result.

## Safe archive extraction and preservation

Authenticate the detached release-manifest pin before verifying or extracting:

    python3 -I -S -B tools/release.py verify --manifest-sha256 MANIFEST_PIN
    python3 -I -S -B tools/release.py extract \
      --manifest-sha256 MANIFEST_PIN --archive /absolute/archive.zip \
      --output-dir /absolute/fresh/extracted-directory

The owned extractor verifies all archive bytes before creating output and
restores file/directory modes and nanosecond modification times from the
manifest. Generic ZIP extractors may not restore those times. Archive members
have deterministic ordering, timestamps, compression, and file modes; the
manifest carries the finer metadata. Symlinks, hardlinks, path traversal,
duplicates, noncanonical outputs, and unexpected inventory are rejected.

The two full mathematical packets and the four selected closure-dependency
files are retained with their original bytes, modes and nanosecond mtimes.
Originals were not written, chmodded, or retimestamped. Access times are outside
the preservation claim. The source's authentic 132 historical Report69/70
changes, split 44/88, remain intact; all 62 historical core entries were
unchanged. These facts do not assert whole-historical-interval preservation
of those then-active report trees. Packaging has its own separately recorded
994-entry original inventory. Its exact scope and observation interval are in
`qa/tool-original-inputs-before.json` and the subsequent verification receipts.
No claim of WORM enforcement or external trusted timestamps is made.

## Primary references

- OEIS A196460: https://oeis.org/A196460
- Svatos, Jung, Toth, Wang and Kuzelka, On Discovering Interesting Combinatorial
  Integer Sequences (2023), arXiv:2302.04606v1, Appendix A.1, Table 3, printed p.32:
  https://arxiv.org/abs/2302.04606v1

No external submission, repository publication, or Library upload is part of
this release preparation.
