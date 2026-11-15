# PA consistency machines: two 194-state compositions and tagged encodings

**No justified machine below 194 states was obtained.** This archive supplies two new 194-state compositions, their complete tables and relative iPRA proof, a comparison of the supplied designs, a sound alternative numerical calculus, and reproducible records of the unsuccessful reductions.

Read **`report/report.pdf`** for the complete mathematical report. Its editable source is **`report/report.tex`**, with included fragments in the same directory and in `research/tagged3/`.

## Concrete machines

| Machine | Working states | Source instructions | Branch outcomes | Exact blank startup |
| --- | ---: | ---: | ---: | ---: |
| PA194LCAX11GHF | 194 | 3,671 | 4,778 | 57,870 steps |
| PA194LCAX11GHSF | 194 | 3,668 | 4,774 | 57,712 steps |

Each uses one two-way infinite tape, symbols 0 and 1, an initially all-zero tape, head coordinate zero, and a separate halt control. The complete dense table is `machines/<name>/machine.tm`; each row has `state read write direction next`. Dense start is **0**, working controls are **0 through 193**, and halt is **194**, excluded from the state count. There are 388 rows. Native start is 74 and halt is 254. `labels.json` gives the dense-to-native conjugacy, including halt in its final entry.

Dense SHA-256 identities:

```text
PA194LCAX11GHF
01c1b37ac3bbc51b2dfef22b8e42a6b3713ed720350269f819d82793e3f01bce

PA194LCAX11GHSF
6d03507fcc85825f81f7db5d02b0cb60e48f87c53be3dd0e4a8888d4922517a9
```

The constructions compose the supplied GH/GHS programs with the existing loop-continuation reassociation and two existing guarded physical shortcuts. The component ideas are attributed to the incoming packets. These combined tables are new: exact canonical tuple comparison finds neither among the 139 spanning 194-state graph classes in the audited collection, and they are mutually distinct. The structural comparison allows arbitrary control renaming, any spanning initial root, global reflection, global bit exchange, and erasure of halt-entry action decorations.

Exactly five native rows differ from each GH/GHS parent. The changes alter recurring execution, including 305 source addresses and 61 constructor-loop occurrences. The resolved logical instruction graphs remain identical to their respective parents. The full tables also appear in the PDF appendices.

## Mathematical and verification status

The new ordinary iPRA relative proof gives both bounded halting implications between each parent P and child N:

```text
H_P(t) -> H_N(Theta(t))
H_N(t) -> H_P(Theta(t))
Theta(t) = 13 t^2 + 715 t + 58624.
```

Here H means halted by the specified time in the totalized blank execution. It follows intuitionistically that the parent and child nonhalting sentences are equivalent. `proof/relative_proof.tex` contains the standalone argument; the report incorporates it.

Both new machines passed independent literal-row symbolic verification of every source branch, nine arbitrary natural registers, arbitrary affine nonnegative gap, and an arbitrary nonempty spare list. The independent checker imports neither the builder nor arithmetic-block oracles. It derives four generic list traversal lemmas from the literal rows and checks the complete blank startup tape, including blank exterior. These are symbolic checks, not bounded tests on small register values.

The absolute conclusion `iPRA proves Nonhalt(M) <-> Con(PA)` invokes the supplied **written** GH/GHS calibration and its revised AX11H dependency. The exact underlying AX11H ZIP has SHA-256:

```text
93ee082ef035b2d32e71d6af5239b25b4bea1773f03bea4d2c39810a7fe15075
```

It is retained as `references/ax11h_written_calibration.zip`. Its source pin is `1c9524d8bf2e0a27b9a16ff622359927f536e663`, with Foundation gitlink `32e1a0956a8622fad067328ca1959729a7634428` and the exact mapped `nativePAConsistency` endpoint. The unchanged GH/GHS parent packet with acceleration is also retained. This archive does not newly implement every numerical PA-proof compiler recipe or complete the end-to-end Lean theorem. The report and `research/calibration_audit.md` explain the dependency and the focused review performed here.

## Reproduce the delivered results

Use Python 3.10 or later with the standard library and assertions enabled. Do not use `python -O`.

```sh
python3 verify_all.py
```

This checks the SHA-256 manifest, reconstructs both tables in a temporary copy, repeats construction-side and independent literal verification, compares regenerated artifacts with frozen outputs, checks the common clock envelope, and repeats exact novelty against all 139 frozen representatives. It also checks the universal 68,268-row rho template, the concrete guard certificate, both finite recoding suites, the specialized-rho countermatrix, and the tagged-three AX free-algebra interface. Regeneration occurs in temporary directories; delivered artifacts remain unchanged.

For a shorter run that omits only the independent literal replay:

```sh
python3 verify_all.py --quick
```

The narrower machine-only wrapper remains available:

```sh
python3 reproduce.py
python3 reproduce.py --construction-only
python3 verification/check_clocks.py
```

The independent verifier is executable mathematical evidence, not a proof-assistant kernel. Parent literal certificates are explicitly marked as imported in the clock receipt; child certificates are newly replayed. Validation logs and the final full-replay receipt are under `verification/`.

## Comparison scope

The main snapshot is ProveIt commit `8d31445d858761a8f6150c2e5012adae8895e932`. The audit inspected 718 tracked PA `.tm` files plus 2,108 literal occurrences in the six then-current incoming ZIPs and their distinct nested ZIPs. Its strict recognizer accepted 2,803 occurrences representing 855 byte payloads, classified as 720 spanning graphs across all sizes. The 194-state frontier has **139 spanning graph classes**; 54 spanning 193-state research classes and two nonspanning 194-state byte forms are recorded separately. The JSON supplement inspected 11,847 occurrences and 8,205 distinct payloads, recognizing 311 explicit 194-table occurrences and no additional graph class.

These graph counts include rejected and auxiliary research tables. They are not counts of established consistency machines. Every one of the 724 original source payloads was matched against its pinned Git blob identity.

A later audit through `ef0839bf15d8b556bc1e1634e6ad310adbcd4fe3` checked the filing of the incoming packets and subsequent formalization additions. All 42 newly filed literal-table blobs were already in the original census; no new 194-state graph appeared. Complete source and late-audit evidence are in `comparison/`.

The portable novelty check needs no repository or network. To repeat the full source census, obtain the pinned repository and original incoming ZIPs, consult `comparison/COMPARISON_NOTES.md`, and set `PA_AUDIT_REPO` to the local checkout. Full-inventory scripts retain some original analysis paths for provenance and are not invoked by `verify_all.py`.

## Additional mathematical result and reduction attempts

`research/tagged3/recoding.tex` proves a two-way PR proof translation for

```text
I(A,B) = 3 p(A,B)
U(a,B) = 3 p(B,a) + 2
M(a,b) = 3 p(a,2b) + 1
E(a,b) = 3 p(a,2b+1) + 1,
```

where p is Cantor pairing. One inverse permutation acts on both formula codes and variable labels. It preserves the self-indexed diagonal and gate; the nonmonotone restricted-rho guard is repaired by a fixed primitive proof expansion. The independent universal certificate contains 68,268 rows over four formal variables, rather than numerical samples.

The source implementation in `research/tagged3_pricing/` reached **207 states**, with 4,831 construction-side source contracts and complete startup verified. The optimizer's 203 score overcounted simultaneously compatible folds by four and is not an accepted count. This larger candidate has not received the separate literal verifier used for the two 194-state deliverables. The tagged-two prototype in `research/tagged2_pricing/` has an optimistic 206 score but fails a source contract; it is unvalidated.

Other bounded attempts are under `research/physical/` and `research/startup_search/`. Startup repair of the inherited 193-state runtime completed 767,923 runs and 65,104,852,630 literal transitions, with no whole-frame hit. These are overlapping execution-work counts. Resource-bound runs remain unresolved, and no impossibility claim follows.

## Contents and PDF build

| Path | Contents |
| --- | --- |
| `report/` | Main PDF, LaTeX, both complete tables, all 139 comparison rows |
| `machines/` | Two dense/native machines, labels, source and grammar |
| `inputs/` | Exact GH/GHS parent inputs |
| `construction/` | Builder, retained compiler, provenance, machine-specific README |
| `verification/` | Independent checker, full contracts, startup tapes, clock audit, replay logs |
| `proof/` | Standalone relative iPRA manuscript |
| `comparison/` | Ledgers, graph representatives, novelty checker, source and late audit |
| `research/` | Recodings, rho certificates, pricing, failed reductions and logs |
| `references/` | Exact parent and absolute-calibration archives |
| `licenses/`, `NOTICE.txt` | Original licenses, attribution and contribution scope |
| `MANIFEST.sha256`, `PROVENANCE.json`, `STATUS.json` | File identities, source pins, result boundaries |

Rebuild with an ordinary pdfLaTeX installation:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

C++17 is needed only for optional negative searches. No external service, Lean installation, or network is needed for accepted-machine replay. Original licenses accompany derived code and proof dependencies. No upstream repository was modified.
