# Euler-checked free-group terminals for compressed normal cuts

Research continuation for ProveIt, 12 October 2026.

The complete article is [article/Euler_Group_Terminals.pdf](article/Euler_Group_Terminals.pdf), with its main source in [article/Euler_Group_Terminals.tex](article/Euler_Group_Terminals.tex). Full mathematical proofs, experimental limitations, sixteen research questions and a global complexity research programme are included.

## Main result

Let an authenticated whole normal cut have `c` compact orientable components, all with nonempty boundary. If its component fundamental groups are certified free with total rank `r`, then every component is a handlebody **if and only if** its source Euler characteristic satisfies `chi = c - r`.

This criterion needs neither a separate irreducibility certificate nor a separately matched boundary census. The proof uses classical topology, including the Loop Theorem and the three-dimensional Poincaré theorem. It determines unmarked homeomorphism types. It does not construct source-coordinate meridians or transport a boundary pattern.

For the native source class with disk parallelity bases, the new complete whole-cut compiler has at most `74t` generators, `78t` relators and `78t` literal signed letters, independent of normal-coordinate magnitudes. The full source profiles, integer bit mass and source proof have separate costs. A deterministic nonincreasing singleton Tietze policy has polynomial discovery and independent replay bounds. It is explicitly incomplete.

The exact source ledger is `chi = c - a + m - h3`. If a valid trace deletes `z` freely trivial relators, then `b2 >= z - h3`; equality holds when all relators have disappeared. Thus a completed free trace passes the terminal gate precisely when `z = h3`. Five saved source-bound proof packets establish actual positive second Betti numbers that would be missed by freeness alone.

## Concrete native improvement

The previously missed `pilot/finite_figureEight/0` cut is certified as a genus-two handlebody and a solid torus. Its 25-generator, 22-relator, 53-letter presentation reduces to free ranks two and one, with source Euler characteristic `-1 = 2 - 3`. The difficult five-row component is already freely and cyclically reduced, and has no initial unsigned column leaf. The new policy needs three genuine substitutions before its final private pivots. Its accepted relator lengths are `18, 16, 13, 7, 3, 0`.

This is a statement about a supplied cut of the figure-eight exterior. It is not an unknot verdict for that knot.

## Final source audit

The exact baseline is commit **9bacc258bff4b34b4a92b6fa71d290ba5e60ea26**. The audit evaluates 106 historical sources and 14 interior-vertex/three-handle sources.

| Method | Historical / 106 | Interior / 14 | Total / 120 |
|---|---:|---:|---:|
| Current canonical default | 92 | 12 | 104 |
| New group terminal alone | 64 | 12 | 76 |
| Incoming deferred comparison | 99 | 12 | 111 |
| Current default plus group | 95 | 12 | 107 |
| Deferred plus group | 100 | 12 | 112 |

The current default already has 104 positives; the earlier incoming report's 102-positive default used an older baseline. Those two previously integrated gains are not attributed to this package.

All **291 positive outputs** across the three separately evaluated producers independently replay. All **76 serialized new group packets** replay from the delivered files. Fresh Regina literal cuts complete on 113 sources; seven exceed the 4096-normal-disk expansion cap. All 105 explicit oracle-positive cases are covered by the combined portfolio. The eight combined refusals each contain an oracle-recognized nonhandlebody component. This finite corpus does not establish general completeness.

The new terminal adds three cases over the current default: `pilot/finite_trefoil/0`, `pilot/finite_figureEight/0`, and `pachner23_5_8_2/mixed`. Only the figure-eight case adds to the deferred method.

## Implementation and verification

The patch adds six production modules in three producer/checker pairs:

- `source_cut_group` and `source_cut_group_verify`: complete signed source presentation and independent geometric reconstruction.
- `free_group_elimination` and `free_group_elimination_verify`: deterministic polynomial one-sided policy and independent exact Tietze replay.
- `normal_cut_groups` and `normal_cut_groups_verify`: authenticated whole-cut assembly and Euler-checked genus census.

It also adds three test modules and edits the existing whole-cut producer and verifier entry points: **eleven files total**. The patch has been checked and actually applied to pristine affected baseline files, with all eleven resulting hashes matching the integrated test checkout. See `integration/patch_validation.json` and [INTEGRATION.md](INTEGRATION.md).

The default `group_fallback=False` preserves existing behaviour. Set `group_fallback=True` to retain the geometric terminal as a fast path and try the new method after a refusal. The direct method is `normal_cut_groups.normal_cut_group_handlebodies`. The existing public verifier dispatch recognizes the new schema. Each stage of the optional portfolio currently gets its own `max_cycles` allowance; the wrapper does not claim a single shared allowance.

All **1,749 native tests pass**, as do a separate run of all **33 new focused tests**. The independent algebraic audit checks **10,203 presentations**, including **6,748 complete explicit-map Tietze replays**, **481 nonabelian S3 comparisons**, **485 Regina group recognitions**, and **3,240 rejected mutations**. Two dispatcher replays and sixteen strict transport/adapter checks additionally exercise the delivered packet formats. These are mathematical proofs plus ordinary exact software and independent tests, not a formal proof-assistant development.

## Performance interpretation

Complete-query measurements include native source construction, certificate production, compact JSON round-trip and independent source replay. Regina measurements include source import, literal cutting and genus recognition. Imports and warm-ups are excluded; seven shuffled rounds and duplicated A/A arms are retained.

The new direct path takes approximately 5.7 ms on the trefoil cut versus 24.7 ms for the literal Regina task. It is slower on the figure-eight cut (75.5 versus 22.5 ms) and substantially slower on the mixed Pachner cut (1.25 seconds versus 3.18 ms). The original aggregate 45-second benchmark cap on the mixed case and the separately completed retry are both preserved. This is an additional certified capability, not a universal speedup.

The meridian multiplicity family illustrates inherited compression: 1024 copies take about 8.4 ms for the new certified path versus 111 ms for the literal task. A `2^16384`-copy source takes about 35 ms without expansion; no explicit-time extrapolation is made. The article separates this existing compression benefit from the new terminal's contribution.

A diagnostic profile of the mixed Pachner case attributes 98.4% of instrumented wall time to four inherited source-construction and verification stages; the new finite compiler and algebraic stages account for about 0.086%. Appendix C proves a polynomially guarded explicit-orbit certificate design motivated by this profile. Its native weighted-query adapter is a proposed next optimization, not an implemented part of the patch. The raw profile and its limitations are retained in `results/`.

## Reproduce

After following the pinned-base integration instructions, run from this package:

```bash
fast_root=/path/to/ProveIt/Topology/UnknotRecognition/fast
python tools/verify_packets.py --fast-root "$fast_root"
python tools/audit_euler_defects.py --fast-root "$fast_root" \
  --replay-only certificates/euler_defects.json \
  --output /tmp/euler_defect_replay.json
python tools/audit_freeness.py --fast-root "$fast_root" \
  --target certificates/figure_eight.json \
  --output /tmp/independent_freeness.json
python tools/audit_native.py --fast-root "$fast_root" \
  --output /tmp/native_audit.json --packets /tmp/group_packets
python tools/benchmark_terminals.py --fast-root "$fast_root" \
  --case-timeout 120 --output /tmp/terminal_benchmarks.json
python tools/generate_figures.py
bash article/build.sh
```

Native production and replay use only the Python standard library. Regina is required for the independent oracle audits and benchmark. Matplotlib is required to regenerate the figure. The saved runs used Python 3.12.14 and Regina 7.4. Do not run the research audits with Python `-O`, because some use assertions.

## Contents and provenance

- `article/`: full article, bibliography, vector figure, build script and PDF.
- `integration/`: patch, complete eleven-file overlay and patch validation.
- `fixtures/`: the two exact source corpora.
- `certificates/group/`: all 76 complete positive source-bound packets.
- `certificates/euler_defects.json`: five independently replayed positive-H2 certificates.
- `certificates/figure_eight.json`: convenient standalone target packet.
- `comparison/deferred/`: four unchanged and attributed incoming comparison modules.
- `tools/`: portable reproduction, replay, profiling and figure scripts.
- `results/`: raw counts, proofs of replay, full test logs, timing samples and diagnostic profiles.
- `SOURCE_AUDIT.json`, `CLAIMS.json`, `SHA256SUMS`: source identity and claim/reproduction ledgers.

The native audit retained a checked prefix of 105 cases, corrected a hexadecimal-versus-integer comparison in the harness, and completed the final fifteen after matching all source hashes. The full explanation is in `results/NATIVE_AUDIT_METHODOLOGY.md`. No source or algebraic certificate failed.

## Remaining mathematical objective

**The generic quasi-polynomial unknot-recognition bound remains unproved.** The article proves conditional global branch-budget and marked-interface quotient theorems, as well as an exact residual terminal kernel. It distinguishes `exp(O(log^2 n))` from `exp(O(log^3 n))`, and makes candidate discovery, marked transport, source-proof size and all rejected searches explicit obligations. The sixteen proposed questions and concrete milestones appear in the article and [RESEARCH_QUESTIONS.md](RESEARCH_QUESTIONS.md).

The incoming deferred overlay and the new patch both edit the whole-cut producer. Their full-file overlays must be merged deliberately; the measured 112-case union is not a claim that the incoming `forest_strategy` API has already been merged into this patch.
