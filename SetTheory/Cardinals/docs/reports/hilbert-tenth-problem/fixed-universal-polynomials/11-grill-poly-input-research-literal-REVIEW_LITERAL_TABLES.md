# Independent audit of the finite literal U15 / tag / Genera packet

Status: PASS. No correction found in the audited artifact.

The audit is bounded finite-table and semantic work. It neither instantiates nor audits the two recoders, input arithmetic, Grill history circuit, final polynomial, or their costs. It is not a proof-assistant certification or an independent proof of U15 universality.

## Frozen objects and reproducibility

- Literal packet SHA-256: `3c8924dbb1b5d6e6b8897e59550b0e38a703654b87442c73487f411e94ae355b`
- Own builder SHA-256: `1c80e8d050ff079cf56444e2cc0eed626195099a3ad0188c7e021c4837b205c5`
- Independent checker: `review_literal_tables.py`
- Machine-readable result: `review_literal_tables_result.json`
- Reproduce the independent audit with `python review_literal_tables.py`
- Separately, `python build_literal.py --expect` passed byte-for-byte regeneration of the packet and manifest

No downloaded upstream program was imported or executed. The checker obtains only the frozen upstream `TABLES` dictionary using Python AST parsing and `ast.literal_eval`. The primary `u15-table16-page.png` image was also manually inspected. Every source-file hash and size in the manifest was independently checked.

## Source and literal rules

All 29 instructions match the frozen upstream U15 table and primary Table 16 (printed p.121, PDF p.17). The absent instruction is `(u10,b)`. With `c=0`, `b=1`, and refined index `2(u-1)+read`, the start is 0 and the sole accepting state is 19. All 30 refined rows, including all write bits, directions, and both successor indices, match independently reconstructed rows.

Every RIGHT and LEFT rule was checked against the corrected semantic schema, including:

- Write-dependent doubling, parity preparation, even-branch leading filler, and both successors
- The final filler in every corrected even `t0` production
- LEFT preparation/shrinking and all required target prime rotations
- Accepting head `A:19 -> HALT`, inert accepting suffix symbols, all 30 filler rules, the inert sink, and the ignored total halt rule
- Totality, unique identifiers, every canonical-symbol map, the designated accepting source, and the absence of any other `HALT` emitter

The exact tag counts are 570 symbols and 570 productions. A direct decomposition is `14*16 + 15*18 + 4 + 30 + 40 + 2 = 570`: right rows, left rows, accepting row, fillers, shared prime rotations, and inert/halt rows. Output lengths are 59 of length one, 436 of length two, 29 of length three, and 46 of length four.

## Normalization and phase rules

All 2,026 Genera phase productions were independently checked. There are exactly 442 unique ordered pairs; their set equals the two consecutive pairs in every four-padded tag output, together with the dummy/dummy pair. No duplicate pair represents the same ordered expansion.

There are 569 nonhalt original symbols of width one, 442 width-zero pair symbols, one width-zero dummy, and one ignored width-zero halt symbol: 1,013 total, with 1,012 nonhalt symbols. Width counts are 569 one and 444 zero. Original phase 0 emits its two padded pairs; original phase 1 emits two dummy/dummy pairs. Every pair expands identically at either phase; the dummy emits two dummies at either phase. Every literal production has exactly two valid output identifiers.

The unique halt-containing pair is `(HALT,DUMMY)`. Only the phase-0 `A:19` rule emits this pair. Only its expansion emits `HALT`. All original/dummy outputs at both phases are `HALT`-free, verifying the hypothetical-prefix exclusion on the claimed valid layer shape. The ignored halt row is explicitly total. The metadata is restricted to valid canonical runs; it does not assert unique acceptance on arbitrary malformed inputs.

The derived finite parameters also check: `392*(1013+1)=397488` phases if the corrected Grill compiler is later emitted, and width-one E length `196*(1013+1)=198744`. These are source-dependent parameters, not a constructed arithmetic circuit or its operation ledger.

## Independent executable evidence

The checker consumes only the emitted packet for dynamics. Expected Turing updates use a separate sparse two-way tape, writing at position zero, moving the head by the primary instruction, reading the new square, and re-encoding the physical left/right tape. They do not use the builder's arithmetic macro formulas.

- All 29 nonhalt refined rows, with every `M,N` from 0 through 24: 18,125 exact one-step macro comparisons
- 2,005,675 tag steps, with maximum 251 per macro
- Every one of the 534 operative nonhalt tag symbols exercised as an active head
- No active filler or inert sink and no premature successor canonical-head read
- Minimum intermediate preacceptance queue length three
- 300 tested macros entered accepting state 19 and produced exactly one fresh halt symbol on the accepting head step
- 5,554 two-generation projection cases, including every original symbol at both phases with dummy positions, dummy-only words, and 1,000 deterministic random composite words
- 528 successive two-generation projections from actual canonical rows, carrying existing dummy symbols and persistent phase; maximum normalized test word length 896
- 24 complete normalized runs to the first halt from accepting state 19 or its actual U15 predecessor state 17, with small tape parameters; exactly one halt each, at most ten normalized layers, largest first-halt word 16,384 symbols

The complete normalized halt tests happened to put the first halt at index zero, so their dynamic hypothetical-prefix checks were empty. The nonempty-prefix exclusion is instead covered by the exhaustive structural checks: the first-halt layer contains only originals/dummies plus halt, and every original/dummy production at both phases contains no halt. This distinction avoids presenting a vacuous dynamic check as nonempty-prefix coverage.

## Conclusion

The frozen literal table is a faithful instantiation of the explicitly corrected schema and the primary U15 control table. Its counts, totalization, phase-dependent normalization, pair alphabet, and unique-halt adapter are consistent with the stated semantic contract. The bounded dynamics provide strong independent supporting evidence. Universality remains conditional on the imported U15 theorem and input interface, and the full arithmetic/history construction remains future work.
