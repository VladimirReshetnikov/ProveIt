# Exact input grammar and propagation of a single finish event

Date: 2026-10-26. Independent complete source/check review and fresh replay:
ROOT. Author receipts: [input grammar](wang-tiles942-input-language-author.md)
and [reset/finish rows](wang-tiles942-reset-rows-author.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942InputLanguage.lean (137 lines) | a28c66e285b3fc652392bc9d58c04135a4fef1f11b4a7e4378a0e02a4416307c |
| WangTiles942InputLanguageChecks.lean (79 lines) | a5aaa22ade8ea6d6edb6a230006d39149af0a6862dc720656fab763acb11e514 |
| WangTiles942ResetRows.lean (162 lines) | c12f1209b1a90e967859a10e989b7fde9ae32bbcf8b6245f99ca267adcdf7513 |
| WangTiles942ResetRowsChecks.lean (82 lines) | 53df3940ba01e30572b97ddeaa879b1b670401badd29dc09bae0a70da2b82f8b |

ROOT read every line of all four frozen files before fresh direct
`lake env lean -M6000 -j1` executions. Both main outputs were separate
temporary objects; the checks used frozen author-built main objects.
All four passed, with empty main logs and eighteen standard-only axiom
audits. No entire dependency or umbrella rebuild is claimed. ROOT authored
the geometry prerequisite used by the reset-row checks; this is independent
review of these new implementations, not independent authorship of their
whole dependency chains.

The input index2*q+b recovers its operating state and bit by division
and remainder. Structural Allowed-family cases prove that an operating
head input selects exactly that actual transition row. Halt432/433
retains pass and finish, and plain0/1 retains pass, finish and every
actual directional receive target, including215. No locally possible
finish is discarded by this finite classification.

The reset proof establishes generic two-direction connectivity of an
arbitrary open integer interval, including negative seeds and singleton
interiors. Color1 then propagates reset status across any seam-free row.
This keeps the three possible reset South labels distinct. One south438
edge at time t gives one reset at t+1; propagation makes that whole next
interior row reset, and time matching pulls south438 back across row t.
Actual language classification identifies every row-t tile as finish.

The marked-plane check derives all matching and nonseam hypotheses from
the actual marked word and PersistentStrip; only a single actual south438
trigger remains. There is no supplied uniform row, event-existence,
unique-head or run premise. Finite tests retain halt215 and all finish
alternatives, reject operating-input finishes, distinguish reset labels,
and preserve the genuine seam obstruction to reset inference.

Run-step decoding and eventual halt remain separate obligations. These
packets do not assert a final consistency theorem. The decimal equation
and metrics are unchanged.
