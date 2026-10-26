# Constructed copies, top bounds and physical order: root review

Date: 2026-10-26. ROOT read all new source/check files, author receipts
and independent receipts in full. These packets were authored by the
agents named in those receipts. ROOT authored earlier literal clause
and carry-composition dependencies, not these new proofs or data.

## Exact sources

Paths are relative to `Lean/DiophantineConsistency/`.

| Source | Lines | SHA-256 |
| --- | ---: | --- |
| `CurrentWordCopies2011.lean` | 217 | `61e1662e3bd9a4a1409a5d47da4a017e714173ca3b2fc247a1bbb38a56546a9e` |
| `CurrentWordCopies2011Checks.lean` | 99 | `a12cbec6f9889336a0b8add70c5a175f0c451c0b22bbbf7c81b552ff4b16c47c` |
| `CurrentWordTopBounds2011.lean` | 259 | `7f8cf6688ef8f0152cbafd388957635a0f8a10e7e72de73fc52af87871217a1f` |
| `CurrentWordTopBounds2011Checks.lean` | 85 | `d90115c218fc12fc7f9667089392bafb4e7777cc7452f9422544fdf8065d4b20` |
| `WangTiles942PhysicalData.lean` | 1324 | `38a11d1ef8d3391074d4cd347e0f764417c6502afd9a6a064d54266456396f5b` |
| `WangTiles942PhysicalOrder.lean` | 180 | `eafbd5914bf4219d6ce48b501c8be41c228253ef719b65a02e7d167ada0ce3e9` |
| `WangTiles942PhysicalOrderChecks.lean` | 65 | `9d7bfcf65995b05546b19c89d44b9de8bb1bdb1bc3e41cf8c9a6060dd7e43460` |

## Mathematical findings

The constructed marker is Start at j+s, so its actual source at j−s
equals current Start. The exact base translation handles all periods
without division by2011 moduloN. Actual temporal/horizontal matching
gives nine South/North and eight East/West bit equalities. Derived low
resets identify normalized digits with the full raw fields, and even
reflected contributions vanish only after reduction modulo2. All17
copy masks and the marker mask follow for the same constructed carries.
No pair equality, mask, clean carry, unique Start or nonzero stride is
supplied. The wrong-marker-sign control actually fails at the same
physical source, while no tiling is asserted for that synthetic control.

The top packet retains all monomials: field2009 has only the actual
Start coefficient times marker1004, and2010 has none. Boolean marker
and the carry57 bound reset2009; the next recurrence gives zero carry
and digit at2010. The final cell's canonical top index is exact even
at N=1. The proved zero-suffix prefix estimate gives F<q/radix.
Source support separately yields C<radix^(N*2011−1006), with the correct
exclusive endpoint. Neither mask nor matching supplies these bounds.

The physical data are checked numerals, not assumed coefficients: all941
positive non-Start indices and actual table weights are proved in59
bounded blocks. Adjacent strict decrease gives an injective enumeration
of the941 non-Start indices and hence full coverage. The actual printed
rank composed with this enumeration is a strictly increasing finite
endomap and therefore the identity. Start is explicitly protected at0.
Both inverse identities, full942 coverage and a generic selector-sum
reindexing are proved. No quadratic floor computation or external
sorting certificate is a Lean premise. This prepares K residue proofs;
it does not itself prove them.

## Validation and limits

ROOT freshly rebuilt the complete Copies main/check sequentially with
`lake env lean -M6000 -j1`, declared `Elab.async false` and pinned
Lean4.32.0. Both terminal results were exit0; the main log is empty,
all14 reports use standard axioms, and both objects match the author.

| Root evidence | SHA-256 |
| --- | --- |
| `/tmp/current-word-copies2011-root-main.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/current-word-copies2011-root-checks.log` | `89d28957021de3a00a8ec85460e9f04885062df244ea80e2f308179aced73cc5` |
| Main `.olean` | `71b9a3acbb1e3d5fa6507a5c56777cb11a818870da11876b6689034d5bf077ab` |
| Checks `.olean` | `00eaa4d598ac297db4e93c627a2b6214bf36763274e90917f0efde1b0592e64b` |

TopBounds has author and isolated independent main/check passes,16
standard-only audits and byte-identical objects. Its harmless exponent1005
elaboration notice is disclosed in both receipts. PhysicalData/Order has
three author and three isolated independent passes,16 standard-only
audits and byte-identical objects. The independent data replay ran to
completion in79.76 seconds. Its reviewer also reconstructed every actual
tile, coefficient and rank from the715-digit seed using a separate
standard-library model. This numerical cross-check is corroboration;
the complete Lean bindings are the proof. Prerequisite authorship and
development failures are disclosed in each receipt.

All replays reuse existing prerequisite objects; no fresh full closure
or umbrella build is claimed. No `sorry`, `admit`, `native_decide` or new
axiom occurs in these sources. Padding, cell-origin tests, the entire
high mask, actual modular K data, controller, safe rank mutations,
polynomial converse and internal-ZFC interpretation remain open.
The maintained equation artifacts and their decimal/distinct-name format
are unchanged.
