# Actual halt to a finite marked Wang word

Date: 2026-10-26. ROOT independently read all six complete frozen sources
and author receipts, checked their operational and signed-coordinate
arguments, and freshly replayed each main and checks with
`lake env lean -M6000 -j1`. Existing prerequisite objects were reused;
fresh main outputs went to separate `/tmp` objects and checks imported
the frozen author objects. No entire-closure rebuild is claimed.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942TraceCycle.lean (182 lines) | 58ca5b2877426faf6704700f970043526c50873f429e9248552d8bb3019ca17e |
| WangTiles942TraceCycleChecks.lean (101 lines) | 9934b7b6c05a83704474b842e2f425068ccadd05341b6c86dda0b453662d1081 |
| WangTiles942CycleBoundary.lean (104 lines) | a2f992dbfd4c14d70b8daf423c0b598d714131c5605cf29c833bc7dc2b808f8f |
| WangTiles942CycleBoundaryChecks.lean (63 lines) | 938cd83cf5a768a0c1a77f79cb6bb16b2f78b0caabe29f4ecca6ebf174c8aa65 |
| WangTiles942CycleBand.lean (167 lines) | feff6383911a22e0f496f95eff693d0ee757861831890f555cf85c5370de18e8 |
| WangTiles942CycleBandChecks.lean (82 lines) | adbc833379205c7784de10393dbe682654812d8962f7523aa26ef6ab639b1091 |

`runTile` constructs the exact actual run row: the proved transition
construction while operating and the proved pass construction after
halt. North is color at time t and south color at t+1, including actual
write/movement into halt. `cycleTile` uses the initializer at0, actual
run/wait rows thereafter, finish atH−2 and reset atH−1. The finite
successor is explicitly moduloH. Actual halt atT and T+2≤H discharge
finish membership; H≥3 keeps all distinguished roles separated. Every
vertical edge matches, including reset back to initializer. Tests show
why H=2 fails and why a premature finish is not Allowed.

The boundary module applies the actual halted-trace box at both t and
t+1. Thus positions at or beyond±(T+1) differ from both the old head and
the actual moved head, and read blank. Their run tiles are literally
(0,0,0,0). With independent margins T+2≤L,R, the first interior west edge
is the code2/1/0 for initializer/reset/other; the last interior east edge
is its square4/1/0. The first receiver negative control confirms that
excluding only the old head would be insufficient.

The band lifts finite time using the canonical value of signed t in
`ZMod H`. Its seam at−L has west equal to the **previous** right code
squared, north/south437, and east equal to the current left code. These
are actual Allowed seams. This proves ordinary horizontal matches in
the band and exactly the positive-time twisted match at its right end.
No clean-boundary or independently supplied run premise occurs.

`marked_word_of_halt T L R H` consequently constructs an actual marked
word of length(L+R)*H and strideL+R, from only an actual blank-run halt
atT, T+2≤L,R,H and3≤H. Margins and height remain independently enlargeable.
Every original canonical-band tile is retained at its signed address.
No coprimality, unique Start or quotient factorization is assumed.

All six fresh root runs passed, with empty main logs and39 standard-only
or axiom-free reports:17 for the cycle,7 for boundaries and15 for the band.
Their check log SHA-256s are respectively
`3a480314632476e91c8afe212332e7e0c92a76d6461ea401e2c2769bdb398353`,
`7e138a58890b576b408a40c8529258beb3b472a87f26be559885f05357ae1245`,
and `b874c0c598cd8160b14da234a2b6c7c84b80b1eadf2b60946f4468fd9b3e240d`.
Only subsets of `propext`, `Classical.choice`, `Quot.sound` occur.

The [trace-cycle](wang-tiles942-trace-cycle-author.md),
[boundary](wang-tiles942-cycle-boundary-author.md) and
[band](wang-tiles942-cycle-band-author.md) author receipts bind each
construction. This is the native reverse construction; the arithmetic
controller, polynomial witnesses and internal-ZFC derivation remain open.
The maintained decimal equation and size metrics are unchanged.
An [independent cycle/boundary review](wang-tiles942-trace-cycle-boundary-peer.md)
also passed all four isolated fresh builds with24 standard-only reports,
byte-identical mains and unchanged shared artifacts. The separate
[band/completeness review](wang-tiles942-native-completeness-peer.md)
passed its four isolated builds with22 standard-only reports.
