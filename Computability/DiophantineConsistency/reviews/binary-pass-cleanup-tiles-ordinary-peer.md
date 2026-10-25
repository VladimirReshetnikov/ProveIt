# Binary pass/cleanup tiles: independent ordinary review

Verdict: **PASS — code-free ordinary proposal only**. The four selected
rewrites preserve the whole indexed tuple pointwise and give the stated
charged source saving. No rendered improvement or execution is approved.

Reviewed immutable `research/binary-pass-cleanup-tiles` manifest SHA-256
`80d44e88695ed56036aaeab3a50292a388bbf2cd7e960463125c7a75fb349a6c`.
Its full README is 11192 bytes, SHA-256
`433f45e54d49c7c52a56f083b142d7e9975eb4fbb1e53ef33dcc25743adcd6cc`;
SOURCE_PINS is 5574 bytes, SHA-256
`5bfe4e19c454f889cde6f2853965bf5c01edc2984e63186686158c84cbe78acb`.
All paths below are relative to `Computability/DiophantineConsistency/`.

## Complete read and authentication

Read the entire note, all 3819 bytes of its selected constant body, complete
pins/manifest, full compact-parent README/pins/body, full indexed ordinary
proof, whole existing 943-entry TILES JSON and four-port binding. Authenticated
all twelve direct and one own pins, both note payloads and exact note
inventory, plus every member and exact inventory of both whole parents:

| Parent | Payloads | Payload bytes | Manifest SHA-256 |
| --- | ---: | ---: | --- |
| `research/compact-tile-parameters` | 2 | 14125 | `5dafe5e3d18abb8d8a4e2254d7ac777d9db21933a8b768eba2c46535a9e3fdf9` |
| `research/indexed-tile-enumeration` | 38 | 359892 | `e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84` |

Inspected every existing compressed/raw port byte using standard-library
gzip, checked hashes, bit lengths and canonical little-endian lengths:
K0 74111 bytes, MC 73759, MF_source 73759 and beta 73759, totaling 295388.
These are the existing accepted tuple, not newly generated coefficients.
The accompanying JSON records all pins, parent seals and raw hashes.

## Eight cases, inverse bijections and all 943 indices

The merged pass row has binary local indices a,b and the following entire
four-case map:

| a | b | Index | Ordered tile |
| ---: | ---: | ---: | --- |
| 0 | 0 | 434 | (0,0,0,0) |
| 0 | 1 | 435 | (0,1,0,1) |
| 1 | 0 | 432 | (0,432,0,432) |
| 1 | 1 | 433 | (0,433,0,433) |

The inverse for 432 <= i <= 435 is j=i-432, b=j mod 2 and
a=1-floor(j/2). Since j=2 floor(j/2)+b, substitution gives
434-2a+b=432+j=i. The binary quotient/remainder are unique, so the map
is a bijection preserving each ordered tuple at its original index.
The order in which the local parameters enumerate cases is immaterial.

The cleanup row similarly has all four cases:

| a | b | Index | Ordered tile |
| ---: | ---: | ---: | --- |
| 0 | 0 | 924 | (0,0,0,438) |
| 0 | 1 | 925 | (0,1,0,438) |
| 1 | 0 | 926 | (0,432,0,438) |
| 1 | 1 | 927 | (0,433,0,438) |

Here j=i-924, a=floor(j/2), b=j mod 2 is the unique inverse, and
j+430 floor(j/2)=432a+b. All eight entries equal the existing TILES JSON.
Both row domains are printed and charged. Proof-only inverse floors do
not appear in the selected table.

The unchanged index blocks are 0..1, 2..431, 436..923, 928..930,
931..933 and 934..942. Together with the two four-element blocks they
partition all 943 indices. Exact complete-body comparison establishes
that every other row is copied unchanged, including the merged direction
family and square-indexed terminal nine. The universal head identity below
preserves every call in those rows. Thus this is a pointwise proof for all
943 tuples, with no selector permutation or fresh tuple generation.

## Head label, all 430 actions and whole constants

For every integer q,b, `2(q+1)+b = 2q+b+2`; in particular h(215,b)=432+b
and the actual first target h(1,0)=4. The initializer (3,436,4,4), other
literal controls and tail tiles remain untouched. Head arithmetic still
uses three operations; two source parentheses disappear.

For every integer m and digit value z, `14(1-m)+mz = 14+m(z-14)`.
The identical literal seed and unchanged N,T0,E0,nu,sigma,m,tau definitions
give the same value at every one of the 215 flag indices. Therefore both
decoded v and d at each j=2q+b, 0 <= j < 430, remain equal. The u expression
is unchanged, so all 430 complete actions and their indices are identical.
Consequently sets/ranks and every transition/copy tile retain their meaning.
The fixed flag expression drops from four to three operations; the main
polynomial's 66 operations do not change.

Read the full seed and verified its entire literal block against the parent
and accepted 436-character seed. All 62 alphabet characters and positional
interpretation are unchanged. Equality of every ordered tuple preserves
every complemented payload. The complete Phi is identical in Z[x], not
only at a selected numerical argument; all four control groups and support
positions are literal copies. Thus its values at rho and 1/rho, the support
indicator/dummy corrections, Lambda and whole MC/MF/K remain equal. Beta
and the single source-high-mask shift are unchanged. The accepted whole
native/Pell/refutation calibration therefore applies to the same four
integers and fifteen-positive, 66-operation, degree-157 polynomial.

Dependency order remains seed/actions, sets/ranks/tiles, payload/Phi, MC/K,
with Lambda/MF depending on the fixed radix. Local binary indices create
no extra unknown or recursion.

## Complete charged text comparison and limitations

An inert text comparison applied exactly the four pinned replacements to
the entire accepted compact body and obtained the whole proposed body.
Each old pattern occurs exactly once; no other source byte differs.

| Replacement | Old bytes | New bytes | Nonwhite saving |
| --- | ---: | ---: | ---: |
| Head label | 15 | 13 | 2 |
| Pass rows | 67 | 41 | 24 |
| Cleanup row | 43 | 38 | 4 |
| Default flag | 35 | 33 | 2 |
| Whole body | 3854 | 3819 | 32 |

The net byte saving is 35. Whole-body nonwhite source characters decrease
from 3587 to 3555. The exact proposed body SHA-256 is
`86f7c12435d09e11a2df312b407da50bb833e34129582e94fdc05a638ae89698`;
the accepted compact body SHA-256 is
`a62f4893e1554d12995c27ec5c542a993e01c1b11d9125352ae14fdb0a5dae17`.
All domains, separators, constant formulas, seed, alphabet and footer are
included. The selected table has ten rows instead of eleven and no floor.

The unselected three-control polynomial reproduces all three literal
tiles; its completely charged row is 52 bytes versus 53, at higher arithmetic
complexity. Nested integer quotient identity also validates the unselected
shared-Q variant. Charging N/Q/T0/E0 with the full new Q definition and
all uses gives 107 bytes versus 106 and one extra nonwhite character.
Both comparisons support retaining the selected literal alternatives;
neither is included in the proposed whole body.

These are ordinary identities and exact source-text metrics. Rendered
glyph counts, page fit, readability, source/PDF audits, fresh raw-byte
reconstruction and implementation controls remain future work requiring
separate full reviews and execution release. This note does not modify or
release the held grouped66 candidate or any maintained page.

No application/module import, compilation, decoder execution, tuple
generation, new coefficient data, standalone TeX/PDF process or Lean work
occurred in this review. Only inert text/JSON/hash and existing gzip-byte
inspection were used. Only the two outside review records were authored.
No finding remains against the exact frozen ordinary proposal.
