# Round16 square/weighted literal sources: independent static review

Result: **STATIC APPROVAL, no unresolved finding.** This review covers the
frozen CODE ONLY/HOLD preparation below. It does not report successful
execution, emitted source systems, executed controls, a projected equation
or a new numerical endpoint. A separate root release is required before
any of the five proposed source-only commands.

I read every line of the 225-line producer, 587-line independent checker,
259-line proof, README and boundary, together with the complete pin,
copy, archive-member and held-inventory records. I inspected the complete
selected source/certificate JSON inputs and the literal interfaces used
by the new code. I did not import, compile or execute either new program,
an incoming program, a source transformer or a projector. No transformed
source was emitted. Only inert text, JSON, hash and Git-ZIP member
inspection was used for this review. Author files were not edited.

## Exact checkpoint and authentication

The reviewed folder is `research/round16-square-weighted-source/`.

| File | Bytes | SHA-256 |
|---|---:|---|
| `HOLD_INVENTORY.json` | 3309 | `2fbc07b5e317b0cc1d58fbd012a66039c958ea721120879a520736cdba7a5f06` |
| `build.py` | 13542 | `c40bc4c9d2b791f441a4dfc085ba342ec368428846cce8fbdf9e4b7992b511de` |
| `check.py` | 35451 | `f0b4dbee6d484293e48ead858e5cb5c8076c780814042e41c6f7531494a3f040` |
| `PROOF.md` | 14204 | `fa512b03b2b1f26b6dec4ab294f51bd689eeab1ee39458e26c8422c805ad040b` |
| `README.md` | 2876 | `3df5da8689b6804e4ce205733ae7fdb81261f72f3e5c1105f2acafc92c523d13` |
| `BOUNDARY.md` | 2471 | `24734f3bae41bc3721b7c0a151202dc86266a316526d6afc4a3cbf23bc777d09` |
| `SOURCE_PINS.json` | 7760 | `a5d3b9b0bb3238fdd3f46e00673d7440ee38700b15dc3545c68b933dc68ed6a5` |
| `COPIED_INPUTS.json` | 3164 | `c034a9ce66c1b42ed28c4e17d33878689a3cf0e3c2fa03bea581920a021e70e7` |
| `ARCHIVE_MEMBERS.json` | 3101 | `be6f7749dd1881df90e75125d865bfd159607eadf4d55afe078dfd209ed12f45` |

The held inventory closes exactly 21 payloads, 474102 bytes, with its own
root inventory excluded. All 28 external whole-file pins, seven core
pins and twelve exact local copies pass independent byte/hash checking.
The two complete ordinary inventories also pass, including exact names,
all member hashes and typed byte counts where applicable:

- Hstar/remainder/x-fusion ordinary seal:
  `aeb8e0988d86b7dd08e15e7db439ba1122a7095a93b311e26e07d2caaf5dabad`.
- Weighted products/private175 ordinary seal:
  `66d5c89f48f5d8a7fc2f13f86205c46ddff52b4821a6c1683188fc93d8772ce3`.

The ten selected original source131 member copies were compared with the
whole original 446-member ZIP, read from Git without restoration or
execution. Original commit:
`fd3e384e92ed4813a5536f877c5cd835ca4c75d2`;
blob `d48000bbfe86ad6a3d8ade43f8bdfd19d20f33d7`;
ZIP SHA-256
`97c828ef295d52ea53800dc0761e94cc5605dec306aae3eeecef1d074fa254f8`.
The copied source is the entire 541-coordinate/398-row system; its guarded
parent is the entire 622-coordinate/425-row system, with exact original
body and variable prefixes. All 81 old Legendre auxiliary coordinates
occur only in their own guard rows.

The inert authentication receipt is
`/tmp/round16-square-weighted-source-independent-static-auth.json`,
1647 bytes, SHA-256
`2e508dc30a7bf0e4a7a62ba2b7a0b9ac4462a4dfa50d2fc641f97d8719d60e7a`.
It records static authentication, not a run of the reviewed checker.

## Complete transformations and witness boundaries

Both profiles keep the numeric namespace of all old body coordinates
0..540. They delete exactly the x graph at row398 and the nine CRT scalar
graphs at rows401..409, together with their thirty private coordinates
541..543 and550..576. Other old guard rows, names and auxiliary triples
are explicitly mapped and compacted. New products are appended after
retained old guard auxiliaries, so the code correctly uses explicit body
and row maps rather than treating all new body coordinates as a prefix.

The sole old occurrence of private175 is row158. Replacing its N-square
definition by `175=2+sum_(j=16)^24 v_j^2`, and replacing its BH consumer at
row382, is exactly the pinned ordinary private-slot construction. Old
175 is not claimed fixed in an old/new witness map; the old square and
the new Hstar are reconstructed according to their respective meanings.
No frame, power or cap port uses this private slot.

All eleven remainder repairs are bound to their actual two body rows
and guard rows. Each old remainder occurs linearly, with coefficient
minus one, in those two body rows only. The substitution is
`r=1+q*u`; the slot is retyped as u. The interval equation becomes
`D-2=q*u+s`, while its graph is `u*s` minus the Legendre form. It remains
quadratic. The proof and map records explicitly rechoose the interval
witnesses: retaining a slot and its graph polynomial is not a claim
that an old raw-remainder triple can be kept unchanged.

Plain uses seven unique monic partial products of the eight factors
`v16+1,...,v23+1`. Weighted uses five partials starting with
`EA=v143-v20-1` and `EB=v140-v21-1`. Its actual ideal identities give
`EA=F*(v16+1)*(v20+1)` and
`EB=F*(v17+1)*(v21+1)`, hence the final root is exactly `F^2*P8`.
The checker separately collects both identities and the third bounded
edge identity from their original source rows. The fresh final graph
is directly quadratic, `(x+1)*root-1` minus a new Legendre form; no
unmentioned x product coordinate is assumed. Both profile maps use
fresh strict triples and uniquely recomputed monic partials.

## Actual power, frame and cap interfaces

The literal context includes all eighteen requests, their 54 ports,
fifteen seed pairs/norms, five moduli and 38 affine frame atoms. I checked
the complete row-to-call list, actual request outputs and seed aliases,
the derived t+1 pair, full frame and cap/pool records. The source context
uses original indices and supplies explicit maps into each active
profile. It does not use an old certificate's frame-row number as the
active row identity.

All five modulus coordinates268,285,291,307,313 have metadata kind
`witness`, so the independent symbolic expansion correctly leaves them
as boundary variables. The separate witness-kind discriminant333 is
explicitly lowered through actual rows259/260 to `A^2-1`. With that
lowering the derived request has the required recurrence polynomial
`q*X_t+(q*A-1)*Y_t-Qt1-T*d`. Other requests collect to
`X+(n-A)*Y-m-T*d`. No unnoticed blanket expansion of witness-kind
moduli is used.

The proof's order is acyclic. Retained remainder/slack anchors give
B>=1 and q>=2; the square horizon gives t>=16. The generic cap argument
permits initially signed x/CRT targets. The q^t request fixes the
positive t abscissa; the same pair at base F^2+1, including the base-one
case, recovers V0. The actual ceiling then gives F>=1, B>F^2+1 and q>=3.
The retained cofinal relation gives y>=F+1. No removed x/CRT sign or
repaired interval sign is used to obtain those conclusions.

The BH request gives positive K before N=B^K is interpreted. Endpoint
and signed-output arguments give the divisibility needed for repaired
residues without first assuming the Qx output positive. The residue-one
identities exclude negative q+1 targets, and the reciprocal row excludes
the last zero target. Thus the eight product factors are nonnegative.
The strict fused graph makes x+1 and all eight factors positive.
Only afterward do the positive denominators and repaired interval
equations restore all required interval signs and fresh old scalar
graphs. The native/refutation contract is invoked after those steps.

Completeness rebuilds the changed radix, digit, remainder, frame, Pell,
cap and guard witnesses in the ordinary construction order. The old H0
to Hstar transfer is through decoded refutations and fresh canonical
data, not an asserted unchanged old q/W/Pell tuple. Maps between the two
repaired Hstar presentations fix their common repaired semantic tuple
and unaffected witnesses, while rechoosing products and strict triples.
These distinctions match the accepted ordinary contracts.

## Independent checker, controls and file handling

The executable closure is exactly the two new programs and Python's
standard library. Neither imports the other or any incoming, vendor,
factorizer, projector, collector or source module. There is no process
launch. The checker reconstructs each complete profile independently,
checks canonical integer terms and degree at most two, collects every
row identity, verifies full headers/metadata/maps/privacy, and computes
the actual unused-coordinate sets. It does not assume all raw variables
are live or infer a projected census from deleted guards.

I read all planned rejection paths: nineteen per profile and five
global controls, for 43 planned negatives. They include actual private
JSON artifacts, changed rows and coefficients, a cubic naive interval
substitution, maps, source-context and witness-map corruption, producer
binding and altered indexed bytes. These reach structural and semantic
checks rather than relying solely on a changed outer hash. The four
positive controls check semantic polynomial invariance under term
permutation and cancellation. They are explicitly not claims that the
full literal-format checker accepts a noncanonical serialization.
None of these controls has been executed in this static review.

The producer prepares all expected data before writes and compares full
bytes on rebuild. It rejects unexpected or different existing data,
symlinked data targets and writes into protected input/core locations.
The checker authenticates whole indexed data bytes and a final closed
inventory if present. Receipt writes require separate fresh or byte-
identical outputs. The five README paths are compatible with the held
verification directory. Normal and optimized execution do not rely on
Python assertions for required checks. Both pure rebuild commands are
designed to compare all eight generated data files; that remains a
future run obligation.

## Decision and remaining scope

The full reviewed closure is suitable for root's separate decision on
the five specified source-only commands. There is no requested author
code or proof correction. The held bytes remain unchanged, and no data
directory exists at review completion.

This approval retains the explicitly pinned source131/Round15/C222 and
ZF-to-ZFC ordinary contracts. It does not newly audit or rerun all of
their transitive runtime closures. It licenses no factorization,
projection, SOS/quartic coefficient census, frontier, optimality, page
promotion or Lean claim. In particular, five versus seven new partials
and private175 reuse establish literal constructions and witness maps,
not an automatic projected dimension saving.
