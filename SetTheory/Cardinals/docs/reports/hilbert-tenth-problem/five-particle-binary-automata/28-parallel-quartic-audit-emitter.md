# Independent audit of the concrete quartic certificate emitter

Date: 2026-10-03. Scope: `compiler.py` and `circuit.py`, compared with `audit-design.md`, the pinned source metadata, `PARALLEL_RULE_PROOF.md`, and `PARALLEL_LEMMA_AUDIT.md` in the frozen sparse-parallel research packet. This audit does not edit the emitter or frozen packet. Local tests execute only this new emitter and pinned research metadata/oracles, with no upstream checkout execution, package installation, or publication.

## Verdict and scope

**No correctness blocker found.** For a fixed parser-valid source, exact natural mass `n`, horizon `T`, and Boolean direction, the emitted sum of squares has the claimed endpoint semantics and a unique complete auxiliary natural witness for each accepted external input. The conclusion covers every finite support of the fixed mass, including malformed, multihead, translated, and noisy supports. It is not restricted to admissible source encodings or the tested coordinate universes.

This is a source-level mathematical audit with bounded executable checks, not a proof-assistant verification. The all-input conclusion rests on the lemmas below and the pinned all-input parallel-swap theorem. The tests are binding/regression evidence; they cannot by themselves establish those universal statements. This does not provide one polynomial with fixed arity for all sources, masses, or unknown horizons, or encode arbitrary infinite-support inputs.

Two reporting qualifications matter:

1. `Certificate.result(x)` uses `check=False` with a dummy target. It is an evaluation helper, **not an input-validating endpoint verifier**. Validation/acceptance is expressed by all residuals, or by `witness(x,y,check=True)`. The theorem concerns zeroes with natural external variables.
2. The counter `A` counts signed assignment registers, not uniformly bounded-fan-in elementary additions. Several count, offset, and displacement assignments are wide sums. `residual_monomials`, `ordered_sos_term_bound`, coefficient-bit totals, and coefficient L1 totals must be retained when reporting cost. A small register count alone is not a bound on serialized arithmetic work.

## 1. Direct slot formulas and IDs

Let `es=4D+15`, `em=2D+6`, `pm=2D+7`, `r=D+3`, and `L=3D+4`. For moving branch index `e`, mode index `k` (`O=0`, `I=1`), put `eb=e*es+k*em` and `pb=E_count+(2e+k)*pm`. Let the occupied distinguished pair be `h<h2`, marker `z`, orientation `ell` in `{0,1}`, and `w=side` for O, `w=-side` for I. Every comparison below is closed at both range endpoints.

The emitted formulas agree exactly with the pinned `LazySource.gate_at` numbering:

| Family | Type ID | Anchor and matching condition |
|---|---|---|
| Free E | `eb` | `u=h-ell*w`; old head `h`, new head `h+(1-2ell)w` |
| Behind | `eb+1+t-S` | `u=z`, `t=w(h-z)-ell`, `S<=t<=L` |
| Ahead | `eb+1+r+t-(S+1)` | `u=z`, `t=-w(h-z)+ell`, `S+1<=t<=L` |
| Dispatch | `e*es+2em` | `u=z`; home+ at `h-z=S`, O− at `h-z=side*S` |
| Endpoint | `e*es+2em+1` | `u=z-ell*side*delta`, both orientations `h-z=-side*S` |
| Commit | `e*es+2em+2` | `u=z`; I+ at `h-z=side*S`, home− at `h-z=S` |
| Direct | `p*es+direct_index` | `u=z`, `h-z=S` |
| Phase free | `pb` | `u=h` in both orientations |
| Phase near | `pb+1+side_index*r+t-S` | `u=z`, `t=s(h-z)`, `S<=t<=L`; side index 0 for `s=-1`, 1 for `s=+1` |
| Phase home | `E_count+2p*pm+control_index` | `u=z`, `h-z=S` |

All families also impose the exact signed mode/control gap. Dispatch, commit, and direct select the correct source/target home gap. Behind/ahead/free flip the relevant moving mode's sign. Endpoint changes O+ to I−, or vice versa, and displaces **both** head and marker by `(1-2ell)*side*delta`.

In particular, the two easily missed reverse anchors are present: free E has `u=h-w`, and reverse endpoint has `u=z-side*delta`. Reversing a template therefore retains the same `(ID,u)` even when the currently occupied marker has moved. No ordered-factor transition routine is called.

Travel is computed from occupied coordinates, never enumerated over the travel interval. A false range test substitutes a fixed in-range travel value before ID construction. This controls dummy IDs; rejected descriptor coordinates remain fully defined affine expressions in occupied coordinates. No invalid ID is used as an unchecked array index. The compiler does not call `gate_at` or construct an F-sized template array.

The exact raw widths are

- `K_E = binom(n,2) [4p + (14p+2a) max(n-2,0)]`
- `K_P = binom(n,2) [4p + (8p+2m) max(n-2,0)]`

The loops and the explicit width check agree with these formulas. All loop bounds depend only on source data, n, T, or the next power-of-two sort width, never input-coordinate magnitude.

### Raw soundness, completeness, and absence of duplicate live keys

Every triple endpoint has precisely one pair of sites at distance at most D. The designated head gap is at most D. Every marker-to-head distance is at least `S-D=D+2`; the shifted reverse endpoint has the same relative marker-to-head distance. Thus any genuine raw endpoint uniquely determines its occupied pair indices and remaining marker index. A pair endpoint is immediate. Its signed gap fixes orientation, and the displayed arithmetic recovers type, travel/side, and invariant anchor. This proves every genuine raw endpoint is generated by one slot.

Conversely, each slot's gap/range/incidence conditions make its listed old coordinates exactly the corresponding translated endpoint. They are already present because they are occupied coordinate entries. `put` then counts all occupied sites in `[u-(3B+1),u+(3B+1)]` and requires exactly the endpoint arity. This is precisely new-rule raw exactness, using B2 for pairs and B3 for triples. It is neither old radius-B raw matching nor a uniform triple-radius test for pairs.

For a fixed type and anchor, the opposite orientation cannot coexist under that exactness test: the distinct endpoints have equal size, and containing both would require extra sites. Since every family/source/orientation is generated once and the distinguished pair/marker is unique, there are no duplicate live `(ID,u)` keys. This matters because sorting-based isolation does not separately deduplicate.

## 2. Guards in both orientations

Each detector band is inclusive: left `[u-Z-J,u-Z]`, right `[u+Z,u+Z+J]`. Its interval flags and count are deterministic. A singleton produces exactly `side*(x-u)-Z`; an empty band produces J+1. Multiple hits force a false validity bit and a fixed class J+1, so there is no invalid table access or free rejecting class.

Every literal entry of the `(J+2)^2` truth table is scanned and charged. Dispatch always uses the branch **domain** table, commit always its **image** table, and direct always its **domain** table, on both orientations. The latter is correct for zero update. No orientation-dependent table switch appears. The tables are parser-validated fixed source constants. Other families are unguarded.

## 3. Raw-first sorting and all-type isolation

`sort_keys` is a fixed bitonic network padded to a power of two. Its strict comparison is lexicographic on `(-raw, anchor)`: live rows first, then increasing anchor; exact ties do not trigger that comparator. Every comparator swaps the complete `(raw,u,source_slot_index)` row with deterministic arithmetic selects. Stability of equal keys is unnecessary; the network's complete wiring determines every row and witness. Padding is the constant row `(0,0,-1)`.

Consequently, the live rows form an anchor-ordered prefix. A live key has another raw anchor within H if and only if an immediately adjacent live row is within H. The emitted two-neighbor tests use `<=H`, with `H=2(B3+r_block)` and `r_E=Z+J`, `r_P=3B3+1`. Distinct types sharing an anchor conflict. False raw slots cannot compete. Keys that will later fail prospectivity still compete, because isolation is computed before any prospective rejection.

## 4. Compaction, rank, and dummy lanes

The rank before each sorted row is a deterministic integer prefix sum of its isolated bits. Lane k scans every row and selects the source index precisely when that row is isolated and its rank is k. It then scans every source slot to route all descriptor fields. There is no existential permutation, arbitrary padding payload, or unbound source index.

For an absent lane, presence is zero and all payload fields are fixed zeroes: ID, anchor, arity, and each old/new coordinate. The intermediate index starts at constant −1 and remains fully determined. A pair's third old/new coordinates are also fixed zeroes; the arity test suppresses them even if the support contains the actual coordinate zero.

The fixed `floor(n/2)` lanes suffice. Distinct isolated anchors are separated by more than H, hence by more than `2B3`; their endpoint supports, each contained in its own radius-B3 interval and containing at least two particles, are disjoint. Therefore at most `floor(n/2)` isolated keys exist on every accepted input and every subsequent genuine snapshot. This is a mathematical bound, not a property inferred from sampled lane occupancies.

## 5. Hypothetical rediscovery and prospective identity

For each lane, `move(X,[lane],[present])` constructs the single hypothetical swap from the same immutable X. Absent lanes yield X; nevertheless their complete downstream circuits remain constrained. A live isolated endpoint can be replaced without collision: its exactness interval covers the write interval, and both old/new shapes have the same number of distinct sites. The deterministic coordinate sort yields the canonical hypothetical support.

`raw(Y,name)` is then invoked for **all** source slots anew. It is not limited to initially discovered types, anchors, or eligible candidates. Relevant after-keys use the closed anchor interval `|u_after-u_lane|<=q`, with `q=B3+r_block`.

Since the lane is isolated and `q<=H`, its complete before-key set in this interval is exactly `{(ID_lane,u_lane)}`. The code therefore correctly tests that at least one after-key has that same type and anchor, and that no distinct after-key lies in the interval. `same` compares ID and anchor only; orientation is deliberately excluded. The endpoint symmetry theorem identifies the own after-key with the opposite orientation. Explicitly demanding own-key persistence is a valid additional binding check, not an unwanted orientation equality.

## 6. Simultaneous update and canonical ordering

Each original coordinate receives the sum of the selected endpoint-site displacements whose old site equals it. Selected supports are disjoint, so at most one active old-site term applies. Pairing old/new sites in the fixed head/head/marker order need not preserve the identity of an overlapping site: it still transports the full old set to the full new set. Unmatched particles receive zero displacement.

All selected flags are computed from immutable X and independent single-swap supports. The final `move(X,lanes,selected)` applies them together, rather than mutating X while scanning. Exactness prevents collision with unchanged particles; isolation prevents collision between distinct selected endpoints. The odd-even transposition network has fixed n phases and strict `a>b` swaps, so its result is the increasing canonical support and every internal wire is determined even if equal values occur on rejected external inputs.

These operations are the finite-support restriction of the pinned parallel block. The cited lemma supplies candidate-set invariance, selected-key invariance, and involutivity for all inputs. The emitter composes E then P for each forward step and P then E for each inverse step, exactly 2T blocks.

## 7. Natural external inputs, quadratic residuals, and uniqueness

There are 4n natural external variables: canonical positive/negative pairs for each ordered input and requested output coordinate. Every external pair is constrained by `plus*minus=0`; its interpreted integer is `plus-minus`. Comparator acceptance rows require each successive coordinate to be at least its predecessor plus one, on both sides. Thus invalid signed pairs, duplicates, and unsorted external supports cannot have zero residuals. Final linear rows equate every computed output coordinate with its requested target.

The primitive gates are deterministic over these natural variables:

- Signed assignment to integer f uses `p-m-f=0` and `p*m=0`. Its unique natural solution is `(max(f,0),max(-f,0))`.
- Comparison with integer difference d uses `b(b-1)=0` and `d-(2b-1)s+1-b=0`. If b=1, natural slack is d and d must be nonnegative. If b=0, slack is −d−1 and d must be negative. Exactly one branch is possible.
- Equality is `ge(x,y)-ge(x,y+1)`. AND, OR, and NOT receive proven bits, so their deterministic assignment rows produce bits without requiring a separate Booleanity row for every derived output.
- Every select and arithmetic product uses already determined registers. An inactive mask changes a downstream value; it never removes a defining equation. All candidate, sort, rank, lane, rejected prospective, and padding wires are therefore constrained.

Expressions supplied to assignment rows have degree at most two: products are between affine signed registers or bits; nonlinear intermediate results are lifted to fresh registers before reuse. `Circuit.row` explicitly rejects larger residual degree, independently of Python assertion settings. External pair constraints and Boolean comparator equations are quadratic; domain/output checks are at most linear in existing registers. Summing their squares yields an ordinary integer polynomial of degree **at most four**, including degenerate constant/zero cases.

For fixed natural external variables, topological induction gives exactly one complete assignment to all auxiliary natural variables before acceptance rows. Acceptance rows keep that assignment precisely when signed representation, ordering, and endpoint equality hold; otherwise they reject it. A sum of real/integer squares is zero exactly when every residual is zero. Hence accepted fibers have exactly one auxiliary natural witness and all other fibers have none. This is complete-witness uniqueness, including inactive circuitry, not merely unique final state.

For n=0 or n=1, raw families are empty and each block is identity. The n=0 empty polynomial has the single empty auxiliary witness. For T=0, the construction reduces to canonical-domain and identity-endpoint checks. Sources with p=0 retain direct/home-phase families and correctly permit empty E.

## 8. Executable evidence and version binding

`audit_emitter.py` is a local, standard-library-only reproduction script. `audit-emitter-receipt.json` records exact audited hashes and counts; `audit-emitter-test.log` records the run. The literal test oracle enumerates each small source's template IDs directly through pinned `gate_at`, independently of the production candidate-index discovery. Such F-enumeration is confined to the test oracle; it is absent from the certificate compiler.

The raw corpus includes both orientations of all 95 types of the smallest moving source, left/right increment and decrement reverse anchors, different dispatch-domain/commit-image tables, detector-boundary/multiple-hit cases, type-specific exactness boundaries, inclusive exclusion boundaries, and the frozen malformed cascade. For every fixture support the audit compares the entire emitted raw key/orientation map with both stored oracle data and independently enumerated literal templates. Every live descriptor's old and new endpoint sets are also checked against its actual pinned type.

Additional fixed-seed tests cover bitonic widths 1 through 17, negative/equal anchors, arbitrary live/false rows, power-of-two padding, conservation of complete row payloads, deterministic compaction, fully zero absent lane payloads, comparator and signed-pair boundary equations, and canonical-domain rejection at zero horizon. Compaction cases include multiple simultaneously occupied isolated lanes; the detailed receipt counts them.

The latest emitter relocation loads byte-identical pinned dependencies adjacent to `compiler.py` rather than through an absolute research-folder path. The gate formulas and semantics are unchanged. The current circuit additionally records coefficient bit/L1 totals and accumulates expanded SOS coefficients directly; these changes preserve the same residual list and polynomial. The receipt, rather than prose copied hashes, is authoritative for the exact tested versions.

No assertion of source-uniform efficiency independent of explicit source/guard size, logarithmic dependence on J, novelty, optimality, or public release follows from this audit.
