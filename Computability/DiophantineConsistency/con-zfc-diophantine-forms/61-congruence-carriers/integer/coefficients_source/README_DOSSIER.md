# Complete coefficient binding for the 37-integer sextic and 34-integer octic

This dossier provides the whole, explicit numerical coefficient tuple required
by the two secondary reductions `../sextic37.json` and `../octic34.json`.
It also preserves exact historical comparison polynomials and their proofs.
It does not change either reduction or either polynomial.

## Active binding

The source Q45 is package 57's quartic guard reduction, whose own proof
explicitly selects package 34's **mixed-parity-unrounded-1064921** tuple.
The use of the larger tuple here is intentional. The main low-variable
constructions elsewhere in the deliverable can use a different complete
tuple; their individual ports must not be interchanged with these ports.

| Polynomial port | Fixed integer payload | Bit length |
|---|---|---:|
| `beta` | `generated_payloads/beta.bin` | 1,064,921 |
| `K0` | `generated_payloads/K.bin` | 1,065,043 |
| `MC` | `generated_payloads/MC.bin` | 1,064,921 |
| `MF` | `generated_payloads/MF_source.bin` | 1,064,922 |

Every payload is the minimal unsigned little-endian encoding of one fixed
integer. The accompanying `.bin.gz` files contain identical integers. In
particular, `beta=2^1064921-1` and `MF_source=MF_native+beta`: the high mask
is already shifted. Together the raw payloads use **532,479 bytes** and the
gzip payloads use **10,466 bytes**.

`ACTIVE_BINDING.json` supplies direct local paths and authentic hashes for
these two reductions. The `coefficient_binding` fields in the two original
reduction packets retain Q45's inherited package-relative source paths;
this dossier resolves those historical paths without editing the packets.

## Exact reconstruction and provenance

Thirty text source files were fetched through the GitHub connector and checked
against their Git blob identifiers. `TRANSFER_LEDGER.json` records every
local file, repository path, snapshot, full source URL, exact byte count,
Git SHA-1 and SHA-256. The primary retrieval snapshot is
`beb0192cb8dc36f78c369c080f2adfbc1887a486`.

The original coefficient builder and independent verifier are preserved
unchanged in `coefficients/`. The literal machine input `coefficients/k215.tm`
was recovered from the canonical K215 directory because the package's placed
copy was deduplicated out of its coefficient directory. Its expected SHA-256
is checked by both source programs. The ordered 943-tile input is also
preserved exactly.

The coefficient builder was run locally and the independent decoder was run
against its output. **Every regenerated raw payload, every gzip payload,
and the complete generated manifest match the historical package-34 binding
exactly.** This is stronger than merely matching the uncompressed integers.
Receipts are `BUILD_REPLAY.json`, `INDEPENDENT_REPLAY.json`, and
`EXACT_REPRODUCTION.json`. The independent decoder checks 69,230 native basis
identities, all 8,801 radix digits, the exact masks, the controller arithmetic,
and 73,511 finite coverage cases. These are finite arithmetic checks;
the unbounded compiler equivalence remains the inherited mathematical proof.

Reproduction from any working directory:

```sh
python3 /absolute/path/coefficients_source/coefficients/build_coefficients.py \
  --output /absolute/path/coefficients_source/generated_payloads
python3 /absolute/path/coefficients_source/coefficients/verify_independent.py \
  --payloads /absolute/path/coefficients_source/generated_payloads
python3 /absolute/path/coefficients_source/verify_dossier.py
```

The two preserved historical programs explicitly require a non-optimized
Python invocation. The new dossier verifier uses explicit checks and also
works under `python3 -O`. It authenticates all source bytes and all fixed
coefficients and rechecks the historical comparison counts and exact degrees.

## Historical comparison evidence

The historical files are recovered from package 29 at snapshot
`8c6eec9d19ef80538c8e61ff6e0180040583446a`, before the collection moved to its
current directory. The earlier package's own source snapshot is recorded
inside its unchanged JSON packets and proof. The literal packets, rather
than only a reconciliation README, establish the comparison:

| Construction | Integer variables | Residual equations | Single-polynomial degree |
|---|---:|---:|---:|
| Package 29, Q42 | 42 | 21 | 6 |
| New unit elimination, Q37 | 37 | 20 | 6 |
| Package 29, Q36 | 36 | 15 | 8 |
| New unit elimination, Q34 | 34 | 17 | 8 |

Thus the sextic saves five integer variables (11.90%), and the octic saves
two (5.56%). The octic uses two additional residual equations; neither
comparison should be described as improvement in every metric. The new
constructions are derived from Q45, not by a claimed direct bijection with
the historical Q42 or Q36. Those historical equations also use a different
complete coefficient tuple. The count comparison is nevertheless meaningful
because the domains and total degrees agree and each has its own claimed
consistency equivalence.

The new verifier expands the old Q42 and Q36 polynomials with symbolic ports,
checks their 42/36 variable counts, 21/15 residual counts, residual degrees,
exact degrees six/eight, and the recorded nonzero leading coefficients.
It confirms their 467/845 symbolic monomial counts. The complete ordinary
historical proof is preserved as `low_degree/upstream/ODD_SCALE_LIFTS_PROOF.md`.

## Proof and attribution boundary

The package-34 coefficient adapter, package-34 quartic50 reduction, the
historical odd-scale lift proof, its signed-domain and odd-scale dependencies,
the Wang-language descriptions, and the original notices and licenses are
included. This is a self-contained finite numerical reconstruction and
local algebra package with explicit mathematical dependencies. It is not
a complete standalone Lean/Rocq build of the compiler or of ZFC syntax.

Original notices are retained under `licenses/`, together with the package-34
root `LICENSE` and `NOTICE.md` and package-57 notices. Newly written dossier
material and reduction code follow the repository's MIT No Attribution terms.
