# Compact fixed coefficients for the positive equations

This directory supplies one complete, explicit coefficient tuple for the
new positive equations. Its active instance is

`wang943-complement67-shared-anchor-length8807-prime581197`.

All upstream files were retrieved from VladimirReshetnikov/ProveIt at
commit `9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`. Their bytes agree with
the SHA256 and Git blob pins recorded by source64's positive14 package.
`UPSTREAM_FILES.json` retains those historical pins and separately records
the actual retrieval commit and current source paths. Four additional
source61 proof files are included and authenticated at the same current
commit. Upstream source files, licenses, bindings, and compressed payloads
are preserved byte for byte.

## 1. Exact binding and coefficient sizes

The polynomial leaves `beta`, `K0`, `MC`, and `MF` must receive all four
values in the following table. The names `K` and `MF_source` belong to the
upstream payload convention.

| Polynomial leaf | Upstream port | Payload below `native/` | Bits | Raw bytes | Gzip bytes |
|---|---|---|---:|---:|---:|
| `beta` | `beta` | `coefficients/beta.bin.gz` | 590069 | 73759 | 108 |
| `K0` | `K` | `coefficients/K.bin.gz` | 592884 | 74111 | 8940 |
| `MC` | `MC` | `coefficients/MC.bin.gz` | 590069 | 73759 | 193 |
| `MF` | `MF_source` | `coefficients/MF_source.bin.gz` | 590070 | 73759 | 204 |
| **Total** | | | | **295388** | **9445** |

Each uncompressed payload is the minimal unsigned little-endian encoding
of its integer. Thus the literal value is
`int.from_bytes(gzip.decompress(path.read_bytes()), "little")`.
The preserved upstream gzip files use a zero timestamp.

With `rho = 2^67` and `B_native = 2^590069`, the conventions are

```text
beta = B_native - 1
K0   = DC + B_native * DR
DR   = rho^42
MC   = MC_native
MF   = MF_source = MF_native + B_native - 1.
```

The `MF` payload already contains the native-to-source shift. It must be
inserted directly. The whole-tuple binding is
`native/COEFFICIENT_BINDING.json`, whose SHA256 is
`0599543212b8d2bbed2db018a29d6826702e1877faa5c8a1861d041998cb1783`.
`POSITIVE_PORTS.json` provides the same aliases and payload hashes in a
small integration manifest.

These four integers are fixed coefficients, not quantified variables,
unspecified program indices, or values obtained by running the machine.
The arithmetic in the builders is finite and independent of whether
ZFC is consistent. The uncompressed payloads together occupy 295388
bytes; their bit counts should not be mistaken for the size of their
compressed descriptions.

## 2. Exact finite reconstruction

Run from this directory, using Python 3.10 or newer:

```bash
python3 verify.py
python3 -O verify.py
```

To record a fresh receipt and save newly generated payloads to a directory
that does not already exist:

```bash
python3 verify.py --receipt local-checks.json --regenerate rebuilt
```

No downloads or third-party Python packages are needed. The wrapper
authenticates all 44 preserved source files by SHA256 and Git blob SHA1,
checks the complete active tuple and the original compressed files, and
then runs the unmodified source44 builder in a temporary copy. It compares
the regenerated raw bytes with every preserved payload. It subsequently
runs the unmodified, independent source44 auditor, which reconstructs the
integers directly from the pinned literal tile list without importing the
builder. The resulting audit receipt must equal the preserved upstream
receipt.

The included `REPRODUCIBILITY_CHECKS.json` was produced by this procedure.
All four raw payloads and all four gzip payloads were byte-identical to
upstream. Different Python or zlib versions can produce a different gzip
stream encoding the same bytes. In that case verification still requires
the exact original raw integer hashes, and the fresh receipt identifies
the different compressed hashes. The original payload files remain
unchanged.

The independent auditor authenticates 12 historical dependencies,
matches all 430 literal machine transitions, verifies 66062 native basis
conditions, checks 38663 single-bit mutations and 87380 finite complement
models, certifies the padding-controller arithmetic, and checks the
unchanged predecessor evaluator sources. These finite checks supplement
the universal mathematical arguments; they do not establish those
arguments by testing examples.

## 3. Native dimensions and controller

| Parameter | Fixed value |
|---|---:|
| Wang tile count | 943 |
| Literal binary machine transitions | 430 |
| Radix bits `b` | 67 |
| Cell length `L` | 8807 |
| Cell width in bits `d = bL` | 590069 |
| Native support size | 986 |
| Clause target exponents | 4393, 5495 |
| Shared anchors | 1095, 2195, 3296 |
| Spatial shift exponent | 42 |
| Padding prime | 581197 |
| Controller step | 581196 |
| `MC_native` population | 589083 |
| `MF_native` population | 986 |

The complete finite recipe is the preserved
`native/build_coefficients.py`; its inputs are the preserved literal
transition data. The independent recipe is
`native/audit_coefficients.py`; its main input is
`native/source/coefficients__wang943_tiles.json`.

## 4. Source contract needed by the positive endpoints

The new 13-positive-variable and 12-positive-variable constructions use
the normalized source interface described in
`upstream/positive61/PROOF14.md`, then the source61 transport carrier in
`upstream/positive61/PROOF13.md`. The local new proofs supplied alongside
those equations perform the further carrier and centered-norm changes.
The relevant inherited proof dependencies in this directory are:

| File | Role |
|---|---|
| `native/PROOF.md`, sections 1–6 | Complete compact native tuple: complement decoding, overlap geometry, carry bound, mask population, actual-rank padding controller, and canonical promises |
| `native/PROOF.md`, section 7 | Substitution of this entire tuple into the inherited arithmetic compiler; displayed positive source system |
| `native/source/coefficients__PROOF.md`, section 6 | Canonical square scale, odd normalized and ordinary multipliers, and odd `s = Y/q^3` |
| `native/source/coefficients__source_proofs__WANG943_COEFFICIENTS.md` | Literal marked Wang language and inherited native compiler interface |
| `native/source/coefficients__source_proofs__WANG943_COMPACT_LAYOUT.md` | Inherited compact layout dependencies |
| `upstream/PELL_LEMMAS.md` | Pell classification, rank extraction, and inherited large-index facts |
| `upstream/ORDINARY_KERNEL.md` | Ordinary arithmetic compiler proof |
| `upstream/SQUARED_MODULUS_PROOF.md` | Squared-modulus recovery used in later source interfaces |
| `upstream/FOURTEEN_PROOF.md`, `upstream/FOURTEEN_GAP_PROOF.md` | Intermediate rank and positive-gap interfaces |
| `upstream/TRANSPORT_SHIFT.md` | Native/source transport and mask-shift convention |
| `upstream/INTEGRAL_ROOT_REPORT.tex` | Source58 integral-root interface and completeness constructions |
| `upstream/positive61/PROOF14.md` | Normalized positive source contract and independent rank argument |
| `upstream/positive61/PROOF13.md` | Positive13 transport carrier and source recovery |
| `upstream/positive61/AUDIT12.md`, `SIGNED_INDEX_LEMMA.md` | Signed norm branches, auxiliary rank recovery, and canonical parity |

In particular, `native/PROOF.md` section 6 explicitly transfers the
canonical identities `pc(R) = 3dN + 2` and `R = 3 mod 4`, and the square
and odd-scale promises from source36. The proof in
`native/source/coefficients__PROOF.md` section 6 spells them out:
`N` and `d` are odd, `t=dN`, `q=2^t`, `X=2^R`, `R>t`,
`X/q=2^(R-t)` is a positive square, the canonical normalized and ordinary
multipliers are odd, and `v2(Y)=3t`, so `s=Y/q^3` is odd. Consequently
the canonical `w=X/q` is divisible by four: `R-t` is a positive even
integer. The canonical `J=(q-1)/(B_native-1)` is odd and is 1 modulo 3,
because it is a repunit of odd length in the even base
`B_native = 2 mod 3`; hence `J = 1 mod 6`.

These are canonical completeness promises. The native soundness proof
also covers arbitrary decoded witnesses; it does not require every
witness to have the canonical prime-power dimensions.

The coefficient reconstruction is self-contained and executable offline.
The Con(ZFC) equivalence composes the named ordinary mathematical proofs
with ProveIt's inherited literal K215/refutation calibration. The bundle
does not claim a new end-to-end proof in a proof assistant. The machine
table and its provenance are included as
`native/source/k215.tm` and `native/licenses/NOTICE_K215.md`.

## 5. Preservation, aliases, and licenses

The active tuple is the 590069-bit compact source44 tuple. Historical
source files in `native/source/` also discuss their own predecessor
tuples; they are retained for the upstream audit and proof provenance.
They are not alternative active bindings. In particular, the
1064921-bit mixed-parity tuple used by some unrestricted-integer
predecessors is a different whole tuple. A separately proved adapter is
required to instantiate one of those equations with the compact tuple.

`native/COEFFICIENT_BINDING.json`, `native/SOURCE_PINS.json`, and
`native/INDEPENDENT_AUDIT.json` retain their original contents and source
commit fields. `UPSTREAM_FILES.json` records the later retrieval pin
without rewriting those historical records. The verification wrapper
does not edit preserved source files.

The upstream MIT No Attribution licenses and notices are retained under
`native/licenses/`, together with `native/NOTICE-upstream.md`.
The new verification wrapper and integration files are distributed under
the same MIT No Attribution terms in `LICENSE`.
