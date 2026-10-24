# Literal coefficients for the integer sextic

This directory supplies the **complete** source34 coefficient tuple for
the integer equation.  It is an offline, Python-standard-library bundle:
all four actual numerals are included as raw and compressed binary data,
and both their construction and independent decoding are reproducible.
No search for a halting computation is performed.

## Use and reproduce

From this directory run:

```sh
python3 build_coefficients.py
python3 verify_coefficients.py
```

Both entry points also work with `python3 -O`; their checks use explicit
exceptions.  The first authenticates the 35 copied source/proof/notice
files, reconstructs all 943 tiles from the complete 430-action machine,
checks 69,230 finite convolution identities and the controller's finite
hypotheses, and regenerates all payloads.  The second uses the preserved
independent upstream decoder, which does not import the constructor.  It
checks all 8,801 digits of the actual transport constant, all masks,
machine-to-tile equality, geometry, carry bounds, controller orders and
unit residues.  The reports are `BUILD_CHECKS.json` and `VERIFICATION.json`.

Use the four ports exactly as follows:

| Polynomial port | Compressed literal file | Bitlength | Raw bytes |
|---|---|---:|---:|
| beta | `payloads/beta.bin.gz` | 1,064,921 | 133,116 |
| K0 | `payloads/K.bin.gz` | 1,065,043 | 133,131 |
| MC | `payloads/MC.bin.gz` | 1,064,921 | 133,116 |
| MF | `payloads/MF_source.bin.gz` | 1,064,922 | 133,116 |

The decompressed format is the minimal unsigned little-endian integer
encoding.  The four raw files total 532,479 bytes; their compressed files
total 10,466 bytes.  Every raw **and** gzip SHA256 agrees with the
historical source34 manifest.  Compression is storage only and is not a
reduction in mathematical coefficient height.

`COEFFICIENT_BINDING.json` binds these files to the polynomial names.
Its complete-tuple SHA256 is

```text
b61ee51bdd2d9e4274db603b64cb1d092a8f5feeb83f510433876f21fea2c85f
```

The canonical length-delimited digest encoding is specified in that
manifest and implemented in `provenance.py`.  In particular **MF is the
already shifted high mask**.  It must not be replaced by the native high
mask, and no port should be taken from a different compiler generation.

For example, after running the verifier, fixed integer values can be read
without decimal conversion:

```python
import gzip
from pathlib import Path
p = Path('payloads')
ports = {port: int.from_bytes(gzip.decompress((p/file).read_bytes()), 'little')
         for port, file in {'beta':'beta.bin.gz', 'K0':'K.bin.gz',
                            'MC':'MC.bin.gz', 'MF':'MF_source.bin.gz'}.items()}
```

## Exact finite coefficient specification

Let b=121, L=8801, d=bL=1064921, rho=2^121, and B=2^d.  The ordered
943 tiles, with edge order (west,north,east,south), are the authentic
`upstream/source34/wang943_tiles.json`.  Their order is material: tile0
is Start and tile1 is Forbidden.

Put W_j=2^(10+2j), for 0<=j<44, and

```text
(o_0,o_1,o_2,o_3)=(1020,1000,980,960),
E={0,...,942} union {o_t+2j: 0<=t<4, 0<=j<10}
  union {1063,1064,1095,1096,2195,3296}.
```

For the tile with index e<943 and labels x_(e,t), define

```text
c_e = 1 + sum_{t=0}^3 sum_{j=0}^9 bit_j(x_(e,t)+512)*W_(10t+j)
          + sum_{j=40}^{43} W_j.
c_(o_t+2j)=W_(10t+j).
(c_1095,c_1096,c_2195,c_3296)=(W_40,W_41,W_42,W_43).
c_1063=c_1064=0.
mu=1022+sum_{j=0}^{43}W_j.
Z=(2^119-1)*sum_{e=8792}^{8798}rho^e+(2^27-1)*rho^8799.
```

All four polynomial ports are fixed by the following finite formulas:

```text
DC=rho^40+rho^41+rho^1100+rho^2200
   +sum_{e in E} c_e*(rho^(4393-e)+rho^(5495-e)).
DR=rho.
MC=B-1-sum_{e in E,e!=1}rho^e-2*rho^1063.
MF_native=4+mu*(rho^4393+rho^5495)
          +sum_{j=0}^9(rho^(1000+2j)+rho^(1021+2j))
          +rho^2195+rho^3296+Z.

beta=B-1;  K0=DC+B*DR;  MC=MC;  MF=MF_native+B-1.
```

These equations are the source34 recipe with the source's entire tuple
preserved.  `upstream/source34/build_coefficients.py` and its independent
checker are exact upstream Git blobs.  The wrapper uses an explicitly
specified zero-timestamp, level-nine, Unix-header gzip encoding to match
the preserved gzip hashes as well as the authoritative raw numeral hashes.

## Selected inherited mathematical dependencies

The new sextic's local algebraic proof and its complete compiler
calibration have different scopes.  The bundle includes the following
direct ordinary-proof dependencies; the rest of the transitive ProveIt
formal project remains identified by their pinned references.

| Included document | Role |
|---|---|
| `proofs/PROOF41.md` and `PROOF44.md` | Source integer system, common-sign Pell argument and delayed radix-sign recovery |
| `proofs/COEFFICIENT_PROOF.md` | Full mixed-parity tuple adapter, native soundness, canonical completeness and rank controller |
| `proofs/WANG943_LANGUAGE_AND_COMPILER.md` and `WANG943_COMPACT_LAYOUT.md` | Literal marked tile language, padding and native layout |
| `proofs/ODD_SCALE_27_PROOF.md` and `SIGNED_DOMAIN_29.md` | Odd cubic scale, signed-root restoration and auxiliary rank recovery |
| `proofs/FIXED_BLANK_67_PROOF.md`, `ORDINARY_BLANK_PROOF.md`, `BLANK_HELICAL_PROOF.md` | Positive Pell/native interface and canonical witnesses |
| `proofs/PELL_RELAXED_AUXILIARY_PROOF.md` and `EXPLORATION_FIXED_MINUS_INDEX_PARITY.md` | Ordinary strong-rank lemma and signed Pell congruence step-down |
| `proofs/K215_ORDINARY_CALIBRATION.md` | Inherited ordinary calibration of the literal machine to finite ZFC refutability |
| `proofs/QUARTIC45_PROOF.md` | Immediate predecessor of the source44/source41 system |

`SOURCE_PINS.json` gives the exact source paths, commit, Git blob SHA1,
SHA256, byte count and pinned URL for every copied file.  Copied contents
and notices are unchanged; some of their relative links assume the
original repository layout, so use this ledger to resolve those links.

The independent finite checker confirms the concrete arithmetic data and
finite prerequisites.  It does not prove the universal compiler theorem
by testing, decide consistency, or supply a new end-to-end formal ZFC,
Lean or Rocq certificate.  The selected ordinary proofs state the
unbounded mathematical bridge being inherited.

## Attribution

See `NOTICE.md` and `licenses/`.  The exact original source34 and source64
notices, ProveIt license, Wade license and machine/source notices are
preserved.  The reconstruction wrappers and integration manifest are new
packaging; the literal tiles, coefficients, native compiler, Pell
interfaces and machine calibration retain their upstream provenance.
