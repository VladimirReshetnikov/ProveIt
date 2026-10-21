# Zero-spare transfer215 reproducibility component

This component packages the calibrated append-zero transfer machine: 201 source
DAG nodes, 4,775 primitive occurrences, 6,209 guarded cases, and 215 working
states plus a separate halt label. It is a new physical resource policy and
blank initializer for the unchanged transfer language. It is not a state
reduction below 215, a new calculus, or a claim of unconditional nonhalting.

## Exact machine

- Native table: machine/zero_spare_transfer215.native.tm; blank start 74,
  halt label 254. SHA-256:
  29a6ed4a594d7f974cf267a9e6b665af34c9afd8dd7abbbecf0b538ecab151e0.
- Canonical table: machine/zero_spare_transfer215.tm; blank start 0,
  working labels 0 through 214, halt label 215. SHA-256:
  60eae1c30d214f71c65a207087dc716ba4cdad2a1a62c51e9e107434a0ceb4f1.
- Source: source/transfer201.sites.json. SHA-256:
  05e7caa159d95cdf9ee254d313c44c52369ac91e52cbc23d54b15f0b64b95922.

Every CI appends one physical spare with value 0 rather than 1. The spare
suffix is not the logical theorem stack: neither this change nor the
initial spare values change the source command equations or field encoding.
Relative to the inert append-one transfer215 input, the only row change is
native (198,0) from (write 1,left,40) to (write 0,left,40); the designated
native blank-start state changes from 0 to 74. No state or row is deleted.

## Replay

Python 3, standard library only, assertions enabled. From this directory:

    python3 -I -B verify.py --runtime --work /absolute/path/to/new/output

The output directory must not already exist. Omit --runtime for finite
checks. The complete replay takes about two minutes on the preparation
machine; speed varies. It writes FULL_REPLAY_PASS in output/replay.json.
MANIFEST.json checks the exact sizes and SHA-256 hashes of the shipped
component. SHA256SUMS additionally pins the manifest. Neither file purports
to provide a digital signature or independent authenticity guarantee.

No network, installation, optimizer, received-code execution, external
repository, or environment-selected input directory is needed. All executed
checker code and inert inputs are included. The isolated preparation replay
used a fresh dependency-closed copy, an empty external environment, Python
-I -B, and a working directory outside the component. The original owned
runtime helper/kernel are retained byte-for-byte for auditability. Their old
standalone entry points and historical path defaults are not invoked;
verify.py imports only their pure table/frame/arithmetic/symbolic functions.

The full replay verifies:

1. Deterministic source reconstruction; two independent CFG calculations;
   four closed-body transports; all 6,209 physical/source successor bindings.
2. Literal table reconstruction; 430 complete rows; all 215 working states
   graph-reachable; the exact native/canonical bijection and supplied maps.
3. All 73,172 blank transitions with sparse-native, dense-native and
   sparse-canonical simulations; exact whole tape and zero exterior.
4. The complete 177-primitive source prefix into the first AX, finite
   command/credit corroborations, and the inherited dominated-row certificate.
5. Fresh all-natural primitive checking, four fresh finite-list one-block
   schemas, 6,209 cases, 1,611,489 symbolic rules, and all 430 table rows.
   Row coverage includes the 12 rows occurring in the one-block schemas;
   these are already a subset of the 430 directly used case rows.

The deterministic compressed census is evidence/runtime_cases.json.gz.
Its uncompressed SHA-256 is
97377f25c4da0a9979f4e8c34a8c9d7164303eba720d7c72a21310c5e889aa54.
The runtime domain is independent natural register values at each decrement
guard, arbitrary natural extra gap, arbitrary first spare value and arbitrary
finite remaining spare list, with the entire tape and zero exterior.
Proof-construction loop bounds do not bound actual runtime or those values.

## Startup and mathematical boundary

The exact reached frame is ordinal 119, native state 84, canonical state 81,
head -2, logical registers (N,T,W,A,D,H,X,Y,L)=(0,6,0,0,1,1,10,1,0),
gap 0, 65 physical spares [0,0,1] followed by 62 zeros, and 107 one-cells.
A 177-primitive AX prefix from ordinal 25 and registers
(0,0,0,0,1,1,0,0,0) reaches precisely that logical continuation. This is not
a claim that the hypothetical earlier AX prefix had the same physical
spare history as the actual blank execution.

The inherited all-natural AX contract completes this special AX. Its top
is the enabled Bundle(1,1,0), and its first eight stack heads are retained
axioms. The remaining numerical tail is 171, including Q_1(1)=18, which is
not presumed to be a theorem. At the resulting scheduler root N=0 and the
proof pointer is empty. The proved credit debt d(0)=3 leaves a permanent
margin of five safe theorem heads. The unsafe suffix is never exposed.
The unchanged strong transfer compiler accepts arbitrary underlying stacks
and has successful candidates beyond every cutoff.

Together these establish the ordinary mathematical blank-start calibration
with the identified inherited numerical-calculus and arithmetic-macro
premises. The exact source, physical runtime, startup bridge, compiler and
protected-credit argument are distinct obligations. A finite sample alone
does not prove any universal premise. No new Lean/Rocq endpoint, internal
PA proof-code theorem, absolute consistency proof, or minimality result is
claimed. See proofs/README.md for the complete proof dependency sequence.

## Contents and attribution

- inputs/: inert predecessor source/table, literal reconstruction baseline,
  label map and fixed logical certificate.
- source/ and machine/: exact source, two tables and canonical maps.
- checks/ and verify.py: owned executable checkers and literal row recipe.
- evidence/: runtime aggregate/census/coverage, exact blank witnesses, source
  bridge, independent startup receipt, finite corroborations, clean replay.
- proofs/: current source binding/startup proof, independent startup review,
  unchanged transfer compiler and general protected-credit induction.
- provenance/: identified inherited calculus/macro dependencies and original
  attribution notices. Historical paths are archival references, not replay
  dependencies. The historical full parent archives are not bundled here.
- licenses/: retained licenses/notices and their pins; see its README.
