# Inherited native calibration: pinned proof texts

This directory makes the inherited mathematical dependencies of the
source34 twelve-integer construction easier to inspect. It is a provenance
supplement, not a new proof of the native compiler or an end-to-end formal
verification run.

`PROVENANCE.json` gives exact repository paths, immutable read commits,
URLs, byte counts, SHA-256 digests, Git blob identities, and the role of
every included source. Fourteen key files also match the SHA-256 and Git
blob identities recorded in the original source70 pin ledger. The main
read snapshot is ProveIt commit
`84e16e43092614bae262ca59651cb9d77e31a255`. The historical T4 bridge is read
at its explicitly cited commit `f0ae4e0991ca44a7bb4e5671d42e33d775e48035`.

The chain is:

1. The new carrier proof restores the signed source described in the
   already bundled scalar/interpolation/residue proofs.
2. `PROOF41.md`, `PROOF44.md`, the two scale/domain proofs, and the two
   ordinary Pell proofs identify the earlier arithmetic source and its
   signed canonical witness construction.
3. `COEFFICIENT_PROOF.md` gives the exact source34 coefficient adapter,
   geometric bounds, and controller. `FIXED_BLANK_67_PROOF.md` and the
   historical T4 bridge identify the inputless native/Pell interface.
4. `WANG943_LANGUAGE_AND_COMPILER.md` identifies its tile language with
   blank halting of the literal machine in `k215.tm`.
5. `k215_proof.md` and the dominated-calculus proof identify that machine
   halting with finite syntactic ZFC refutability. `KEndpoint215.lean` and
   `K215_FORMAL_README.md` identify the separately compiled upstream
   endpoints; their full imports and proof-assistant build outputs are
   intentionally not copied or rebuilt here.

**Coefficient warning.** The Wang-language, compact-layout, and T4 bridge
texts include historical coefficient geometries. Their language/interface
results are inherited. The actual numerals used by this package are only
the source34 `mixed-parity-unrounded-1064921` tuple, its already shifted
MF, and the two determinant scales supplied in the final coefficient
payload directories. Historical coefficient tuples must not be mixed.

The full upstream dependency closure is not bundled. Links inside these
unchanged proof texts retain their upstream relative context; use the
absolute pinned URLs in the provenance ledger when reading them outside
the repository. Original licenses and the K215 notice are included.

Run `python3 check_provenance.py` to authenticate these retrieved bytes.
That check verifies file identity only. It does not prove any unbounded
Pell, compiler, calculus, or consistency theorem.
