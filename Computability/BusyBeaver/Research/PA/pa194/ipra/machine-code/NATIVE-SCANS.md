# PA194 scanners in native iPRA

`PRAEqualityToIPRA.nativeOfClassical` proves a general transfer theorem: for
any arity and any two terms in the repo's primitive-recursive-code language,
a candidate classical PRA proof of their universally closed equality gives a
proof of that equality in the candidate native iPRA `standardTheory`.

The proof applies the existing Gödel–Gentzen translation to the classical
proof, instantiates the translated equality at arbitrary terms, removes double
negation using the established native-iPRA stability of bounded formulas,
and universally closes the resulting family. The result is an object-theory
derivability statement; the use of classical Lean metatheory and completeness
in constructing the original classical PRA proofs does not add a classical
reasoning axiom to the target iPRA theory. `Classical.choice` appears among
the Lean metatheoretic dependencies because the framework represents
provability by existence of a proof.

`PA194NativeScans.oneScan` and `PA194NativeScans.zero` apply this transfer to
the independently checked dense-state-1 and dense-state-15 scan identities.
The statements quantify over the tape halves and the scan length. These are
machine-specific local segments, not a full source-to-physical-machine
simulation or either direction of the desired consistency equivalence.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-native-scans.sh
```

The script regenerates the pinned machine table, rebuilds the segment and
transfer modules in a private directory, checks selected source and overlay
object hashes, and rejects `sorryAx`. Other transitive prebuilt overlay
objects are assumed to correspond to their recorded sources; the entire
foundation and iPRA dependency chain is not rebuilt by this replay.
