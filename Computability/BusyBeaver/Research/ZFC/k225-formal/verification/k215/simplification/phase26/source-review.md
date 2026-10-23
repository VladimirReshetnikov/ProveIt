# Source review

The changes shorten existing proof bodies in five maintained modules. All
retained public declarations keep their names, binder names, types and attributes;
imports and computational definitions are byte-identical. The full selected kernel build and exact profile checks pass as recorded in
the [phase README](README.md).

| Module | Proof simplification | Lines removed | Bytes removed |
|---|---|---:|---:|
| `FirstOrder.Completeness` | Existing context-list constructors, append inclusions and sentence-renaming identities replace repeated membership and weakening arguments | 56 | 1,091 |
| `InternalRank` | One inclusion proof serves both equality directions; one subset bound shares the extension's recursion-witness transport | 12 | 487 |
| `BoundedZFCConsistency.InternalSatTotality` | Structural semantic congruences replace two witness transports; outer truth bits are decoded before connective congruence | 43 | 1,676 |
| `KZipTape` | Index induction reuses existing head and tail normalization | 7 | 100 |
| `KHomeReady` | Two single-use private certificate arguments are inlined in `ready_sound` | 8 | 357 |

No helper declaration or framework is introduced. The only retired declarations
are the private `KHomeReady.rowsCheck_sound` and `boundary_of_check`, whose proofs
now appear directly in their sole caller. Public single-use lemmas are retained.
`InternalOrd` was audited and remains unchanged.

The rank argument preserves its ordinal/domain bounds and arbitrary recursion
relation. The satisfaction argument keeps the same environment guards,
certificate closure and slots: `0/3` for environments, `0/3/4` for closure and
`4/1/0/2` for triple membership. Its congruences have constructive implementations;
the selected compiler profiles match the accepted phase25 reports. The runtime changes preserve
the exact Home rows, window, arbitrary right frame and step count. Their checker,
executor and fallback definitions are unchanged.

The separate phase25 paired-decrement experiment changes certificate computation
and remains unadopted. Its three-block result supplies no full-batch acceptance
or general speed claim, and contributes no savings to this proof-only batch.

The first focused attempt omitted two explicit target-context arguments to
`Prov_weaken`. The second exposed a rank variable eliminated by dependent
substitution. Two inferred contexts and two inferred coordinates repair these
elaboration issues. Both failed runs and the original source peers remain
historical; the repaired sources pass the focused and full kernel builds.
