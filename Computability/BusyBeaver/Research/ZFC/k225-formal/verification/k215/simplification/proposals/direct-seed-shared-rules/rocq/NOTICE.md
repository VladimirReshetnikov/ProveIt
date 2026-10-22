# Attribution and source scope

The 71 condensed-detachment derivations are Jeff's `ZF/stdzf/coq/L1_LProp.v`
at busy-beaver commit `c132d7eae8158cd3a9850ea3eb7251158c3dd821` and their
ProveIt `L224Prop.v` adaptation. This packet factors those existing proofs;
it does not claim them as new mathematical discoveries.

The named syntax and standard calculus/metatheory inputs are the same pinned
Jeff sources. The numeric-code dependency is Elliot Glazer's `KCode230.v`
at k230-rocq commit `3142e4dd980f0be12f4abb636c4ae2528afc17eb`, normalized
from CRLF to LF. The restricted named-calculus inputs are from ProveIt commit
`6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`. Exact paths and SHA-256 values are
in `evidence/source_manifest.json`.

ProveIt's existing license is preserved in `licenses/LICENSE.ProveIt`.
The upstream K230 attribution text is preserved in
`licenses/THIRD_PARTY.k230.md`; in particular it records that no explicit
license notice was found for the reference's custom standard-ZF files. This
packet does not relicense those inherited portions or assign a blanket license
to them. Coq and its standard library remain separately installed dependencies.

New contribution: one abstract propositional interface; the two concrete
instances and exact-name facades; replacement of the proof-only equality atom
by a bound formula; the complete compatibility client; and reproducible
generation, checking, source-binding, and measurement scripts.
