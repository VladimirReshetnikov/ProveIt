# Provenance and attribution

## Retained inputs

The principal upstream project is Vladimir Reshetnikov's **ProveIt**:

https://github.com/VladimirReshetnikov/ProveIt

The research catalogue was inspected at commit
`ad8cbe8249445f43408617e88a0edb668b00248d`. The unchanged input archive
`K225_Construction_2026-10-19.zip` was retrieved from commit `680f05870` under
`Computability/BusyBeaver/Research/ZFC/`. Its SHA-256 is
`75b58ce7b5840ef3a3158341f7cf1e601aab67d19ab147d96cf37d1186cb6cbc`.

That archive retains its own sources, manifests, ordinary runtime verification,
proof-assistant material, discovery code, and attribution. In particular, its
symbolic runtime and independent runtime engines are reused unchanged here.

The exact K230 formal endpoint was inspected in Elliot Glazer's development:

https://github.com/elliotglazer/k230-rocq

at commit `3142e4dd980f0be12f4abb636c4ae2528afc17eb`. The required source files
are already retained within the pinned K225 archive. Its own attribution credits
Mira, Vladimir Reshetnikov's ProveIt work, Andrew James Wade's compiler, Jeff's
busy-beaver reference development, BusyCoq, and the Coq Library of Undecidability.
Existing MIT, MIT X11, MIT No Attribution, and MPL 2.0 notices remain intact.
No additional license is asserted for upstream files without an explicit one.

The alternative-formalism comparison retains selected Source 116 documents from
ProveIt's `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/` at
the catalogue commit. Their exact hashes are in
`experiments/theory/selected_results_manifest.json`. Its membership-defined
equality and CP/GIC comparison are prior work, not new claims of this packet.

## New work in this packet

The DN4 source recipe, literal transition-table delta, standalone replay script,
source/formula verification, ordinary double-negation proof translation,
seed-invariant checker, auxiliary proof files, report, and recorded experiments
were prepared in this research session for incorporation into ProveIt.

The C++ local-fold search programs are adaptations of the retained upstream
discovery sources, changing the chosen start label and/or accepting externally
computed tape-window domains. They are untrusted discovery tools. No output is
accepted as a smaller consistency machine without the separate semantic,
startup, and unbounded-runtime obligations.

`proofs/PositiveTransport.v` is a generic theorem about deterministic transition
systems. `proofs/PairAdd2.v` proves an elementary arithmetic identity and a
composition of stated register contracts. Fresh compile and independent kernel
logs are included. Neither file asserts an end-to-end theorem about DN4 and ZFC.

The main report is an ordinary mathematical research document. Its claim of a
225-state consistency machine combines the inherited calibration with the new
written calculus proof and freshly replayed ordinary runtime verification. It
does not assert an improvement below 225 states or a new exact-machine kernel
endpoint.

## External mathematical references

- John Hester, *Automated ZFC Theorem Proving with E* (2019),
  https://arxiv.org/abs/1902.00818, for a primary comparison of NBG and ZFC
  theorem proving and the finite-axiom NBG option.
- The pinned K230 files `Codes230.v`, `CD230.v`, `Comp_Prop230.v`, `Enum230.v`,
  `Seed230.v`, `ProgLib230.v`, and `KCode230.v`, retained inside the original
  archive, supply the exact numeric logical rows, macro contracts, enumeration
  semantics, and compact-theory calibration used by the new proof.

The generic arithmetic-negation idea also appears in prior ProveIt Source 56.
This packet therefore records its particular 225-state-layout probes and helper
conflicts without asserting priority for that identity.
