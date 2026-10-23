# Attribution and scope

This component is for Vladimir Reshetnikov's ProveIt repository, reviewed at
commit `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

The register semantics, segment lemmas and finite-run induction descend from
the repository's K230/K215 formalization and its Jeff/Wade/BusyCoq ancestry.
`LookupNormalized.v` adapts the maintained `K215F.NormalizedBisim` argument;
`PathEq.v` copies its path utility block verbatim. Literal programs, path codec
and certificate data are unchanged current inputs. `source_bindings.json`
identifies every copied file.

The smaller lookup-coverage interface was already proposed in
`verification/k215/simplification/proposals/guarded-core/refinements/REVIEW.md`
and `proposals/sharing-interfaces/structural/INTERFACE.md`. The existing Lean
`RMBisim.lookupC_all` is a checked precedent. Prior `proof-refinements`,
`proof-core` and `composition-address-bounds` packets already supply checked
normalized balanced lookup via list refinement. The contribution here is the
direct Rocq completion and current literal source check, not discovery of those
ideas or of the certificate.

Inherited notices and license texts are retained in `licenses`. They preserve
the original authors, third-party terms and the documented limits of the
upstream license scope; new local material does not relicense inherited code.
Original additions may be incorporated under ProveIt's MIT No Attribution
terms. The compiler and its standard library are external installed tools.

Reviews in this collaboration are separate source-review work, not an external
human endorsement. The exact compiler receipts determine the validation scope.
