# Attribution and licensing

This research contribution was prepared for Vladimir Reshetnikov's
ProveIt repository. Its new prose, scripts, certificates, and construction
use the MIT No Attribution license in `LICENSE`.

The immediate starting point is ProveIt's unchanged
`K224_Construction_2026-10-20.zip`, obtained at commit
`49ee7cfdc8e0364c6db3614675d141d66f9350ed`. Its ancestry includes
ProveIt's Source116 logical proof subset, Source124/K225 runtime machinery,
and Elliot Glazer's K230 Rocq development pinned to
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`.

The two inherited runtime-engine modules and the original numbering map
are retained byte for byte and checked by the reproduction driver. The
complete K224 predecessor is preserved unchanged, including its sources,
provenance, manifests, and notices. In particular, the vendored K230
ancestry includes notices for LibTactics, the Undecidability library,
BusyCoq, and Wade. Those components retain their original license terms;
this contribution's MIT No Attribution license does not replace them.

The new contributions are the merged-G exact theory equivalence,
source/emitter adapter and address repair, the selected three-fold
226-to-223 construction, exact final runtime and blank-start adapters,
independent local checkers, and the additional equality frontends and
research documentation. No global priority or minimality claim is made.
