# Sign24 Lean degree upper-bound guarded candidate

Two source-only stages propose the generic syntactic degree bound and the
concrete abstract/current sign24 expression degree upper bounds. The runner
binds the current expression definition to its audited producer, and uses the
reviewed sign24 bridge environment as base. It retains `-M3600`, 4 GiB sampled
RSS, 10 GiB host floor, timeout and disk guards. No theorem is claimed before
Lean and independent terminal audit; this is not an exact lower bound or a
JSON/PDF binding.

Author no-Lean preflight exited 0 for two stages. Runner SHA-256:
`f7a888fbbabac8ecc1d56cddf7918de8ea91187d72511798cf16a71a090c2524`.
Manifest SHA-256:
`10676c339feb4f60c1c1bc260068e282d941125d52a58883d57c2bffc33640d2`.
Expression survey SHA-256:
`95df75084d293ce32734fb75d5a9b8798ff2bc16566b432aa91f585ccec275f7`.
Independent prelaunch review and an assigned Lean slot are required.

Attempt 01 compiled the generic bound then timed out at the concrete syntax
degree proof; see [`attempt01`](attempt01/README.md). Overall exit was 1 and
the failed module's reports include `sorryAx`. The [independent prelaunch
review](../../reviews/nine-sharing-sign24-degree-upper-prelaunch-independent/README.md)
and [partial terminal audit](../../reviews/nine-sharing-sign24-degree-upper-terminal-independent/README.md)
record the successful generic child and failed concrete stage.
