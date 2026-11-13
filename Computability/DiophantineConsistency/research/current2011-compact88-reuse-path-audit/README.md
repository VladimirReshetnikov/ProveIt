# Compact 88/30 reuse for the current-2011 endpoint

The inspected compact 13/88/30 native iPRA endpoint is a **source-only,
unelaborated proposal**, not an already checked endpoint. Its proposed local
same-valuation zero equivalence is nevertheless port-parametric and presents
a possible reuse route. This is a bounded source audit, not an exhaustive
search of every filesystem or historical run.

## Exact interfaces and port boundary

* `P88FourSquareModel.zero_iff (p : Fin 4 → ℤ) (v : Fin 13 → V)` proposes
  equivalence of internal zeros of the four-square graph and `P88Pair.graph`
  at the same arbitrary signed port tuple and same valuation in an IΣ₁
  model. It calls the **unelaborated** `P88PairModel.zero_iff` and compact
  factor-unit source interfaces. The local graph and model sources are in
  `ordinary13-freej88-four-square-lean-draft` and `ordinary13-freej88-lean-draft`.
* That draft's `expression` fixes `CompactSymbolicModelIff.p`, and its
  `positiveBridge` and proposed endpoint therefore concern this compact tuple,
  not arbitrary `p`. `CompactSymbolicPorts.ports` gives `[β,K,L,β+H]`.
  The compact β is `2^(67*8807)-1 = 2^590069-1`; current-2011 β is
  `(2^47)^2011-1 = 2^94517-1`. These are unequal. The compact endpoint
  cannot simply be instantiated at the current tuple.
* `Compact44/IPRAOrdinary13.lean` is a retained **87-operation** endpoint
  for `FreeJ13.graph` at the compact tuple, not a checked 88/30 endpoint.
  The recorded author-side endpoint replay and its unpaired/inherited provider
  limitations are described by `ordinary13-freej87-endpoint/README.md`.
* The current source-only endpoint draft instead applies
  `AdaptiveFourSquare88ModelDraft.bridge` to the current-port
  `HAAdaptiveFactor87.polynomialBridge`, then proposes native, standard and
  mapped Gödel–Gentzen translated conclusions. Its graph/model and its endpoint
  client have not been elaborated together. The matched peer endpoint evidence
  has the further provider qualifications in `ha87-focused-peer-mismatch-audit`.

## Concrete possible source reuse

The compact and current JSON graphs use the same 13 witness names and the same
four *formal* port positions. Their 87-row parent graphs share all rows except
28–34, and the seven differing rows compute the same ring polynomial
`M*(g31-k*Bt) + Y*qm - q3*Bt`. For their 88-row four-square graphs, rows 0–27
and 35–75 agree; the same first-root identity applies at 28–34; rows 76–79
use the identity `u*((V+u)+V) = (V+u)^2-V^2`; and the final sum of four
squares differs only by association and evaluation order. The checker proves
these **local free commutative ring polynomial identities** with a sparse
integer-polynomial calculation and checks the remaining row equalities. This
establishes the indicated JSON-level all-port ring equality, not a Lean theorem
about either generated `Expr` or the PDF.

One could elaborate the compact model drafts, prove the corresponding generated
expression/evaluation equalities for the 87- and 88-row graphs at a common
arbitrary port tuple, instantiate the local equivalence at the current tuple,
and use the current 87 bridge rather than the fixed compact positive bridge.
That route needs the compact pair-model and four-square-model source chain,
its unit/factor lemmas, both graph-to-expression bindings, and a coherent
selected provider closure. It remains a proposal: it does not demonstrate a
shorter build or discharge the current draft's obligations. The existing
compact provider survey is a bounded source/record inventory; its historical
roots and differing selected objects do not authenticate a coherent build for
these additional drafts. The same warning applies to current-provider ancestry.

## Reproduction and scope

From `Computability/DiophantineConsistency`, run
`python3 -I -S -B research/current2011-compact88-reuse-path-audit/check.py` and
compare stdout with `receipt.json`. The checker verifies 30 pinned inputs,
reproduces two existing source receipts and the compact 87 graph generator
check, and performs the exact row, local polynomial and beta-exponent checks.
The source signatures are inspected as text. The JSON-to-Lean correspondence
is not established by the local algebra alone. No Lean, build, provider replay,
axiom check, formal iPRA derivation, or PDF semantics was performed here.
