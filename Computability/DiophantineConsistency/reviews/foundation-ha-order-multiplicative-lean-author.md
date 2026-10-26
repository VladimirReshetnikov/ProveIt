# Multiplicative order image in HA — author receipt

Author: `circuit_reduction`; author validation, not independent review. I
read the complete new main, checks, build and freeze drivers before execution.
Only new owned files and private links were written; frozen source, vendor
files, shared objects, umbrellas and Git state were not changed.

| Source | Lines | SHA256 |
|---|---:|---|
| `FoundationHAOrderMultiplicative.lean` | 91 | `d7d0de75f9023ab6391e6f6c0577dbf155ae9db00125d6771cedf9f09722427f` |
| `FoundationHAOrderMultiplicativeChecks.lean` | 75 | `b4e6962590596fbb4e56043edc139ce60db23df7dae39b5310a3162c6b987180` |

Both are under `Lean/DiophantineConsistency/`. Both first fresh builds passed
with `-M6000 -j1 -DElab.async=false` and a 512 MiB reserve. Main output is
empty; the 14 final check reports have no diagnostics and only standard
axioms. The ordinary and negative witness helpers use only `propext` and
`Quot.sound`; the actual source endpoint inherits `Classical.choice` from
the explicitly audited existing Foundation implication equivalence. No
custom axiom, `sorryAx`, model oracle, native decision or classical HA rule
is used.

Private overlay: `/tmp/foundation-ha-order-multiplicative-x427kf4a/lib`.
Fresh main object:
`663bf82bfe05a2ea419c54c037a8133ba38c87080275f178563103b7486c3249`.
Fresh checks object:
`21534ce3ec5eee0cbc875b55271965a2579eb86a589a00ce6e482977afba533f`.
The full commands, logs, source snapshots and drivers are in
`reviews/foundation-ha-order-multiplicative-author-replay/`.
Dependency manifest SHA256:
`ebc48cb6455dcd0f094ed437b32d9836c9117328de01a6fc17e3aea4189e9579`.
Snapshot: `9294c63bd0562a7e7bfc76c4e87e957d5265e839`.

The exact endpoint is
`FoundationHAOrderMultiplicative.mulLtMul : HA.Proves
(sentence PeanoMinus.Axiom.mulLtMulᴺ)`.
It targets the actual source axiom
`forall x y z, x<y and 0<z -> x*z<y*z`, with closure count three and
matrix indices two, one, zero. Literal checks bind that sentence and its
entire conjunction premise. A negative control ensures the positive
multiplier premise has not been deleted.

For ordinary order, open predecessors `d,e` with `s+S d=t` and `0+S e=u`.
HA zero-addition yields `S e=u`. After both binders, `d` is slot one, `e`
is slot zero, and every ambient term and retained assumption is shifted
twice. Choose predecessor `d*u+e`. Actual HA `succ_mul`, `add_succ`,
`add_mul` and equality congruence prove
`(S d)*u=d*u+u=d*u+S e=S(d*u+e)`, then
`s*u+S(d*u+e)=s*u+(S d)*u=(s+S d)*u=t*u`.
This constructs the order witness without a new induction or a semantic
algebra oracle. General ordinary and negative helpers retain arbitrary
finite HA contexts.

The translated proof pairs the two double-negated premises with the frozen
intuitionistic `pair_doubleNeg`, then applies `map_doubleNeg` to the ordinary
implication. No witness is extracted from a double-negated order premise.
The conclusion remains double-negated; no DNE or extra stability assertion
occurs. The checked Foundation implication equivalence and actual universal
closure supply the literal source sentence, with no copied GG recursion.

Checks retain sparse nonlinear parameters zero/four/seven and an extra open
equality assumption, exercise the unit multiplier, instantiate the complete
product witness with both fresh slots, and distinguish swapping those slots.
All exact source/target and helper axioms are reported.

The private overlay reuses 96 authenticated prerequisites, including the
same 76 Foundation modules: the prior 95 Witnesses prerequisites plus its
frozen main. Source/object/trace pins, inherited path inventory, parent
manifest, compiler and package identities were rechecked before and after
builds and at freeze. There were no prerequisite builds or new Foundation
imports. Only these two leaves were freshly compiled; no full closure
refresh is claimed.

The remaining arithmetic-image cases are `ltIrrefl` and `ltTri`. This
packet does not claim those cases, full arithmetic proof transfer, or the
final HA equation/consistency equivalence.
