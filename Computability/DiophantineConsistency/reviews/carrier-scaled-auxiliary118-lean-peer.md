# Scaled auxiliary Carrier118: independent Lean review

PASS. Reviewer: `/root/circuit_reduction`; author: root. I found no
incorrect coefficient, hidden norm premise, coordinate substitution, or
extra mask-port shift. Both fresh isolated builds passed with objects
byte-identical to the author's and six standard-only axiom reports.
No source correction is requested.

I read the complete new main and checks before execution, together with
the complete `ShortEquation`, `Carrier65`, `CurrentPositiveZero2011`,
`CurrentWindowCarry2011`, and the exact `DiophantineConsistency.ConZFC`
definition in `Bridge.lean`. I also reread the complete
ordinary `research/scaled-auxiliary118/PROOF.md`, the root author receipt,
and the independent current-positive-zero endpoint receipt.

I did not author this Lean packet, the earlier ordinary replacement proof,
or its finite graph/auditor. I independently reviewed that ordinary proof
earlier in `scaled-auxiliary118-circuit-peer.md`. I authored several reused
Pell/source and arithmetic-transfer prerequisites, including
`NativeOuterSeedConstruction` and `NativePositiveSourceConstruction`.
This is independent review of the new replacement and composition, not
independence from every prerequisite in the endpoint's proof chain.

## Exact reviewed binding

Paths below are relative to `Lean/DiophantineConsistency/` under
`Computability/DiophantineConsistency/`.

| Source | SHA-256 |
| --- | --- |
| `CarrierScaledAuxiliary118.lean` | `2e222efd3b40626e6734fe30e5b7239fb7a7abd5fd9c14bee8e4a238c237c620` |
| `CarrierScaledAuxiliary118Checks.lean` | `e404326b866f3a04a6b67f2d35e869493cdc6eebbd86da2222e22ad78c05381d` |
| `Carrier65.lean` | `be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154` |
| `ShortEquation.lean` | `2d447a166a33dedb90c8acdf0755d584a9d057bf46a047e0a454bf150f628b68` |
| `CurrentWindowCarry2011.lean` | `94f9ec318d90b66200757bba8992eb6560e283dbdceeac877e48eee80ade3d06` |
| `CurrentPositiveZero2011.lean` | `cdbd33de5ccb176c253d1cfca41f1d34b8d0121790a4b06c5d38d461b72b648c` |
| `Bridge.lean` | `c57457f028f0fca0279a95deb3950665bb663473adeaae32b32c5fa772b24114` |

The new `value` retains `Carrier65.core` unchanged and replaces only the
coefficient of `V²-y²` in U: `S²` becomes `delta*f²-delta`. The final
product still uses the same P,Q,W,Z and subtracts the same delta.
The literal identity `Z=delta*strong` is therefore shared by both values.

`scaled_identity` factors the new value as delta times
`ShortEquation.product` with coefficient `delta*(f²-1)`.
`original_scaled_identity` factors the old value with coefficient
`delta²*(i*c²)²`. Its intermediate U identity uses the actual
`S=i*delta*c²`, so there is no missing scale or exponent.

For either zero, nonzero delta permits cancellation. The remaining
integer product forces the strong factor to be an integer unit.
`strong_ne_neg_one` uses the actual identity
`delta=(a+2)²-1` and a complete modulo-four argument, with no assumption
that other norms already equal one. The two coefficients agree when the
strong factor equals one. `replace_coefficient` proves both directions
by separately obtaining that unit condition from the relevant zero;
the final `.symm` has the correct new-to-old orientation.

Consequently `value_zero_iff_original` holds for every integer assignment
whose actual delta is nonzero. `positive_zero_sets` derives this condition
from beta positivity and positivity of the independent coordinates. It
does not assume canonicality, a source solution, a sign of rank or tau,
or successful native masks. The witness map is the identity on all
fourteen coordinates, including noncanonical positive zeros.

`value_map`, polynomial evaluation, and the pointwise positive-zero-set
theorem bind the complete polynomial. `currentPolynomial` specializes
exactly `CurrentWindowCarry2011.ports`, whose fourth port is
`highPort+beta` once. The current existence iff preserves the same
assignment and derives beta positivity from the actual finite mask.
The final closed theorem uses the accepted external endpoint for
`DiophantineConsistency.ConZFC = ¬ BProv ZFCax_s [] Form.fBot`.
No supplied consistency equivalence or native interpretation is added
as a premise of the new theorem.

## Fresh replay and limits

After the author announced frozen final checks, I ran sequential direct
`lean -M6000 -j1` builds in
`/tmp/scaled-auxiliary118-circuit-peer-49mr2kj_`. Both reviewed objects were
excluded from prerequisite symlinks, so the checks imported my fresh main.
The fully read preparation driver is
`/tmp/scaled-auxiliary118-peer-replay.py`; the replay manifest and exact
commands are in that overlay's `REPLAY.json`, SHA-256
`4fbed8d1140f964dcb204a86c156c315419f7e0f3b5ce1495417763a54d6740a`.

The main passed in 4.019 seconds, checks in 2.641 seconds. The main log is
empty; all six audits are subsets of `propext`, `Classical.choice`,
`Quot.sound`. No `sorry`, new axiom, or `native_decide` is introduced.

| Replay artifact | SHA-256 |
| --- | --- |
| Main object | `1ba5acbb005ae1d0862a7b604af901253b8f3f9189a22924337678c53422331f` |
| Checks object | `72a509b818037f18d400664d9871b40fa5196a4649fba0768e0d4a61cd52d3ff` |
| Main log | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| Checks log | `25f68e5320e70690b39c5976388ca861ca6bc03f7342830f858908159966c677` |

Previously accepted prerequisite objects were reused. The overlay explicitly
selects the authenticated private current `PellRatio90`,
`NativeHalfBinomial`, `NativeOuterSeedConstruction`, and
`NativePositiveSourceConstruction` objects, with hashes respectively
`d54f59bc03a0648e360c124e18b7b0585cc98147553312b294a43c0fec67680b`,
`7ef4f6dc18292dc30cdea2f5a8e55228ee38c1d7f5a27319eba8db63a73efbfa`,
`f15619430cc65f2744cef7ff49cb9cc512a4eaf6cec457b2d8eeba99b241f32d`,
and `33ccb138518d64b8798e85eb7edaf900d8de420f14e4985f80db1ec7792eba07`.
All pinned reused objects remained unchanged. This is a fresh leaf replay,
not a rebuild of the full post-merge source closure; that audit is a
separate ongoing task. No shared source or object was changed.

The ordinary graph's exact 66-operation/degree-118 result remains a separate
finite proof with its frozen sorted2501 binding. This new Lean packet
proves the uniform algebraic transfer at the actual current2011 ports;
it does not relabel that old graph, newly verify its metric, or establish
a degree theorem in Lean. The final consistency equivalence is external
Lean mathematics, not an encoded internal-ZFC derivation or a consistency
decision. No global minimum is claimed.
