# Actual positive-zero equivalence: independent Lean review

PASS. Reviewer: `complemented47_review`; author: root. I found no missing
premise, scalar mismatch, extra mask-port shift, or witness substitution in
the final composition. Both fresh private builds passed with byte-identical
objects and six standard-only axiom reports. No source correction is requested.

I read all123 main lines and all49 check lines before replay. I also read the
complete current ScalarFacts and native-packing Facts modules, polynomial
window, marked window, literal tile soundness, final arithmetic soundness,
fixed-port13-variable arithmetic equivalences,13-variable completeness and
local zero-set formulas, and the exact13-variable restoration source.
The positive-source construction and its full canonical/source contracts
were independently reviewed in the immediately preceding receipt
`native-positive-source-construction-lean-peer.md`.

I authored the halt-packing and controller-dimension wrappers, portions of
the controller/carry/word/geometry chain, and several supporting reviews.
I did not author this final endpoint, its scalar witness construction,
rank calibration, positive Pell/source completion, arithmetic13-variable
maps, or soundness composition. This is an independent review of the new
composition and its interfaces, not independence from every prerequisite.

| Frozen source | SHA-256 |
|---|---|
| `CurrentPositiveZero2011.lean` | `cdbd33de5ccb176c253d1cfca41f1d34b8d0121790a4b06c5d38d461b72b648c` |
| `CurrentPositiveZero2011Checks.lean` | `79a6dc417560cec163767f9d5af69c4ef647fb081b433ab0abd830dbf41ee44b` |
| `CurrentHaltPacking2011.lean` | `6ed64c4b270ba07ababf8412dfad7ea8d69d7fbcd005f7f403f65fd34b4ead4f` |
| `NativePositiveSourceConstruction.lean` | `f96ba070ef8dac85ea4d63cf687efbee7b9f75f65e35ef498c9c028551bacf5d` |
| `CurrentSoundness2011.lean` | `1118ee3f50dffa046e1205b72a8cac84ef02b5cad0862ef53b79cde1de4ba7ef` |
| `CurrentCarrierArithmetic2011.lean` | `5f749fdfe0a3857c6d84b0505574f1b1d09f5b859167659a34b04ba392f4a5b3` |
| `CurrentPolynomialWindow2011.lean` | `db64a1e9130d09d606f3262781be9a4c0d70db1a9cdb7482cd74ecc0ddf0b730` |
| `CurrentWordScalarWitness2011.lean` | `8a644c7eb65bff5016d28a992e2db477bb5341b33fa31e92f1a086a0d0e4879e` |
| `DecimalMachineZFC.lean` | `778af71680ec6aadd9858d30ace87c25012ac6b9dac02e2a483094401fc06107` |
| `Bridge.lean` | `c57457f028f0fca0279a95deb3950665bb663473adeaae32b32c5fa772b24114` |

Source paths are under `Lean/DiophantineConsistency/`, relative to
`Computability/DiophantineConsistency/`.

The exact predicate is `DiophantineConsistency.ConZFC`, defined as
`¬ BProv ZFCax_s [] Form.fBot`. Its negation reaches the literal decimal
machine through `DecimalMachineZFC.blank_nonhalting_iff_conZFC`, and the
halt-packing wrapper constructs its actual geometric word and controller
data. There is no placeholder consistency predicate and no assumed
tableau/machine equivalence at this endpoint.

`packingData` uses the supplied particular native Facts, rank binding and
forced multiplier. It sets J to the same window repunit, F to the same
normalized digits, C to the same rephased source, alpha=q-C-F, z to the
actual quotient witness, and w to the actual multiplier. All six positivity
facts come from that Facts object. Repunit balance supplies beta*J+1=q;
the ordinary balance supplies C+F+alpha=q. The strict rank growth from the
same packing justifies u<=R, so w=2^(R-u) really implies w*2^u=2^R without
silently truncated exponents.

The transport field uses `hf.scalars.transport_unit`, whose conclusion is
exactly `(K+w)*C+(q-F)-z*(q-1)=1`. The equality is over the integers and
retains the old-z convention. In the scalar construction, z is the successor
of the actual quotient, derived from the ordinary normalized representative;
it is not an assumed transport solution. The rank field is the same signed
`windowRank(q,C,F,lowPort,highPort+beta,J)`. The fourth source port is shifted
by beta exactly once, consistently with the final polynomial's literal ports.

The converse proof destructures one `ExistsPacking` witness and passes its
unchanged a,S,carries,digits,R and forced stride into `packingData`. Its
population and R%4=3 are precisely those of that same rank. Positive u and
beta follow from the actual width, positive power dimension and fixed mask
constant. The positive-source population theorem then constructs both Pell
seeds and a strictly positive14-coordinate zero. Its polynomial is
definitionally the actual `CurrentPolynomialWindow2011.polynomial`, because
`CurrentWindowCarry2011.ports` is the same `CurrentMasks2011.ports K`.
No source zero, mask success, matching word, desired norm, or calibrated
rank remains as an extra hypothesis of `not_conZFC_positive_zero`.

The reverse implication invokes the accepted literal soundness endpoint:
the actual polynomial supplies its original arithmetic window and selected
marked word; actual tile semantics force a halt of the actual decimal
machine, contradicting the same ConZFC predicate. Its marked-word theorem
requires neither unique Start nor a coprime stride. The final logical
equivalences retain the classical logic used by this external Lean proof.

The13-variable conclusions use the same complete fixed ports and literal
kernel. Its positivity is derived from `CurrentKernel2011.K_pos`. The
fixed-port arithmetic interface discharges the mask/port hypotheses of the
fresh13-coordinate completion. Adjacent69/70/71 zero-set equivalences preserve
the entire positive assignment, with delta nonzero derived from positivity.
For `not_conZFC_simultaneous_thirteen_zero`, one call to `completes` returns
one u with all three polynomial evaluations zero; it does not combine three
unrelated existential witnesses. The restoration maps needed for the
reverse implications likewise return actual positive Carrier65 zeros.

The proved domain is strictly positive integer independent coordinates,
as specified by `PositiveZero`. The endpoint now establishes the external
Lean no-positive-zero/ConZFC equivalence for the fixed14 polynomial and
each of the three fixed13 polynomials. It does not assert ConZFC, claim an
object-language ZFC derivation, extend the domain to arbitrary integers,
or certify a globally minimal equation. Those are different statements.

I freshly compiled main then checks with `lean -M6000 -j1`; both set
`Elab.async false`. Outputs were isolated under
`/tmp/current-positive-zero2011-complement-peer-jhu14chi/lib`, with both
reviewed object bundles excluded from prerequisite symlinks. LEAN_PATH was
prepended after `lake env`, so the checks imported the fresh main.

The replay reused the authenticated current private Ratio90/Half/Outer
objects, with hashes respectively
`d54f59bc03a0648e360c124e18b7b0585cc98147553312b294a43c0fec67680b`,
`7ef4f6dc18292dc30cdea2f5a8e55228ee38c1d7f5a27319eba8db63a73efbfa`,
and `f15619430cc65f2744cef7ff49cb9cc512a4eaf6cec457b2d8eeba99b241f32d`.
It used my independently replayed PositiveSource object
`33ccb138518d64b8798e85eb7edaf900d8de420f14e4985f80db1ec7792eba07`.
The remaining accepted objects were reused unchanged. Root's separate
current Ratio90/Half/Outer audit/replay is not represented as my own here.
This is a fresh endpoint replay, not a rebuild of the entire closure.

Both first attempts exited zero with no diagnostics. Main3.63seconds,
peak RSS3,359,892KiB; checks2.67seconds, peak RSS3,342,440KiB. The main log
is empty. All six reports use only `propext`, `Classical.choice` and
`Quot.sound`. No new axiom, `sorry`, or `native_decide` occurs in the new
packet. Both generated objects are byte-identical to root's shared objects;
all41 pinned source/object inputs remained unchanged.

| Replay artifact | SHA-256 |
|---|---|
| Main object | `629d9b6e21a33c0ddaa9d61e067a3c47e0435cb146fb30f6bab259b4026b68c0` |
| Checks object | `c74a78cec6457027befbf2219859e18df01117875ba4dff0c11a8b5ed34524b3` |
| Main log | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| Checks log | `43722bf5203ae1996c3c1cb2099b4a770a190a56364d61114b9a4cc951a3fbcc` |
| Before and after manifests | `747d9d4b1f56d275738acd598982fa77c3e86ae249669986db3e3253e2f01d41` |
| `REPLAY.json` | `22042ff7f04b499454dd958ffa382ef464e120abe969d623a3af91aa0ac35017` |

Only this new peer receipt and temporary replay artifacts were written.
No accepted source, shared object, central document or Git state was modified.
