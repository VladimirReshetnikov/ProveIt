# Independent review of the fixed-arity native Grill wrapper

**PASS; no source or proof correction requested.** The frozen wrapper represents the stated ordinary-positive-input, existentially padded halting relation for each fixed finite Grill program. The full `(0,1,1)` circuit costs **219=98M+121A**, with31 positive witnesses and11 retained comparisons; the raw alternative costs243=104M+139A, with37 witnesses and20 comparisons. The duration is packed into the fixed scalar interface. Universality of the permitted ordinary-input language remains explicitly unproved.

Reviewed source: `grill_tag_native_word_closure.py`, SHA256 `80abbb7a293ba1051fc1d2559c7f8aac5a2f28947535573be49c8c49f5f3e7b7`. Reviewed author receipt: `d6f5488360e120f9db6588933380c814bf17340c6e2e7c6daa073768241253f3`. Reviewed companion proof: `2b506033b06cec4c82953e31679ad410c1bb114f772b9d2828e4de1ec0edf335`.

## Mathematical audit

**Sentinel boundary.** Starting both affine coordinates at1 is necessary and correctly emitted. Applying the selected tiles in reverse original head order yields `U=2^t+Σd_i2^i`. Because every Grill appendant is a palindrome, the lower affine coordinate is `V=scale(G)+value_LSB(G)`, equivalently the most-significant-bit sentinel code of `reverse(G)`. With dyadic `P0=2^ell` and `0<x<P0`, the computed boundary `U=P0*V+x` is equality of two binary sentinel codes. Uniqueness of the leading sentinel recovers both the length equality and `h=wG(h)`. It is not only a numerical checksum.

**Height before typing.** The final source uses `D=Ufinal+phase_initial+rho`. On every supplied positive tuple, `P0=3x+Z0>=4` and `Ufinal=P0*Vfinal+x` strictly exceeds `P0,Vfinal,1`. Thus `D>=7`, and each required endpoint, initial sentinel and `phase_initial` lies below D. This does not depend on an intended history or any native equation. Omitting the former separate `1,Vfinal,P0` addends therefore preserves all hypotheses. For completeness, dyadic `D>Ufinal+phase_initial` also bounds every monotone affine state. The global-slack estimate uses the two histories' separate digit bounds, not a sum-of-endpoints bound.

**Lane separation and dyadic input.** Positivity gives `J>=0,P>=1` and nonnegative native word arguments before classification. The global equality gives `P>1`, hence `J>0,B<=P`, and bounds every history and decoded selected product below P. The existing physical/controller/range bounds survive. The old radix region still has two lanes, permitting `B=P` at duration1. The new input region starts immediately after those two lanes. Since `P0<D<B<=P`, it fits in one disjoint lane. All three joined arguments are below `Scale=P^(g+s+5)`. The retained prescribed-AND theorem then forces Scale and P dyadic, separates the regions, and gives both the old radix identity and `P0 AND(P0-1)=0`. The latter forces the needed dyadic P0; it has not been assumed through an unpaid predicate.

**Actual reverse phase flow.** After the existing controller/range typing, every base-B digit of Q and Next is a phase code in1,...,m, strictly below B. The supplied `phase_initial<D<B`; the fixed terminal code m is also below B. Therefore `B*Next+phase_initial=Q+P*m` is equality of canonical base-B expansions: its low digit fixes the initial phase, each interior digit enforces one reverse phase transition, and its high digit forces the last source phase to0. Thus the reversed selected phases are exactly `(t-1-j) mod m`. Merely satisfying aggregate phase counts is insufficient and is correctly rejected by this equation.

**Closure and positive completeness.** The recovered word equality implies actual queue halting by the supplied closure length, using the induction that stops at the first empty queue. It need not be a first-halt trace of that entire length. Conversely an actual halt supplies a closure, its reversed affine history and a positive phase initial value. The inherited global bound remains strictly positive with this chosen D; its selected slope classes are disjoint. All old AND lanes and the new input lane then have the required semantic values. The imported positive prescribed-AND converse supplies fresh native witnesses at the actual new Scale.

**Native unit option.** The altered wrapper satisfies the unit parent's pretyping assumptions: its native scale is at least16 after padding, its computed F3 is at least8, and all six projected native definitions are strictly positive. The retained strong equation, positive ratio slacks and all four wrapper equations remain present. The three modulo-four norm exclusions and single checksum argument therefore apply unchanged. The root-gap restoration and strong-residual correction are needed; no equality of raw and unit off-zero polynomials is claimed. Only their positive-zero bijection is used.

## Necessary-guard counterexample

The independent checker includes a stronger width-typing counterexample than the illustrative author example. Take the one-phase program `(1)`, whose one head appends `010`. Every real nonempty queue with a1 keeps the same positive number of1s, so this program never halts on positive ordinary input.

Nevertheless the proposed forward heads `000100` give reverse sentinels `U=72,V=10`. The positive numerical assignment `x=2,Z0=1,P0=7` satisfies both `P0=3x+Z0` and `U=P0*V+x`. All phase transitions are correct. Packing that affine path gives positive history/slack coordinates and satisfies every old physical, controller, range and radix AND region. If the new input lane were omitted, those interfaces would admit this invalid boundary. With the actual emitted lane, the AND discrepancy is exactly `6*P^N0`, because `7 AND6=6`. Thus the new source excludes it. This is a semantic interface fixture plus the imported native extension theorem, not a materialized full Pell tuple or a zero of the delivered polynomial.

## Independent executable evidence

The accompanying reviewer pins the exact new source before compiling its bytes. It independently checks all eight complete source closures, coordinate use, liveness and operation ledgers. Direct degree propagation verifies the declared **upper bounds**, including484 raw and1187 unit for `(0,1,1)`; exact-degree metadata remains unset. Witness counts follow `s+g+29` raw and `s+g+23` unit, independently of duration.

For every emitted form, exact symbolic expansion checks all four new wrapper residuals against independently constructed equations: **32 symbolic residual identities** across eight forms. It also checks the computed boundary, height, radix, repunit and phase interfaces symbolically. The reviewer separately reconstructs all joined ports and evaluates **96 complete raw cases,1,920 residuals**, then checks the raw sum of squares. For the native64 residual portion alone it uses the original authenticated source as a disclosed oracle. It does not rely on the author's wrapper manual evaluator.

For another96 cases it independently reconstructs the six projected fields and the possibly half-integral off-zero old root, evaluates the entire raw source, checks all four unit factor corrections and all retained residuals, and reconstructs the complete unit finalizer. Positive samples verify restoration positivity; signed and fractional restored values are algebra tests, not native-domain witnesses.

The semantic census visits **112,224 arbitrary tile words** through length6 over four programs. It independently reconstructs both sentinels and checks packed phase flow. It finds21 positive chronological word closures, including one post-halt closure, and verifies actual FIFO halting for each. It also finds3,357 positive scalar word boundaries rejected by the phase equation. These yield42 complete emitted outer/native-port fixtures, across raw and unit forms. No native Pell zeros are numerically materialized. Thirteen malformed public packet/assignment calls reject, and a public packet-copy check passes.

A separate padding fixture goes beyond that length6 census and the author’s length8 outer census. For program `(0,1,1)` and x=2, allowed widths P0=8 and16 enter exact period3 cycles. At P0=32,Z0=26, the initial word `01000` instead halts after9 steps with heads `010000100`. Its reverse endpoints are U=578,V=18, satisfying `578=32*18+2`. The checker constructs both emitted outer/native-port fixtures. This confirms that existential padding is a substantive part of the represented language; it is not interchangeable with choosing the shortest allowed binary padding.

The full source and companion note were read. The guarded AST adapter preserves all original native rows and adapts the actual retained builder; it does not substitute an untyped word oracle. Dependency bytes are pinned and loaded through a source-only importer with restored module state. The author additionally tests malicious timestamp-valid bytecode and preloaded module isolation. This review does not reprove the historical native Pell classification; it checks its application to the new ports and explicitly relies on the pinned, previously reviewed theorem.

## Reproduction

Use Python with **SymPy**, which is required both by this review's symbolic checks and historical native dependencies. In the existing research environment:

```sh
/tmp/diophantine-research-venv/bin/python review_grill_native_word_closure.py \
  --source grill_tag_native_word_closure.py \
  --root /absolute/path/to/native-stream-queue \
  --expect review_grill_native_word_closure.json
```

An equivalent Python environment may replace the displayed interpreter. The helper has no permanent `/tmp` source dependency: explicit paths or colocated sibling files are supported. It writes only with `--output`. A fresh complete saved-receipt replay passed.

The verified result is a fixed-arity representation of this precise padded-input halting language. It supplies no fixed universal Grill program, no padding-insensitive universal recognizer, no new proof of the creator's compiler, and no improvement to the separate87-operation universal-polynomial result.

Root independently read the complete proof and replayed both suites in the research environment. Both fresh receipts matched their committed counterparts byte for byte.
