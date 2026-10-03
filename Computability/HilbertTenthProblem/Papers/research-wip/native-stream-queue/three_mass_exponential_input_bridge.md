# Paid exponential input for four unbounded three-mass histories

The [source](three_mass_exponential_input_bridge.py) composes the existing positive-input [52-operation exponent component](pell_fixed_affine_exponent52.md) with the four complete clock histories in [the factored native coefficient packet](native_pell_factored_first_coefficient.md). The [receipt](three_mass_exponential_input_bridge.json) contains every gate of both finalizers for all four resulting polynomials. The default SOS finalizer has the smaller degree bound at the same cost. All parent bytes remain unchanged.

For each fixed source machine M, the interface starts M at payload

    N0=Q=8^(32x)=2^(96x),     x>0,

hence at counter valuations `(96x,0)`. The output y and native physical time T retain their natural domains. The history duration is existential and unbounded; there is no externally supplied horizon. This is a complete ordinary-input encoding for the specified machines, **not** a theorem that all recursively enumerable sets have recognizers on this unary two-counter input convention. None of the four emitted machines is universal.

## 1. Positive input and complete finalizer

Write U for the exponent component's product of six integer factors, before its last subtraction. Its authenticated 51-gate certificate computes

    r=48x, Q=r+delta,     delta>0.

Thus Q>=49 and the old raw input `z=Q−1` is natural on every permitted supplied tuple, before any equation or native typing. The proved positive extension theorem is

    U=1 implies Q=2^(96x),
    and every positive x admits positive private coordinates with U=1.

This states an output projection and completeness, not uniqueness of the private witnesses. The distinction between the signs is essential. The same component has genuine positive U=−1 extensions with Q=2^(96x−4); these must not be accepted by an unchecked multiplication of units.

Let S(z,y,T;h) be the **entire** 20-residual sum of squares of one existing unbounded clock packet. Its witnesses h are all positive. For natural z,y,T the inherited theorem identifies its zero set with the exact first-halting trajectory of the specified source, including final payload and physical time. The rejecting totalization prevents outgoing halt continuations. The squared-height no-wrap proof and all native conditions remain present; see [the unbounded interface, Sections 1 and 3](three_mass_unbounded_interface.md#3-exact-clock-without-new-native-selection-lanes).

The preferred new polynomial is

    F_SOS=(U−1)^2+S(Q−1,y,T;h).                     (1)

Both summands are nonnegative, so F_SOS=0 holds exactly when U=1 and S=0. The receipt also emits the same-cost integer-anchor alternative

    F_anchor=U*(1+S(Q−1,y,T;h))−1.                  (2)

On the declared integer domain, S is a nonnegative integer. If F_anchor=0, the positive integer `1+S` divides1, forcing S=0 and U=1. The converse is immediate. Both constructions therefore exclude the exponent's negative-unit branch. The SOS finalizer has the smaller degree bound, so it is the public default. The polynomials differ off their zero set:

    F_anchor−F_SOS=(U−1)*(S−U+2).                   (3)

The checker expands the three actual finalizer gates in independent U,S for all four pairs and checks (3) exactly. No off-zero equality between these two finalizers is claimed.

For any positive x and natural y,T, positive witnesses for either F exist exactly when the specified source, initialized at `(96x,0)`, first halts with payload y at native physical time T. The exponent witnesses and history witnesses are independent except for the computed Q, so their separate extension theorems give completeness. Neither uniqueness nor a pointwise bijection to arbitrary raw-input histories is asserted.

If only the halting language is wanted, quantify y and T as well. Every accepted run here is nonempty, so y,T are automatically positive. This changes the count from three supplied parameters to one supplied parameter and two additional positive witnesses, with no gate change. It does not convert the fixed-source theorem into a numerical universal theorem.

## 2. Actual source substitution and paid counts

Each of the four authenticated raw histories computes its initial configuration through the sole input path

    bridge_input_scaled=K*z,
    bridge_input=bridge_input_scaled+q0.

In the actual fixtures K=5 and q0=1. The product's only consumer is the second row; z has no other source or comparison consumer. Replace these two rows by

    bridge_input_scaled=K*Q,
    bridge_input=bridge_input_scaled+(q0−K).

Both schedules cost one multiplication and one addition. The affine identity

    K*(Q−1)+q0=K*Q+(q0−K)

holds on all integer, rational and real supplied tuples. The private product changes, but the full initial configuration and every downstream register, comparison, and history SOS are identical after substituting z=Q−1. The checker expands the actual two-row affine forms and proves the complete downstream expression DAG identity using one justified affine cut. It separately verifies the complete literal SOS against all 20 comparisons.

Every exponent auxiliary and register receives the prefix `exp__`; every history auxiliary and register receives `mass__`. The exponent's internal y therefore does not alias the external final-payload y. Each full polynomial contains the 51 exponent certificate gates, the entire modified history SOS, and three final gates. The default uses `U−1`, its square, and addition of S; the anchor uses `1+S`, multiplication by U, and subtraction of1. The increase is exactly

    54 operations = 32 multiplications + 22 additions/subtractions,
    12 positive witnesses.

The computed Q needs no extra witness or equality. An explicit Q−1 gate would cost one unnecessary addition. There are 21 conceptual comparisons: U=1 and the 20 unchanged history comparisons. The default is the sum of all21 squared residuals. The alternative is the integer anchor (2).

|Fixed source|Certificate M+A|Full M|Full A|Full total|Positive private witnesses|Degree upper bound|
|---|---:|---:|---:|---:|---:|---:|
|INC2;DEC2|247+342=589|268|383|651|71|2344|
|zero test on counter1 (prime3)|192+272=464|213|313|526|69|1192|
|nop|190+272=462|211|313|524|69|1192|
|positive test on counter1 (prime3)|197+268=465|218|309|527|69|1192|

All emitted gates are live, every numeral multiplication is charged, and every affine input/output, height, clock, native constraint and finalizer is included. There are three supplied coordinates x,y,T; the private-witness column excludes them. For a one-parameter halting predicate with y,T existential, the corresponding positive witness counts are 73/71/71/71.

The exponent product has proved exact degree54. The substituted history SOS has at most its parent's degree, because Q is affine in x and delta. Thus the default SOS degrees are at most `max(108,2344)=2344` and `max(108,1192)=1192`, as shown in the table. The anchor bounds are54+2344=2398 and54+1192=1246. Literal degree propagation, which does not exploit the exponent's main-norm cancellation, gives2399/1247 for the anchor and the same2344/1192 for the default SOS. No exact-degree assertion for these four complete polynomials is made.

## 3. The exact loaded relations and clock boundary

Put Q=2^(96x). The four finite source tables give:

- INC2 followed by DEC2: y=Q and T=600Q+16.
- Prime-three zero test and nop: y=Q and T=192Q+8.
- Prime-three positive test: no accepted input on this slice, because the initial second counter is zero.

The literal table replays check these formulas on five positive inputs per form. These examples illustrate the paid interface; they do not need long trajectories to inherit the compiler's arbitrary-duration theorem.

T measures the native three-mass evolution **after** initialization at Q. It does not measure the work of externally constructing the initial geometry or evaluating the Diophantine loader. If a source-level preprocessing program is inserted, its actual physical ticks belong to T, and a new full history table must be emitted. None of those additional source instructions is silently included in the four costs above. The compact cleaned-time relation is also not claimed here; that would require the separate endpoint/time adapter.

## 4. A reversible normalization prefix, with its exact limited use

The receipt also gives a concrete source-level prefix with 201 states and202 instructions that takes `(96x,0)` to `(x,0)` for x>0. This prefix is not compiled into the four arithmetic packets.

Use fresh labels `entry`, `L0,...,L95`, `D0,...,D95`, `inc_B`, `back_B`, `transfer_entry`, `transfer_loop`, `dec_B`, `inc_A`, `back_A`, `done`. Instructions are:

1. `entry --zero C1--> L0`.
2. For i=0,...,95, `Li --positive C0--> Di`, then `Di --dec C0--> L(i+1)`; the last decrement instead targets `inc_B`.
3. `inc_B --inc C1--> back_B --positive C1--> L0`.
4. `L0 --zero C0--> transfer_entry --zero C0--> transfer_loop`.
5. `transfer_loop --positive C1--> dec_B --dec C1--> inc_A --inc C0--> back_A --positive C0--> transfer_loop`.
6. `transfer_loop --zero C1--> done`.

At each Li in the division loop, `C0+96*C1+i=96x`. A complete block decreases C0 by96 and increases C1 by1. It reaches `(0,x)` at L0, and the transfer loop then preserves C0+C1=x and reaches `(x,0)`. The exact source-step count is198x+4. The receipt records forward and inverse replays for eight inputs and the exact physical tick totals of those forward replays.

This is separated reversible syntax in both directions. Every multiple outgoing group is the zero/positive pair on one counter. The only multiple incoming groups are L0 (zero versus positive C1) and `transfer_loop` (zero versus positive C0). Every other incoming group is a singleton. There is no incoming instruction at `entry` and no outgoing instruction at `done`. Missing cases at Li for i>0 reject malformed nonmultiples; they do not affect the loaded slice.

Consequently the prefix can be attached, using fresh labels and identifying `done` with the initial state, to a supplied separated reversible source whose initial state has no incoming instruction. **If** that source is already proved to recognize its intended language from `(x,0)`, the prefixed source recognizes it from `(96x,0)`. A source program proved only for a different effective encoding does not acquire a unary-input interface by this argument.

This is exactly the remaining boundary in the original report. Its cited [Morita–Imai simulation result, Proposition3.4 and Lemma3.5](https://www.numdam.org/item/ITA_2001__35_3_239_0.pdf), supports a reversible two-counter simulation and a no-incoming initial-state convention; it does not state the required unary `(x,0)` input theorem. The source archive's universality discussion supplies an effective encoder and does not expand a numerical universal table. We neither infer a stronger theorem nor claim an impossibility theorem for other interfaces. The present bridge removes the raw coprime-cofactor alias on this prescribed slice; the actual universal table and its fully justified ordinary-input recipe remain separate obligations.

## 5. Reproduction and finite evidence

Run with Python's standard library; no historical Python module is imported:

    python three_mass_exponential_input_bridge.py \
      --root /path/to/native-stream-queue \
      --expect three_mass_exponential_input_bridge.json

The tool authenticates six parent source/receipt/note files before reading the two complete JSON descriptors. Public `build(variant,finalizer="sos",root=...)` supports exactly `incdec`, `zero3`, `nop`, and `positive3`, with finalizer `sos` or `anchor`. Both selectors require exact strings. `checked(packet,root=...)` requires recursive exact-type equality with the freshly rebuilt canonical packet. `evaluate(packet,values,signed=False,root=...)` requires exactly the supplied coordinate keys and strict integers, enforcing positive x/private witnesses and natural y,T. Its signed option is only an algebraic evaluator, not an extension of the semantic theorem. Calls return fresh data and share no mutable cache. Root is the sibling artifact directory by default. `--output` writes a receipt, while `--expect` compares the entire saved object with exact scalar types. Optimized `-O` execution is explicitly rejected.

The receipt records eight complete structural identities and160 preserved history residuals; four exact symbolic finalizer corrections;192 whole-polynomial numerical identities, including96 signed and32 rational cases;192 complete history SOS reconstructions;697 integer finalizer cases;20 distinct loaded outer table cases, checked for both finalizers; eight reversible-prefix forward/inverse cases;96 public boundary rejections; and eight defensive-copy checks. The whole-polynomial proof is the exact affine cut and retained DAG, not the numerical sample. The prefix theorem is the invariant proof, not the eight replays. Huge positive native/Pell tuples are not materialized; their existence is inherited from the two authenticated component theorems. Original author suites are not rerun.
