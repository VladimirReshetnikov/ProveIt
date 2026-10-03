# Independent review of the exponential three-mass input bridge

**PASS. No correction requested.** The frozen [author source](three_mass_exponential_input_bridge.py), [receipt](three_mass_exponential_input_bridge.json), and [proof note](three_mass_exponential_input_bridge.md) correctly compose the positive exponent component with the four complete unbounded clock histories. This review covers both finalizers, every emitted gate, the ordinary-input substitution, and the separately supplied reversible prefix. It does not establish a new universal source-machine input convention.

Authenticated author SHA-256 values:

- Python: `fe892d2920a866c723ad648ea52ac467d0f531c6aabe13c000f3cd53fef57ef2`.
- JSON: `976e75fc90da362949774ee5cfae2e1b48f35bf351203825b82b3dfba7353296`.
- Markdown: `0d839b4661cad99e37c19a590e9e14840d1d2961383a111c107f2957ccd87187`.

The [independent checker](review_three_mass_exponential_input_bridge.py) and [receipt](review_three_mass_exponential_input_bridge.json) additionally pin all six immediate parent source/receipt/note files. The checker reads the two authenticated parent JSON packets and executes no historical dependency module. It loads the candidate API directly from authenticated source bytes solely for independent caller-guard and copy tests. Its arithmetic interpreter, source reconstruction, sparse polynomial expansion, expression-DAG comparisons, ledgers, and prefix/table simulations are separate implementations.

## Full source identity and finalizers

The exponent certificate is precisely the parent's first51 gates. Its computed values include `r=48x` and `Q=r+delta`. On every supplied positive integer tuple, x>=1 and delta>=1 give Q>=49, so the substituted old raw input Q−1 is natural before using any native equation. Its internal y is renamed `exp__y`, distinct from the external final payload y.

In every actual history, the only raw-input path is the pair `K*z`, then addition of q0. The first product has no other source or comparison consumer. The replacement pair is `K*Q`, then addition of q0−K. Expanding the two actual affine forms proves

    K*(Q−1)+q0 = K*Q+(q0−K).

The private product differs by K; the full initial configuration agrees. The checker uses only that established affine equality as a cut and verifies every other history register, all20 comparison pairs, and the entire history SOS expression DAG. It also reconstructs the literal finalizer from those20 pairs rather than trusting its name or metadata. The source and polynomial identity hold on all integer and rational tuples; the polynomial identity itself is valid over any commutative ring.

Write U for the unchanged exponent factor product and S for the entire substituted history SOS. Both public finalizers have three literal gates:

    F_SOS=(U−1)^2+S,
    F_anchor=U*(1+S)−1.

On integer supplied tuples, S is a nonnegative integer. The first output vanishes exactly when U=1 and S=0. For the second, U(1+S)=1 forces the positive integer1+S to equal1, hence also U=1. Thus neither admits the exponent component's genuine U=−1 branch. This argument retains all20 native/history equations; it does not merge their factors into an unchecked unit product.

The independently expanded finalizer polynomials satisfy the exact off-zero identity

    F_anchor−F_SOS=(U−1)*(S−U+2).

They are not the same polynomial. The anchor zero-equivalence uses integrality: U=1/2,S=1 makes the anchor zero while the SOS is5/4. This is a scalar boundary example, not a claimed full supplied-coordinate counterexample. All claimed semantic coordinates remain integers.

## Complete paid counts and degrees

The checker reconstructs all eight literal sources and checks topological order, exact operand types, every supplied coordinate, and liveness of every certificate and polynomial gate. Both finalizers have the following complete ledgers:

|Source|Certificate M+A|Full M+A|Total|Positive private witnesses|SOS upper degree|Anchor upper degree|
|---|---:|---:|---:|---:|---:|---:|
|INC2;DEC2|247+342|268+383|651|71|2344|2398|
|Prime-three zero test|192+272|213+313|526|69|1192|1246|
|No-op|190+272|211+313|524|69|1192|1246|
|Prime-three positive test|197+268|218+309|527|69|1192|1246|

These counts include the entire input, target, clock, height, native certificate and finalizer. The increment over each corresponding frozen raw history is exactly54=32M+22A and12 positive witnesses. There are21 conceptual comparisons and three supplied coordinates x,y,T. If y,T become existential positive coordinates of a halting predicate, the witness counts rise by two; gates do not change. Each of these four sources has a nonempty accepting run whenever it accepts, and the inherited positive final-payload condition remains present.

An independent sparse expansion of all six exponent factors gives exact degrees5,7,14,22,3,3, with11,80,111,1646,5,10 terms respectively. Nonzero polynomial factors over the rational polynomial ring have additive product degree, yielding degree54 for U. Q is affine in x and delta, so substituting it for the parent's raw input cannot increase the parent history degree. Consequently the valid upper bounds are `max(108,degree(S))` for SOS and `54+degree(S)` for the anchor. Literal propagation gives2399/1247 for the anchor before using the exponent cancellation; this is correctly distinguished from the refined2398/1246. The author claims no exact degree for any complete composed polynomial, and this review does not promote the upper bounds to equalities.

## Semantic input, clock and prefix boundaries

The inherited positive exponent extension theorem gives U=1 exactly on its output projection Q=2^(96x), with a positive extension for every x>0. Combining that theorem with the unchanged raw history theorem proves the stated existential relation: the selected fixed machine begins at valuations `(96x,0)` and first halts with the specified final payload y and native physical clock T. Separate exponent/history witnesses can be chosen because their only shared interface is Q. This is neither a uniqueness assertion nor a bijection with arbitrary raw-input histories.

The exact source tables independently confirm y=Q and T=600Q+16 for increment/decrement, y=Q and T=192Q+8 for the zero-test and no-op, and rejection for the positive prime-three test because the initial second counter is zero. Forty-eight table checks cover six positive inputs in each of the eight emitted forms; these are24 distinct source/input cases. They supplement the inherited arbitrary-duration proof. They neither impose a horizon nor materialize the large positive Pell witnesses.

The 201-state,202-instruction divide96 prefix is a separate source-level construction. It is absent from all eight circuit ledgers. The checker independently verifies its literal separated syntax in both directions, no incoming entry/no outgoing exit, eight complete forward/inverse runs, and their physical clock sums. The proof is the invariant `C0+96*C1+i=96x` at Li and `C0+C1=x` in the transfer loop. There are194x division-loop instructions,4x transfer instructions, and four entry/exit instructions, totaling198x+4. Attachment to a fresh no-incoming source initial state preserves the stated separated syntax.

The prefix therefore converts a *supplied source already proved for `(x,0)`* into one accepting its corresponding `(96x,0)` inputs. It does not prove that an effective universal-source encoder can be replaced by unary input. The author's explicit Morita–Imai qualification is preserved; this review does not perform a new literature or universal-source audit. The four emitted machines are explicitly nonuniversal. Their T counts physical evolution after initialization, and excludes external preparation and the uncompiled prefix. Inserting the prefix would require a new table and a newly charged complete clock circuit.

## Replay and evidence boundary

The saved independent receipt records eight full source and output-DAG identities;160 residual-DAG identities;160 independent full-output cases, including80 signed integers and16 rational tuples;3200 residual-value comparisons;160 literal SOS checks; four symbolic finalizer corrections;1275 integer scalar finalizer cases;64 positive pretyping bounds;228 malformed caller rejections;32 defensive-copy checks; six warm dependency-pin rejections; an optimized-mode rejection; and the separate source-table/prefix evidence above.

The review reads the full new source and proof note and the relevant authenticated parent proof notes. It reuses the already reviewed native/exponent existence theorems. It does not rerun unchanged historical author suites or claim the finite fixtures establish those theorems. No repository, archive, parent source or author receipt was modified.

Replay with the Python3 standard library:

```sh
python3 review_three_mass_exponential_input_bridge.py \
  --artifacts /path/to/native-stream-queue \
  --root /path/to/native-stream-queue \
  --expect review_three_mass_exponential_input_bridge.json
```

`--artifacts` locates the frozen author trio, while `--root` locates its six parent files. The writer passed, and a separate fresh replay from cwd `/`, using the installed author trio, matched the saved receipt exactly. The result has no absolute workspace-path dependency.
