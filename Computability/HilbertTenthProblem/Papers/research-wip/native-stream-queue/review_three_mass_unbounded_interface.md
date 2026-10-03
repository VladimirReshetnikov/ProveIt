# Independent review: unbounded three-mass raw reachability and clock

**PASS within the stated fixed-source, natural-input scope.** I found no mathematical, count or emitted-source defect in the frozen prototype. This is a paid unbounded trajectory-and-clock construction for each fixed source, not an ordinary-input universal machine or a new universal operation bound. The distinction is substantive: its raw halting language has the valuation invariance described below.

The reviewed author files are `three_mass_unbounded_interface.py/.json/.md`, pinned in the [independent checker](review_three_mass_unbounded_interface.py) and [receipt](review_three_mass_unbounded_interface.json). The source pin is `cf9aee77ab78d68a165cbc31e19ded6d1de69663b34e0078f0106777b472340a`, receipt `fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e`, and note `d336c8c12d3328eb4b6857ee382f91b2c9363f50effba5a7b1bf75308f25df45`. I read all209 source lines and the full proof note, then checked the inherited residue-history proof and literal source. No author verifier is called by this review; its recorded checks are not counted as independent evidence.

## Exact clock: why the congruence cannot wrap

The source encodes a positive payload N and finite control q by `n=K(N−1)+q`, with `1<=q<=K` and `m=6K`. With `n=mz+r`, `1<=r<=m`, the residue determines the control and the payload modulo6. Increasing z by one increases N by6. The stated state-map slopes and tick coefficients follow directly from the literal increments, decrements, tests and nops. Their ratios are finite; the clock coefficient depends only on the already used state slope. Thus the selected quotient fields of the inherited residue-history compiler suffice for the complete affine clock word. There is no uncharged new selector lane.

The rejecting totalization is essential. Missing guards and artificial states go to a fixed trap; the original halt code also goes to that trap, which never returns to halt. An accepted positive orbit ending at the original halt code therefore cannot have halted earlier or taken an artificial rejecting transition. It is the original deterministic source's first-halting path.

The changed height and radix are

    h=n_initial+n_target+T+eta,    B=C h²,

with eta positive, T natural and C dyadic, at least the old multiplier and `2384m+2`. Before digit typing, the inherited global bound still gives `J>=1`, all words and lane coefficients below P, positive native ports and the required native scale. Since h is a positive integer, `C h² >= C h`; every old pretyping inequality remains valid. After the complete native theorem forces B and P dyadic, h must itself be dyadic: an odd prime factor of h would divide B. The original range mask `(h−1)J` therefore still gives genuine quotient digits `0<=z<h`. The old transport row proves chronological source transitions without assuming the new clock row.

Each current encoded state lies in `[1,mh]`. No two current states of an accepted first-halting orbit can coincide. If they did, determinism would make the remaining orbit periodic; it could not later reach a halt for the first time. Hence its number t of transitions is at most mh. The corresponding payload is at most6h. Every genuine branch obeys

    0<tau<=396N+8<=2384h,
    sum(tau)<=2384m h²<B−1.

The final strict inequality has slack at least `2h²−1`, by the actual bound on C. Independently `0<=T<h<B−1`. The retained paid equality

    Ctau=(B−1)(clock_quotient_hat−1)+T

and base-B digit expansion give `sum(tau) ≡ T mod(B−1)`. Both numbers lie in `[0,B−2]`, so they are equal. This proves exactness; the clock has not been replaced by a wrapped checksum. The proof would not automatically apply to arbitrary orbit endpoints permitting post-target loops. Its first-halt totalization is what supplies the duration bound.

Completeness also survives. For any genuine finite first-halting run choose a dyadic h larger than the endpoint sum plus its actual clock and every residue quotient. Then eta is positive, B is dyadic, and the old disjoint-class estimate still gives positive global slack, since the new B is larger than the old required multiple of h. The packed tick word minus the ordinary tick sum is a nonnegative multiple of B−1, giving a positive shifted clock quotient. The inherited positive native theorem supplies fresh native witnesses at this scale. No old Pell tuple is reused, and no gigantic native positive tuple is claimed to have been numerically materialized.

The restriction `initial != halt` is explicit. Zero-step first halts need the separate affine endpoint/time relation and are not handled by pretending that the nonempty orbit packet already includes them. Supplying a positive final payload F and retaining `F=y` correctly handles the original natural output y: y=0 has no zero in this interface.

## Complete source and paid counts

The independent checker regenerates each raw parent using authenticated source bytes, then compares every inherited register under two explicitly justified cuts for h and B. The only old interface changes are those just proved. It checks all18 original comparisons, including all16 native comparisons, rather than assuming that an unchanged count means an unchanged theorem.

It independently expands the new clock word as an affine form in the existing quotient, selected-quotient and selector hats. Every coefficient, constant and unhat subtraction agrees with the source transition clocks. It reconstructs the entire20-row sum-of-squares output from the actual comparison operands, counts every literal arithmetic gate and traces the final output's dependencies. All gates are live and every operand is closed over the declared natural parameters, positive auxiliaries and integer literals.

| Fixed example | M | A | Complete operations | Positive auxiliaries | Comparisons | Degree upper bound |
|---|---:|---:|---:|---:|---:|---:|
| INC2;DEC2 | 237 | 361 | 598 | 59 | 20 | 2344 |
| Prime-three zero test | 182 | 291 | 473 | 57 | 20 | 1192 |
| Nop | 180 | 291 | 471 | 57 | 20 | 1192 |
| Prime-three positive test | 187 | 287 | 474 | 57 | 20 | 1192 |

These totals include the raw input `N0=x+1` through its fused encoded port `K*x+q0`, the positive final-payload port, the added requested-time height input, height square, selected tick coefficients, shifted clock quotient, endpoint equality and complete SOS. The formal degrees are independently propagated **upper bounds**, not exact-degree certificates. No fixed-horizon benchmark is treated as equivalent to this unbounded-runtime contract.

The clean-clock paragraph also charges its stated incremental interface correctly: with x,F,Tnative already available, `192*(F+x+1)+2*Tnative+16` costs2M+4A. Adding a new SOS equality costs1M+2A including its accumulation into the existing finalizer. The prototype does not emit a complete clean-clock source, and the note does not claim a complete clean-clock total.

## Ordinary input and representation limits

The valuation obstruction is correct. On a fixed source path, multiplying N by any positive c coprime to6 preserves all divisibility guards and control states. Every payload is multiplied by c, and every tick satisfies

    tau(cN)−8 = c*(tau(N)−8).

After existentially hiding output and clock, source halting depends only on `(nu_2(x+1),nu_3(x+1))`. The documented natural inputs x=0 and x=4 must have the same halting truth for every such raw source. Even when restricting the free input to positive integers, x=4 and x=6 give a corresponding indistinguishable pair. Therefore choosing a different fixed source cannot represent every arbitrary c.e. subset of the raw input coordinate.

This is not an obstruction to computation universality on a suitably encoded domain, nor to the full `(x,y,T)` relation retaining numerical information. The author's claim is explicitly about the halting language after hiding y,T. Its comparison to the paid U21 exponential prefix correctly keeps that different counter/program interface separate. Neither an abstract reversible two-counter universality theorem nor an effective source encoder is a free ordinary-input Diophantine loader.

## Independent evidence and execution boundary

The [receipt](review_three_mass_unbounded_interface.json) records:

- four complete ledger/closure/liveness audits,2,016 paid gates and four reconstructed complete SOS outputs;
- 1,597 literal inherited-register identities under the justified height/radix cuts,72 retained comparison pairs and four exact clock-affine identities;
- 4,800 independently evaluated positive residue-state-clock cases, including rejecting controls;
- 64 complete modular source evaluations;
- all72 saved accepted outer histories independently simulated for first halt, output, exact clock, positive congruence quotient and strict no-wrap inequalities;
- 648 coprime-scaled transition/clock cases.

The general arguments are above; those counts describe finite checks only. They do not replace the inherited native theorem, establish a universal source, test a gigantic complete positive Pell zero, or enumerate all finite machines. The original archive and actual `certificate.py` core are authenticated, without rerunning their unchanged author suites.

One execution boundary was confirmed with the author: the prototype supports a **standalone cold-process CLI**. Its internal `verify()` does not clear preloaded sibling modules or restore `sys.modules`, so it is not advertised as a repeatable, import-isolated library API. A second in-process invocation can report a different executed-dependency set. This is recorded as a supported-interface limitation, not a mathematical defect or an unresolved requested repair. The independent checker isolates and restores sibling modules for its own authenticated parent imports.

Reproduce, with the three frozen author artifacts beside the independent checker or selected by `--source-root`:

```sh
/path/to/research-venv/bin/python review_three_mass_unbounded_interface.py \
  --repo /path/to/Proofs --source-root /path/to/author-artifacts \
  --expect review_three_mass_unbounded_interface.json
```

No repository files or Git state were changed. The checker requires the repository's usual verification dependencies, rejects optimized Python mode and compares deterministic JSON with type-sensitive canonical serialization. Independent writer and fresh read-only replay both pass.
