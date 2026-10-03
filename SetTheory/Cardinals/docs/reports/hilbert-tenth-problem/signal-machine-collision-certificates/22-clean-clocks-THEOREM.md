# Fully emitted unbounded compact-clean-clock circuits

## Result and exact scope

For each of the four pinned fixed-source fixtures, the files in `circuits/` now contain a complete integer arithmetic DAG whose only natural parameters are the raw input `x` and requested **first clean-target time** `Tclean`. Every other supplied coordinate is quantified over the strictly positive integers. There is no external source-step horizon. The complete native/spatial circuits cost respectively **604, 479, 477, 480** operations and use **60, 58, 58, 58** positive witnesses. Their exact total polynomial degrees are **2344, 1192, 1192, 1192**, certified below. All inherited residue selectors, native comparisons, chronological transport and positive terminal payload remain present.

The construction is a new elementary composition and literal emission of an inherited unbounded raw-history theorem with an inherited clean-target CA theorem. It is not a new native/Pell theorem, numerical universal source, ordinary-input loader, or optimal circuit bound. The four illustrative machines themselves halt, when they halt, in one or two source steps; their unspecialized complete encodings use the general horizon-free mechanism. The proof, not a simulation of a long fixture run, is what licenses unbounded-history composition for eligible fixed sources.

The word "time" here means first target time. Arbitrary completion rows after the first target could create later target occurrences; these are not represented by this first-hit relation.

## 1. Dependencies and authenticated interfaces

The public raw source, complete emitted DAG receipt and independent review are pinned at ProveIt commit `ad634b2d10ad666260f9fdff04ec94b75169ee4b`:

- [Author theorem and interface](https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.md)
- [Complete raw arithmetic receipt](https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.json)
- [Independent raw-interface review](https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_three_mass_unbounded_interface.md)
- [Inherited paid residue-history theorem](https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/residue_affine_packed_history.md)

The exact SHA-256 of the raw receipt is `fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e`. Author source and note hashes are `cf9aee77ab78d68a165cbc31e19ded6d1de69663b34e0078f0106777b472340a` and `d336c8c12d3328eb4b6857ee382f91b2c9363f50effba5a7b1bf75308f25df45`. These bytes are included as inert provenance. No third-party Python source was imported, executed or installed for the new emission/checks.

The previously proved clean-wrapper theorem is included unchanged as `source/inherited_clean_target_theorem.md`, SHA-256 `3d85f8cde66837d8916fb3273c2c57cc1a91ce37de1f3d6c6fe28a4db9103168`. It depends on the earlier audited three-mass compiler and its canonical-section/escape properties. This work does not regenerate its local CA rule tables or repeat its full lattice suite.

Write the inherited raw SOS as `P_R(x,y,t; z)`, where x,y,t are natural integers and every coordinate of z is positive. Among z are `final_positive=F`, the native auxiliaries, height/global slacks, all 30 residue-selector hats, a quotient-word hat, any selected-quotient hats, and the shifted clock quotient. Its twenty comparison squares comprise two outer equations, all sixteen native comparisons, the physical clock congruence, and `F=y`.

For these nonempty-start fixtures, the inherited theorem states:

`∃ z>0 : P_R(x,y,t;z)=0`

if and only if the source started at raw positive `N0=x+1` first halts with raw positive output y at native physical time t. In particular, every zero has `F=y>0` and `t>0`.

The raw `x+1` loader is paid through `5*x+q0`; its final encoded port is `5*(F−1)+qh`. The entire F−1 subtraction, multiplication and halt-code addition remain in the new circuits. F is an unshifted positive payload, not F−1 or a counter valuation. No output extraction or domain change is hidden.

## 2. Eligible source syntax and clean geometry

The four literal source machines are:

| Fixture | Source transitions | Halt condition |
|---|---|---|
| incdec | s INC2→a; a DEC2→h | every positive raw N0 |
| zero3 | s ZERO3→h | 3 does not divide N0 |
| nop | s NOP→h | every positive raw N0 |
| positive3 | s POSITIVE3→h | 3 divides N0 |

Their entry s has no incoming instruction, their halt h has no outgoing instruction, and s≠h. All incoming/outgoing instruction groups are singletons, hence satisfy the separated reversible syntax. Disabled ZERO/POSITIVE guards mean genuine nonfinal stuck states, not halts.

For a reversible separated source R with these structural entry/halt hypotheses, construct Rclean with forward states F:q, backward states B:q, a sole new halt H, forward copies of each instruction, inverse copies in reverse direction, and the two NOP bridges F:qh→B:qh and B:q0→H. INC and DEC exchange; tests and NOP are self-inverse. Fresh entry and terminal halt guarantee the bridges introduce no conflicting incoming/outgoing group.

If R has a first-halting trace `(q0,N0),…,(qh,F)` of h source steps, the cleaned trace consists of that forward trace, the first bridge, its unique reverse trace, then the final bridge. It reaches H first after `2h+2` source instructions and restores exactly N0, including every factor coprime to 6. If R never halts or gets stuck, no backward state or H is reached. Fresh entry prevents an early return to B:q0; it is a necessary structural condition, not an assumption one may freely add to any source by prepending a NOP.

Under the inherited three-mass CA compiler, the initial configuration has the right-marker channel at absolute coordinate 0 and the clean stage-zero F:q0 controller plus stationary shuttle at −12N0, with vacuum everywhere else. Its exact cleaned target substitutes H for F:q0 at the same positions. Equality is of the entire finite configuration, not merely of a control-state observation or a translated pattern. Total conserved weight is exactly three. A stuck source follows the prescribed escape behavior and cannot create that target. The theorem concerns the weighted finite-alphabet channel model, not an ordinary integer-state NCCA whose state number equals mass.

Spatial blocking by four preserves every time and moves the left pair to blocked coordinate −3N0, offset zero. The alternative four-phase radius-one simulation preserves native coordinates and multiplies first target time by four; the target is phase zero. Neither changes the three-unit mass or adds background.

## 3. Physical clock identity, both directions

For a source step N→N′ the native durations are:

- INC: `108N+96N′+8`
- DEC: `96N+108N′+8`
- ZERO, POSITIVE, NOP: `192N+8` with N′=N

The inverse instruction has exactly the same duration after interchanging N,N′. Thus the reverse computation takes the same native time θ as the forward computation. The bridges contribute `192F+8` and `192N0+8`. The inherited first-target identity is therefore

`Tclean = 2θ + 192(F+x+1) + 16`.                      (1)

This is forward execution of a logically reversed source using different controls; it does not assert microscopic retracing from CA reversibility alone.

For a fixed fixture, replace the raw natural time port t everywhere by one new positive existential port `theta_positive=θ`. This is exact because q0≠qh and every genuine instruction takes positive time. No positivity shift or unhat gate is needed. It would be wrong to make this shortcut for an initially halted source; that case is separately emitted in §6.

Existentially hiding y makes `F=y` redundant, since F is already a positive supplied coordinate. Delete only that comparison and its finalizer slot. Keep the positive F coordinate, its encoded target, and all the other nineteen comparisons. Add the single affine equality (1), and rebuild the whole twenty-row SOS. Equivalently, as an identity of integer polynomials,

`Q_R(x,U;z,θ) = P_R(x,F,θ;z) + [2θ+192(F+x+1)+16−U]^2`, (2)

where the raw final square vanishes identically under y=F. Equation (2) is an all-tuple identity, not an equality assumed only on zeros. For the phase model, the new square instead uses `4[2θ+192(F+x+1)+16]−U`.

**Soundness.** For natural x,U and positive z,θ, a zero of Q forces all twenty integer residuals to vanish. Reinsert y=F to obtain a zero of the inherited complete raw certificate. Its theorem gives the actual first-halting source history, positive terminal payload F and exact forward time θ. The clean-wrapper theorem gives the first exact whole-configuration target, and (1) gives its time U. The requested clean time therefore cannot be a fabricated checksum or a later posthalt target occurrence.

**Completeness.** If the cleaned CA first reaches its exact target, the inherited clean theorem implies an original first halt. Let F be its raw terminal payload and θ its positive forward time. The inherited unbounded raw theorem supplies positive witnesses with y=F,t=θ. These same witnesses and θ satisfy all nineteen retained raw rows; the clean clock identity supplies the twentieth. Hence Q has a positive integer witness. No reverse witness, microscopic CA trace, new selector lane, hidden natural-time coordinate or uncharged exponentiation is used.

## 4. Why the inherited clock cannot wrap after composition

For completeness of the dependency argument, retain exactly the following paid construction. Encode source configuration `(q,N)` as `n=K(N−1)+q`, where K=5 for all four fixtures, and take m=6K=30. A missing guard, halt control, trap or unused label goes to the trap preserving payload; trap never exits. Therefore a nonempty orbit ending at the original halt is a first-halting genuine source orbit, without an earlier halt or rejecting transition.

The retained packet uses positive η and

`h=n_initial+n_target+θ+η`, `B=C h²`, `C=131072`.

Its global bound and complete native theorem first provide positive correctly scaled native ports, dyadic B,P and genuine digit typing. As C is dyadic and h integer, B dyadic implies h dyadic. The original range lane `(h−1)J` thus gives residue quotients `0≤z<h`. All 30 selectors remain supplied and are typed by their original lanes. The two outer comparisons retain the same global bound and chronological transport; the new cleanup equality does not replace them.

Each current encoded source state is in `[1,mh]`, and a deterministic first-halting path cannot repeat a current state: any repetition would put its future into a cycle and prevent a new first halt. If t is its decoded number of source transitions, then `1≤t≤mh`. Its payloads satisfy `N≤6h`. Every branch has

`0<τ≤396N+8≤2384h`,

so

`Στ≤2384m h² < C h²−1 = B−1`.

The last inequality holds for all h≥1 because `C≥2384m+2`. Independently `0≤θ<h<B−1` follows from the positive endpoint/height identity. The retained clock row is

`Cτ=(B−1)(clock_quotient_hat−1)+θ`,

where the paid affine word Cτ uses precisely the existing selected quotient and selector hats. Its typed base-B digit expansion gives `Στ≡θ (mod B−1)`. Both sides lie in `[0,B−2]`, so θ=Στ. Thus positivity and the height still exclude a clock increased by B−1. Hiding θ as a witness changes none of this argument.

Conversely, for a real first halt, choose dyadic h above its encoded endpoint sum plus θ and every quotient; choose η as the positive difference. Then B is dyadic, the inherited global slack remains positive, and the packed clock minus its ordinary sum is a nonnegative multiple of B−1. The shifted clock quotient is positive. The inherited native theorem supplies fresh witnesses at this scale. No old native tuple is reused at a larger scale, and no enormous positive Pell tuple has been numerically constructed here.

The no-repeat proof is licensed by first-halt totalization; it is not automatically valid for arbitrary orbit endpoints with loops after an earlier acceptance. Zero steps are also outside this nonempty packet.

## 5. Complete arithmetic ledgers and exact degrees

Every listed `+`, `−`, `*` gate costs one operation; constant multiplication and squaring count as multiplication. Integer literals are declared in each ledger and read as scalar constants. There is no circuit exponentiation, division, bitwise operator, hidden predicate, or free affine port. The bitwise AND used in finite outer-history testing is a semantic test of the emitted native block, not an uncharged gate in the polynomial.

| Fixture | M | A | Complete total | Positive witnesses | Natural free ports | Comparisons | Exact total degree |
|---|---:|---:|---:|---:|---:|---:|---:|
| INC2;DEC2 | 239 | 365 | 604 | 60 | 2 | 20 | 2344 |
| ZERO3 | 184 | 295 | 479 | 58 | 2 | 20 | 1192 |
| NOP | 182 | 295 | 477 | 58 | 2 | 20 | 1192 |
| POSITIVE3 | 189 | 291 | 480 | 58 | 2 | 20 | 1192 |

Spatial blocking uses these same polynomials. The fully emitted phase4 variants add exactly one multiplication by four: totals **605/480/478/481**, with unchanged A, witness counts, comparison counts and degrees.

The six new affine gates compute `F+x`, `F+x+1`, `192(F+x+1)`, `2θ`, their sum and its sum with16: 2M+4A. Dropping the final raw endpoint equality saves 1M+2A, and the new clock equality adds 1M+2A. Each final SOS is rebuilt with forty residual/square gates plus nineteen accumulation gates: 20M+39A. Thus the net ledger happens to be raw+2M+4A, but the asserted totals are independently counted from the complete emitted source, not inferred solely from an incremental schedule. Renaming natural raw time as a positive existential introduces one witness and zero gates. Deleting y introduces no witness because F is retained.

**Exact degree certificate.** Set every declared variable `v_i=a_i z` with `a_i=i+2`, in the exact ordered list `parameters+auxiliaries` of that circuit. Work modulo 1,000,003. Attach to each gate its formal total degree bound and the coefficient at that degree after substitution. Constants have degree0, variables degree1. Multiplication adds bounds and multiplies top coefficients. Addition/subtraction takes the maximum bound and includes an operand coefficient only if its bound equals that maximum. A zero coefficient never lowers the formal bound.

This recursion computes the coefficient at the valid bound even when intermediate leading terms cancel. A nonzero output coefficient modulo an integer proves that the corresponding integer coefficient is nonzero, giving a matching degree lower bound. The native/spatial and phase4 output values are:

- INC2;DEC2: degree 2344, coefficient 135347 modulo 1,000,003
- ZERO3, NOP, POSITIVE3: degree 1192, coefficient 977370 modulo 1,000,003

Each JSON includes the complete substitution map and per-gate degree/top trace, making this a reproducible exact certificate rather than a probabilistic upper-bound claim. These degrees refer to the full polynomial in all supplied coordinates before existential quantification or zero-fiber restriction. They do not mean the represented relation intrinsically needs that degree.

## 6. Zero-step and other boundaries

For a source initially at its terminal state, fresh-entry/terminal-halt syntax makes that state isolated. There is no forward step and θ=0, F=N0. Cleanup consists of exactly the two NOP bridges, so its first time is

`384N0+16 = 384x+400`.

The separate emitted polynomial is `(384x+400−Tclean)^2`: 2M+2A=4 operations, no witnesses, one comparison and exact degree 2. Its phase4 version is `(1536x+1600−Tclean)^2`, with the same ledger. These are direct affine SOS circuits; they do not assert that an empty trajectory satisfies the positive-time residue packet.

For the four fixtures, F=N0 on every accepted path, and their clean times simplify to `1584N0+48` for INC2;DEC2 and `768N0+32` for the other three. Those equalities provide independent finite checks, but the emitted interface deliberately retains general terminal payload F. Additional wrapper checks for singleton INC2/INC3/DEC2/DEC3 include F≠N0 and raw coprime factors5 and7.

The older omitted-selector/endpoint hazard is avoided by retaining every raw selector and chronological endpoint comparison. In particular, the tempting fake ZERO3 halt at N0=3 and POSITIVE3 halt at N0=1 fail the retained transport row: the totalized next control is the trap, not h. Only the output-copy row F=y is eliminated, justified by the exact existential projection (2). No selector or encoded halt endpoint is eliminated. This construction does not route through a previously weakened fixed-horizon selector bridge.

All zero-set equivalences require the stated natural/strictly-positive integer domains. Although an SOS is nonnegative over the reals, no rational or real zero-set exactness is asserted. The result gives an input-dependent exact target and first hit, not one universal fixed target, stationary halting, arbitrary-time recurrence, or a universal ordinary-input instance.

### Positive witness fibers are infinite on accepted inputs

The deterministic source history does **not** determine the supplied unbounded arithmetic witness. Fix an accepted pair `(x,Tclean)`, hence its actual finite source history, terminal payload F and exact native time θ. Every sufficiently large dyadic height h, strictly above the encoded endpoint sum plus θ and all residue quotients, is permitted by the inherited completeness construction. Set η to the positive difference and B=C h². Pack the same chronological history at this B; the number of source steps t is fixed while P=B^t and J=(P−1)/(B−1) change.

The selected quotient classes are disjoint, so `Σ Z_a≤W≤(h−1)J`. The global slack satisfies

`β=(B−2)J−W−Σ Z_a−g ≥ (B−2h)J−g > 0`,

using C≥4, h≥3 and the inherited bound g≤m−1 together with its radix lower bound C≥m+1. Every packed lane coefficient remains in `[0,P)`. The packed AND is genuine, and the prescribed native scale `Q=B P^v` is dyadic and greater than the concatenated ports. Thus the inherited prescribed native completeness theorem supplies a positive native extension for each such h. The packed clock has nonnegative shifted quotient because its digits are positive and its ordinary sum is θ. Nothing in the cleanup square restricts h further.

Different dyadic heights give different retained `height_slack=η`, so they yield distinct full positive witness tuples even without assuming native witness uniqueness. There are infinitely many such heights. Therefore **each accepted fixed `(x,Tclean)` fiber of the emitted nonempty circuits is infinite**; rejected fibers are empty. These circuits are not finite-fold representations. This does not constrain the witness multiplicity of some different representation of the same simple relation. The separate no-witness zero-step circuits have just the empty witness tuple when their affine equation holds.

This is a consequence of the inherited all-height completeness proof, not a numerical construction of infinitely many Pell tuples. The checker additionally tests larger dyadic outer heights on concrete accepted histories; those finite tests merely check the implementation of the hypotheses.

If output and clock are existentially hidden, halting remains invariant under multiplying raw N0 by any positive c coprime to6. All guards and control states agree and every tick obeys `τ(cN)−8=c(τ(N)−8)`. Hence the accepted raw-input language depends only on `(ν2(x+1),ν3(x+1))`. In particular x=0 and4 cannot be distinguished for halting; on positive raw input coordinates, x=4 and6 cannot be distinguished. This excludes an arbitrary-c.e.-set claim for this ordinary raw coordinate. A fixed expanded universal separated reversible table, its ordinary-input decoder/loader, and a complete numerical audit of their costs remain separate unexecuted obligations.

## 7. Reproducible evidence and execution boundary

Run from this directory with standard Python3:

```sh
python emit_clean_clocks.py --check
python check_semantics.py --check
```

The emitter re-authenticates the upstream receipt, checks its literal finalizers/counts, emits every inherited arithmetic gate under time renaming, rebuilds every complete finalizer, and compares deterministic output bytes. Arithmetic DAGs are data; their producer Python is not run. The semantic checker independently interprets source instructions and all arithmetic rows. Its deterministic receipt records:

- 19,200 residue-state/clock evaluations including rejecting controls
- 576 accepted full outer packed histories with all four outer equalities and the complete packed AND checked
- 576 strict no-wrap checks and 576 coprime-scaled trace checks
- 192 prime-three false-halt transport rejections
- 576 each of clean-time, native-time and terminal-payload mutation rejections
- 384 complete signed modular SOS evaluations, including every native gate
- 390 zero-step exact polynomial evaluations
- 29 additional wrapper checks, including 13 with distinct terminal payload, plus one nonfresh-entry rejection
- 54 larger-dyadic-height outer extensions with unchanged input/clean time and distinct retained height slacks

Native and phase4 variants are counted separately; these are finite checks, not 576 distinct source programs. Exact circuit degrees are certified algebraically as above. Huge complete positive native/Pell witnesses have not been materialized, and native completeness is inherited. Independent audits and their reproduction commands appear in `audit/`; read their precise scope alongside this proof.
