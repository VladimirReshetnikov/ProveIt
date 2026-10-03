# Independent canonical history-height proof audit

## Verdict

**PASS for the proposed one-row positive-integer canonicalization, conditional on the inherited complete prescribed-native and clean-target theorems.** No mathematical obstruction was found. The projection of each accepted canonical full witness fiber onto its **22 retained native coordinates is a bijection onto the entire complete positive prescribed AND-extension fiber at the fixed actual padded ports and scale**.

The word “entire” is justified: none of the other comparisons uses a native auxiliary. Surjectivity is therefore valid for every solution of the prescribed native block, rather than only for some preferred extension produced by a native completeness proof.

This statement leaves native uniqueness and native finiteness unresolved. It eliminates the proven outer-height source of infinitude but does not establish finite-foldness. It is not a polynomial change of coordinates on all external inputs, an all-tuple identity with the old polynomial, or a bijection with the original unbounded-height witness fiber.

This audit addresses the candidate theorem, its inherited literal interfaces, and the actual eight emitted canonical JSON circuits pinned by the accompanying receipt. It verifies their native block preservation and canonical outer semantics. A separate full emission audit is still responsible for complete DAG closure/liveness, SOS assembly, operation ledgers, and exact degree certificates.

## 1. Frozen inputs, definitions, and dependency boundary

Read in full were the base `THEOREM.md`, `source/residue_affine_packed_history.md`, `source/three_mass_unbounded_interface.md`, `source/review_three_mass_unbounded_interface.md`, the original proof and emitted-circuit audits, the folded `ADDENDUM.md`, and its folding audit. The original raw builder and semantic checker were also inspected as text. The eight folded JSON circuit files and their eight new `*-canonical.json` counterparts were read and independently examined as inert arithmetic data; no packet producer or earlier checker was imported or executed. The new candidate paths and SHA-256 values are individually recorded in the accompanying receipt.

All 44 base manifest entries and all 42 folded manifest entries were authenticated before and after the independent checks. Manifest SHA-256 values:

- Base: `1bf1225aa950ad1d4f842c8bf098e1935925cd1d52c90453b7696c1321648f95`
- Folded: `774a4498984ebccf8216897e21bf597084e70b148557ba4fa12b597bba44ba91`

The inherited complete native/Pell theorem is a dependency, not independently reproved here. No large positive native/Pell tuple is materialized. This is the same dependency boundary as the frozen accepted-history theorem.

To avoid collisions, use `U` for the requested external clean time, `t` for the decoded number of forward source transitions, `N_i` for raw payloads, and `r_i` for shifted residue labels. For a fixed eligible nonempty-start source and natural `x`, put

- `N_0=x+1`
- `n_initial=K(N_0−1)+q_initial`
- `n_target=K(F−1)+q_halt`
- `S=n_initial+n_target+theta`

Here `F`, `theta`, and all supplied auxiliary coordinates are strictly positive integers. The inherited packet retains `h=S+eta`, with positive `eta`, and `B=C h²`. In the four emitted fixtures, `K=5`, `m=6K=30`, and `C=131072`; for the general eligible fixed-source construction, the old hypotheses on the dyadic `C` remain required.

The candidate adds exactly one positive supplied coordinate `kappa` and the one comparison

    eta+kappa=S+1.                                      (C)

Every comparison of the complete clean-clock packet remains, including the 16 native comparisons, both original outer comparisons, the physical clock comparison, and the clean-time comparison. This retention is essential.

## 2. The strict-next-power-of-two lemma

Because `eta` and `kappa` are positive integers, (C) gives `1<=eta<=S`, and therefore

    S < h=S+eta <= 2S.                                 (1)

Conversely, if an integer `h` lies in this interval, the only possible new slacks are

    eta=h−S,       kappa=2S+1−h,                       (2)

and both are positive. No exponent variable or exponentiation circuit is needed to enforce this interval.

The inherited complete native typing proves that `B` is dyadic. Since `B=C h²`, `C` is dyadic, and `h` is a positive integer, `h` has no odd prime factor and is itself dyadic. Exactly one dyadic integer lies in `(S,2S]`. Indeed, if `h_*` is the least dyadic integer strictly greater than positive `S`, then `h_*/2<=S`, so `h_*<=2S`; any smaller dyadic is at most `S`, while any larger dyadic is at least `2h_*>2S`.

Thus every canonical zero has

    h=h_* = the least power of two strictly above S.   (3)

The strict boundary matters. If `S=2^a`, then

    h_*=2S,       eta=S,       kappa=1.                (4)

Taking “least power of two at least S” would be wrong: it would give `eta=0` at this boundary. Conversely, replacing the upper bound by `h<2S` would wrongly exclude it. The `+1` in (C) and strict positivity of `kappa` supply the correct weak upper boundary.

The lemma holds for every positive integer S, including S=1, although actual nonempty source histories have much larger S. The dedicated scalar boundary tests are not represented as actual accepted fixture histories.

## 3. Why this small dyadic choice already bounds every actual quotient

The central additional completeness argument is valid and avoids an assumption that intermediate payloads are bounded by endpoint payloads.

For any current source configuration, write

    n=K(N−1)+q,       1<=q<=K,       m=6K.

The quotient in the shifted residue convention is exactly

    floor((n−1)/m) = floor((N−1)/6).                  (5)

For example, writing `N−1=6z+a`, with `0<=a<=5`, gives
`n−1=6Kz+Ka+(q−1)` and `0<=Ka+q−1<6K`. Hence its residue quotient is z, independently of the state code.

The primitive clock coefficients relative to the current payload N are:

- INC2: `300N+8`
- INC3: `396N+8`
- DEC2 when enabled: `150N+8`
- DEC3 when enabled: `132N+8`
- ZERO, POSITIVE, and NOP: `192N+8`

Therefore every genuine current step satisfies

    tau_i >= 132N_i+8 > N_i > floor((N_i−1)/6).       (6)

For a nonempty genuine first-halting run, `theta=sum_i tau_i`, so every current payload has `N_i<=theta`, indeed `N_i<theta`. Combining (5)–(6),

    quotient_i < N_i <= theta < S < h_*.             (7)

The terminal payload need not have its own outgoing tick; it is bounded instead by its positive encoded endpoint's inclusion in S. No quotient for the terminal configuration is packed. This distinguishes the two relevant cases and avoids applying (6) to a halt that has no physical source step.

Thus **every** dyadic `h>S`, including the unique canonical one, meets the residue-history completeness requirement that h exceed all current quotient digits. An additional maximum over intermediate quotients is redundant for these physical-clock histories. It would not be redundant for a general residue-affine orbit without this positive physical-clock lower bound.

## 4. Soundness, including the no-wrap dependency order

A zero of the candidate complete integer SOS annihilates all old residuals and (C). Forgetting kappa therefore yields a zero of the inherited complete clean-clock polynomial, on exactly its stated domains. That theorem gives the actual nonempty deterministic first-halting history, final payload F, exact native theta, and the first exact clean target at U. An extra row cannot introduce a false halt, a stuck-state acceptance, or a fabricated time.

For clarity, the inherited no-wrap proof does not depend on assuming that theta is already the real time or on the new lower-bound completeness argument. Its order is:

1. Positive supplied hats, height, and the retained global comparison give positive native ports and strict lane bounds before any digit typing.
2. The complete native theorem gives the packed AND, dyadic B and P, and therefore dyadic h. The original range mask types every quotient digit in `[0,h)`.
3. The original transport equality decodes an actual chronological orbit. Rejecting totalization ensures an orbit ending at the original halt is a first-halting genuine source orbit.
4. Every current encoded state is in `[1,mh]`. A deterministic first-halting path cannot repeat a current state, so `t<=mh`; its current payloads satisfy `N_i<=6h`.
5. Each genuine tick is at most `396N_i+8<=2384h`, giving

       0 < sum_i tau_i <= 2384m h² < C h²−1 = B−1.

6. Independently, the retained height identity gives `0<theta<h<B−1`. The retained clock equality implies `sum_i tau_i ≡ theta (mod B−1)`. The two strict ranges force equality.

Only after this establishes actual theta is (7) used to justify completeness at the small canonical height. There is no circular use of the proposed canonical bound to prove exactness of the time from which that bound is computed.

The cap does not weaken any retained no-wrap inequality. Nor can a malicious assignment increase theta by B−1 and adjust S, h, or kappa to make a spurious zero: the full inherited argument applies afresh to whatever positive values appear in that assignment.

## 5. Completeness and every strict positivity obligation

Fix an accepted external `(x,U)` and its genuine nonempty first-halting source history. Its semantic data F, theta, encoded endpoints, and length t are fixed. Set h to (3) and eta,kappa to (2). Both new/retained height slacks are positive, including boundary (4).

Set

    B=C h²,       P=B^t,       J=(P−1)/(B−1).

These are positive integers and B,P are dyadic. Pack the actual chronological residue selectors E_r, quotient word W, and selected quotient words Z_a in base B. Equation (7) ensures all quotient digits lie in `[0,h)`. Supply each nonnegative packed word by its hat, word+1, so zero quotient words, unused residue classes, and unused slope classes all give the permitted positive value 1.

Let g be the number of exceptional slope classes. Because those classes are disjoint,

    sum_a Z_a <= W <= (h−1)J.

The unique global slack determined by the retained global row is

    beta=P−J−(W+1)−sum_a(Z_a+1)
        =(B−2)J−W−sum_a Z_a−g
        >=(B−2h)J−g > 0.                            (8)

The strict last inequality is inherited uniformly from `B>=K_old h`, `K_old>=4`, `K_old>=m+1`, `g<=m−1`, `h>=3`, and `J>=1`. The symbol `K_old` here is the old residue packet's required radix multiplier, not the control encoding K. The squared radix dominates that old requirement; the new cap imposes no conflicting upper restriction on B.

Every scalar AND lane holds for the actual packed words. Each lane coefficient is in `[0,P)`: selectors/class selectors are at most J; quotient and selected words are at most `(h−1)J<P`; class masks are at most `(B−1)J=P−1`; and the range mask is `(h−1)J<P`.

For the fixed lane count `ell=m+g+1` and fixed least dyadic `v>=ell`, let H,M,A be the three concatenated ports. Then

    0<=H,M,A<P^ell<=P^v<Q_native=B P^v.

At the actual retained native boundary the ports and scale are

    A_p=16H+12,    B_p=16M+10,
    Z_p=16A+8,    q_native=16Q_native.                (9)

All three actual padded ports are strictly positive and strictly below q_native. The low padding bits satisfy `12 AND 10 = 8`, and the high parts satisfy `H AND M=A`, so the padded AND relation holds. The scale in (9) is dyadic. These are precisely the prescribed-scale native extension hypotheses used by the frozen completeness proof. It supplies at least one fresh positive 22-coordinate native extension at this fixed scale. Reusing any prior extension at a different height is neither needed nor claimed.

The unique shifted clock quotient is

    clock_quotient_hat=1+(C_tau−theta)/(B−1),
    C_tau=sum_i tau_i B^i.                           (10)

Here `C_tau−theta=sum_i tau_i(B^i−1)` is a nonnegative multiple of B−1. Thus (10) is positive; for t=1 it is exactly 1. The actual path supplies the chronological transport equality and the correct clean time supplies the clean-clock equality. Every supplied coordinate is now strictly positive, and every candidate comparison holds.

This proves canonical completeness without enlarging h, without leaving a merely nonnegative beta, and without excluding all-zero packed quotient words.

## 6. Exactly which outer quantities become canonical

Fix an accepted `(x,U)` for a fixed deterministic eligible source and clock model. The source start x fixes its unique first-halting history; acceptance of U asserts that this history's clean time is U. Consequently all of the following are uniquely determined:

1. The entire semantic forward history, its t, terminal raw payload F, and actual native theta
2. The encoded endpoints and S
3. h, eta, kappa, and B
4. P, J, all E_r, W, every Z_a, and their supplied hats
5. beta and the supplied clock quotient in (10)
6. Every outer arithmetic register and the actual native boundary tuple (9)

No alternate t is possible: the native dyadic argument gives `P=B^t` and an actual t-step orbit ending at the halt, while rejecting totalization makes such an orbit the unique first-halting trajectory. No alternate packing is possible because the same deterministic sequence has unique base-B digits, and the lane typing forces that packing. Beta and the clock quotient are determined by equalities with nonzero coefficient 1 and B−1, respectively.

The supplied nonnative coordinates are exactly the 30 residue-selector hats, quotient hat, any exceptional-class product hats, eta, beta, F, clock quotient hat, theta, and newly added kappa. In the folded circuits this is 38+1 nonnative coordinates for INC2;DEC2 and 36+1 for each other fixture. Computed arithmetic registers are not additional supplied coordinates.

This is a fixed accepted-fiber statement. It supplies no total polynomial algorithm sending arbitrary external `(x,U)` to its h or history, and no all-input polynomial normalization of an arbitrary old witness.

## 7. Full native-fiber bijection

Define `W_can(x,U)` as the candidate's complete positive witness fiber. Let `b(x,U)` be the uniquely determined padded boundary tuple (9). Define `E_native(b)` to be the set of **all** strictly positive assignments to the 22 retained native auxiliaries satisfying all 16 retained native comparisons at that fixed tuple.

The 22 coordinates, in emitted order, are:

    F0, F1, F2, a, c, d, f, h, i, j, k, o, r, s, w,
    tau, eta, zeta, ga, y_aux, odd_half, bound_beta,

each with literal `native__` prefix. Native h and eta in this list are separate coordinates from the outer height and height slack. Native F3 and q are computed from the prescribed Z port and scale and are not supplied coordinates.

Let pi retain precisely these 22 coordinates.

**Well-definedness.** Every full canonical zero has the fixed outer data proved above, and the retained 16 native comparisons hold. Hence `pi(W_can) ⊆ E_native(b)`.

**Injectivity.** Two full canonical witnesses with the same 22 native coordinates already have identical nonnative coordinates by Section 6. Therefore the whole supplied tuples coincide.

**Surjectivity onto the entire fiber.** Take any `u∈E_native(b)`, including extensions not selected by a particular native existence proof. Append the fixed positive outer tuple from Sections 5–6. All 16 native comparisons hold by definition of E_native. Every other old comparison and the new cap depend only on the fixed outer coordinates and external ports, so they still hold. The resulting full tuple lies in W_can and projects to u.

This last independence claim was checked directly on each of the eight frozen folded complete DAGs and each actual canonical DAG: the four inherited nonnative comparisons (indices 0,1,18,19) and the actual new cap (index 20) have no transitive dependence on any native auxiliary. The native block's only incoming outer values are the intended concatenated ports and native scale. For each actual candidate the complete native source gate sequence, ordered 22-coordinate list, and all 16 native comparison pairs are literally identical to its folded parent. The first 20 comparison pairs and natural free ports are preserved, and the only added supplied coordinate is `canonical_height_slack`. The actual `canonical_endpoint_clock_sum` register is checked to equal S on every finite outer test; `canonical_slack_sum` adds the two slacks, while `canonical_sum_plus_one` adds 1 to S.

Thus pi is a bijection. The inverse at a fixed accepted pair simply adjoins its fixed outer constants. No native uniqueness theorem is smuggled into this argument.

In particular, for each accepted pair, the candidate full fiber is finite if and only if its prescribed native fiber is finite, and has one member if and only if that native fiber has one member. The inherited native existence theorem alone settles neither proposition. For rejected external pairs, W_can is empty; the accepted-boundary construction above is not defined or asserted there.

## 8. Source, geometry, zero-step, phase, and domain boundaries

- The four emitted fixtures have distinct fresh entry and terminal halt and satisfy separated reversible syntax. Their accepted source paths have one or two steps; their complete encoding uses the general unbounded mechanism. No longer universal source is inferred from those fixtures.
- Source guards and rejecting totalization remain present. Disabled ZERO3/POSITIVE3 inputs are genuinely stuck, and the cap cannot turn their inherited empty fibers into nonempty ones. Infinite nonhalting paths likewise remain rejected by inherited soundness; bounded tests of prefixes would not prove unbounded rejection by themselves.
- The clean-wrapper hypotheses are unchanged: fresh entry, terminal halt, reversible separated syntax, and the inherited exact section/escape theorem. The new row acts only on arithmetic witnesses. It neither changes the CA nor weakens whole-configuration equality, absolute coordinates, phase, or first-target semantics.
- Native/spatial blocking uses `U=2theta+192(F+x+1)+16`. Phase4 uses four times that expression. **The S defining the cap still contains native theta**, not U, four times theta, or a source-step count. Phase4 changes no native residue clock, radix bound, or native extension fiber.
- Zero-step first halts have theta=0 and are outside this positive-theta packet. The separate no-witness affine zero-step circuits remain unchanged: native/spatial `(384x+400−U)^2`, phase4 `(1536x+1600−U)^2`. Their accepted fibers contain just the empty tuple, and no claim of a 22-coordinate projection applies to them.
- All equivalences require natural integer x,U and strictly positive integer supplied auxiliaries. Dyadic factorization and typed bit lanes are integer arguments. No rational, real, arbitrary-signed, or merely nonnegative-auxiliary exactness is asserted.
- Raw payload cofactors coprime to 6 are still preserved. The raw-input valuation obstruction to arbitrary-c.e.-set universality is unaffected. There is no new ordinary-input universal loader, numerical universal bound, minimal circuit theorem, later-recurrence result, or finite-fold MRDP implication.

## 9. Independent finite evidence and replay

The data-only checker `check_canonical_height_proof.py` and its deterministic receipt `canonical_height_proof_checks.json` are part of this audit. It imports no frozen packet code. It authenticates both pinned frozen manifests and every included copied reference, reads folded and actual canonical circuits as JSON, independently simulates their source instructions, constructs canonical outer candidates, and checks the literal outer arithmetic rows and packed AND hypotheses. The accepted-history and rejection counts include native/phase4 models and, where stated, both frozen/canonical versions; they are not counts of distinct source programs.

The receipt records:

- 32,768 scalar strict-next-dyadic checks, including 16 exact power-of-two S boundaries
- 6,656 residue-quotient/control-code identity instances
- 1,749 enabled primitive tick lower-bound instances, including DEC3's sharp coefficient 132
- Sixteen literal 22-coordinate/16-comparison native interfaces and 72 outer-row/native independence checks across frozen and actual candidates
- Eight literal complete native-block preservation checks on the actual candidates
- 3,072 accepted canonical full outer histories, comprising 1,536 frozen-parent histories and 1,536 actual-candidate histories
- 1,536 actual-candidate larger-height repackings: all old outer comparisons and joined AND still hold, but even the least positive kappa makes the new cap residual strictly positive
- 1,024 stuck-source inputs, with 1,024 deliberately false-halt candidates rejected by transport while their other outer comparisons hold
- 9,216 wrong-clean-time rejections, including 3,072 phase4 times not divisible by four
- 3,072 actual kappa mutation rejections
- 4,096 smaller-height domain failures, 12,288 scalar larger-height exclusions, and 5,120 quotient-bound instances across genuine and deliberately false outer candidates
- 60 accepted histories with all-zero quotient word
- 390 exact evaluations of the separate unchanged no-witness zero-step circuits

All actual padded port bounds, positive global and clock slacks, complete joined ANDs, all four frozen/five canonical nonnative comparisons, and strict no-wrap bounds pass for the accepted outer candidates. The finite tests do not evaluate a complete positive native/Pell zero and do not prove native multiplicity. They supplement the all-input proof above.

Reproduce read-only from the artifact root:

    python audit/check_canonical_height_proof.py --expect audit/canonical_height_proof_checks.json

The checker resolves its packet root from its own script path, then uses only `reference/base`, `reference/folded`, and the actual `circuits` directory. Its receipt stores relative artifact paths and no absolute workspace paths. The default replay authenticates all eight included base references and ten included folded references, in addition to the two pinned manifests; it does not require either original frozen sibling directory. A fresh process launched with `/tmp` as its working directory reproduced the receipt using absolute paths only for the checker and expected receipt arguments.

For an additional full before/after verification of live frozen siblings, optional arguments are available:

    --check-live-base /path/to/unbounded-clean-clock-20261003
    --check-live-folded /path/to/unbounded-clean-clock-phase4-folding-20261003

These optional checks authenticate all 44 and 42 entries respectively and do not alter the deterministic receipt. They were successfully run against the original frozen siblings. Both frozen inputs were unchanged throughout. All new files produced for this audit are confined to the requested new audit directory.

## 10. Final main-theorem review

**Final verdict: PASS, with no remaining mathematical or scope finding.** The main `THEOREM.md` was read in full, and the final generic-source wording was rechecked after correction. The reviewed theorem SHA-256 is `6d48066a8384c055ed1cffef087b520ce55a73475ea8f42654e726837c11c66e`.

The main statement correctly distinguishes the general eligible fixed-source construction from the four literal circuits in the frozen folding packet. Eligibility retains the inherited raw/native and separated-source clean-wrapper hypotheses; it does not claim an emitted universal source or a general fresh-entry transformation. Its two directions, exact physical-clock lower bound, first-halt no-wrap argument, strict dyadic boundary, and positive global/native extension are consistent with this audit.

The stated supplied-coordinate counts are correct: 39 outer plus 22 native for INC2;DEC2, and 37 outer plus 22 native for each other canonical fixture. The full accepted fiber projects bijectively onto all solutions of the complete prescribed native block at its uniquely determined actual ports and scale. The theorem explicitly leaves native uniqueness, finiteness, and infinitude unresolved. Neither finite-foldness nor an ordinary-input MRDP consequence is claimed.

The text also correctly separates two logically different assertions: reassociating the old height additions preserves the old residual polynomials on every integer tuple, whereas selecting and adjoining a canonical semantic outer tuple is only an accepted-fiber construction. The new complete polynomial adds a square and is not the old polynomial or a global polynomial witness reparameterization. Phase4 still uses native theta in S, the no-witness zero-step case remains separate, and genuine stuck/nonhalting inputs gain no zero.

A final fresh read-only semantic replay passes on the actual candidate bytes recorded in the receipt. The checker and receipt are portable through the authenticated copied reference directories described in Section 9. Complete emitted ledger/degree/SOS certification remains the separate arithmetic audit's responsibility, as stated at the start of this report.
