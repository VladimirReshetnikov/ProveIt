# Review of the three spectral archives at060e08a07

The main mathematical constructions survive this review. They give canonical positive-spectrum sign certificates, externally bounded ordinary quartics, and a precise connection between infinite clocks and path-bounding degrees. They do not supply a new ordinary fixed-arity universal polynomial or an arithmetic-operation improvement over the project's complete87-operation construction. Five implementation/interface findings were reproduced and repaired privately: an unauthenticated difference chain, mutable cached coefficients, a two-point polynomial-identity check, a mutable machine descriptor, and incomplete exact-type/schema checks in the second spectral exporter. None is a counterexample to the reports' mathematical theorems under their stated hypotheses.

The archives were retained untouched. Only temporary extracted copies and the three accompanying unified patches were changed. The portable checker accepts original extracted package roots and patch paths, authenticates every original archive member before imports, applies the patches to temporary copies, verifies resulting source hashes, and removes/restores the package import namespaces. Its receipt includes the full archive/member inventory, repair pins, author commands, independent cases and export comparisons.

## Provenance and coverage

| Archive | SHA256 |
|---|---|
|Positive_Spectrum_Diophantine.zip|fe519471be068a0f7f5822c2fd89f1767f15d60379fb8d06d4b7b87f994dfdf8|
|Spectral_Guards_Without_Time_Expansion.zip|0a5cf2d12333bab718453e1139622518f55b6361bd0e947f47d8e748d06f9e53|
|clock_spectra_research.zip|dbbcc5ed44b2a1b87da14ab863c32a5b125484480652fa9a04c5e0340082fb22|

Initial extraction rejected absolute paths, parent traversal, backslashes and symlink entries. The review read the three complete article sources, all README/audit material, and every supplied computational module and author test. It replayed all nine meaningful documented Python invocations, both originally and after the applicable repairs. LaTeX was not rebuilt, no proof-assistant formalization was run, and the finitely sampled calculations do not mechanically prove any infinite-time or computability theorem. The latter received a mathematical proof audit, with the principal imported modulus and exponential-representation statements checked against primary research sources.

Source references below are relative to the top directory inside each respective archive. All source line numbers refer to the untouched originals.

## What is actually represented

**Positive Spectrum.** For fixed positive integer bases and fixed degree limits, the input consists of canonical signed coefficient coordinates and, in finite mode, a natural horizon. The chain applies positive-root differences `E−a`; its row at remaining declared dimensiond has at most2d−1 maximal discrete sign runs. The allocated whole-chain capacity isD²+1. This is an allocation bound, not a simultaneous sharp-minimum claim. The proof's use of a real zero bound controls the number of discrete runs; it does not replace integer-time positivity by real-interval positivity.

The endpoint argument is sound: a constant-sign child makes the normalized parent monotone on the child's lifted interval, and testing the relevant parent/child endpoints forces the whole claimed parent run. The infinite version checks the eventual sign from the largest active base and highest nonzero coefficient. It does not guess a stabilization time. Zero sequences, zero-length finite horizons and inactive padded slots are covered. Canonical signed parts, pinned inactive slacks and unconditional evaluation of arithmetic wires are necessary for the stated unique *complete* witness tuple.

The compiler leaves fixed-base power graphs. Its expanded quartic is exactly the SOS of the arithmetic residuals, but the full certificate also requires52 power atoms in each delivered example. Replacing those atoms by unspecified MRDP witnesses gives ordinary existence, without this implementation's uniqueness, fixed paid operation count or witness bound. The finite and infinite chart algorithms are effective, so there is no hidden oracle in the infinite sign-chart construction itself.

The triangular-loop transfer is also coherent: weighted monomials give a finite invariant space, and positive diagonal scalings yield a positive rational-split spectrum after lifting. The shape and polynomial observables are fixed in advance. Repeated execution of a specified word and composition of a fixed number of phases are covered. Unbounded branch switching in a universal program is not thereby compressed to a fixed number of phases. These finite-dimensional polynomial coefficient calculations are not an encoding of an arbitrary finite-support polynomial witness by a bounded tuple of integers; such an extra transfer would require its own coding theorem and paid costs.

The order-two boundary is valid. The unique padded chart of2^n−y on[0,T] has final active sign zero iff y=2^T. Existentially projecting that unique chart therefore preserves single-foldness, and finite-foldness similarly. Conversely the chart graph is computable. Combining this with single-fold unary-exponential representation yields the manuscript's equivalence with the general SF/FF assertions. This does not prove an arithmetic lower bound for every order-two recurrence. The exact unary-power formulation was cross-checked in the repository's `DPR.lean` (`re_sfu`, line309; `re_single_equation`, line318), without rebuilding it. The primary research paper [Cantone–Cuzziol–Omodeo,2024, p.588](https://arts.units.it/bitstream/11368/3101478/1/CCO24.pdf) explicitly states the corresponding single-fold polynomial-plus-2^u form and its4^u+u variant. The original1984 Jones–Matiyasevich paper's publisher page was located, but its full text was not accessible during this review; no full-original-paper audit is claimed.

**Spectral Guards.** This compiler instead treats ordered positive integer bases as inputs at fixed multiplicity shape. Its all-pairs endpoint implementation hasD²+1 slots andQ_D=(4D³−6D²−D+6)/3 allocated adjacent-row slot pairs, yieldingO(D⁴) arithmetic size with direct endpoint evaluation. Positive Spectrum's shared endpoint scheme gives the statedO(D³) bound in its different fixed-base interface. These are residual/witness growth statements, not counted complete universal SLP ledgers.

The ordinary quartic mode takes an external exponent bit widthB. Binary bits, repeated squares, product wires and a horizon slack enforce0≤T<2^B. The resulting SOS is an ordinary natural-number polynomial, and the unique witnesses are valid for this externally selectedB. IncreasingB changes the emitted arity and syntax. TreatingB as an unbounded input to the same emitted finite circuit would be invalid.

The permanent-sign bound is sound. For the largest active baseB*, leading degree m, lower coefficient massA0, next baseb*, remaining coefficient massC0 and maximum degreeM0, letK=max(0,M0−m). At n>2A0 the leading polynomial has its leading sign and magnitude at least|a|n^m/2. The binomial estimate for(B*/b*)^n uses n≥2(K+1) and B*/b*≥1+1/b*. The reported threshold's final term forces strict domination of all lower modes. The zero sequence and single active base are handled separately. The software implements this scalar threshold, not a complete separate exported all-time frontend.

The order-two oscillation obstruction is also correctly scoped. Foru_n=Re((3+4i)^n), the rational trace6/5 excludes a root-of-unity phase. Every fixed residue subsequence has positive sign-change density and linearly many raw sign runs. This rules out the particular bounded interval-chart format, including fixed residue splitting. It is not a general Diophantine impossibility theorem for that sequence.

**Clock Spectra.** Adequacy means one infinite run satisfies every deadline of one functiond. Neither independently successful prefixes nor a separate clock for everyk suffice. The finite Good predicate includes all earlier deadlines and a horizon at least their maximum; finite branching and compactness recover a compatible infinite run. The explorer's unary guesses provide a path bound from a clock. Conversely a bound on a path supplies computable finite runtime maxima because the given tree decider is total. This conversion is computable, without a claimed elementary or primitive-recursive overhead.

The first-matching-stage singleton construction avoids a false settling-time premise. Each coordinate chooses the least stage≥n matching a nested length-n word. Along an infinite path these stages tend to infinity, so convergence forces every persistent bit to the true limit. The path and the limit compute each other. The approximation's convergence is a mathematical promise, not decided by the finite checker.

The deferred-oracle hierarchy checker is prefix closed: an established rejection depends only on already available answers; a genuinely unknown lower query defers a check; zero claims receive growing simulation budgets. On a well-order, induction forces every row to be the intended jump row. The decidability and well-order hypotheses are finite-program/semantic assumptions, not an embedded infinite oracle or an algorithm deciding well-foundedness. The effective disjoint-union result concerns degree spectra and does not claim uniform recovery of a successful component from an arbitrary clock.

The least-degree argument uses leastness, not mere minimality: every pointwise majorant of an adequate clock remains adequate, hence computes the least degree; an adequate clock in that degree is a self-modulus. [Monin–Patey, Corollary2.2](https://arxiv.org/html/1603.01086) identifies admitting a modulus with hyperarithmeticity. Its stated modulus is nonuniform Turing recovery, exactly the notion used here. The report does not equate this automatically with uniform self-moduli or claim a complete least-degree classification.

The finite compiler's domain isN. Its gadget

    G(D,s,a,b)=(D−a+b)^2+ab+s(a+b)

is a sum of nonnegative terms when s,a,b are natural. Its zero forces a=max(D,0), b=max(−D,0), and selected residuals to vanish. Natural selector sum1 supplies one-hot selection without additional Boolean equations. The full quadratic has3(T+1)+9mT+k coordinates, including all inactive-rule helpers. It gives a bijection with *labelled* legal traces, so duplicate rules intentionally give distinct natural zeros. The seven-rule fixture is expressly nonuniversal. A fixed universal two-stack interpreter is proved possible, but its literal table and ordinary loader are not instantiated in this archive.

The infinite object remains `exists function d, for all k, exists finite z_k`. The finite polynomial family grows with the external horizon and the number of deadlines. It is not one ordinary finite existential integer tuple. Ordinary MRDP can represent each coded finite Good predicate; it does not remove the outer universal/function quantifiers. Likewise, base-four rational stack coding gives exact finite-word rational states and step-preserving affine dynamics, with no robustness claim for arbitrary real perturbations and no solution of Hilbert's tenth problem overQ.

## Concrete findings and private repairs

1. **Unauthenticated annihilator input — Positive `code/profiles.py:165,184`.** The public constructor and local verifier accept a chain rather than constructing it themselves. The verifier never checks the bottom function or the relation between adjacent functions. With f(n)=4^n−20·2^n+64, the supplied chain[f,0] and rows`[0,6]:+`, `[0,6]:0` pass, although f(3)=−32. The compiler's normal path calls `make_chain`, so this is a trust-boundary gap, not failure of the conditional monotonicity theorem. The repair authenticates each formal polynomial-exponential step. For f≠0 it recoversa from one nonzero coefficient ofEf−g, checks that it is a positive integer and checks every coefficient ofEf−g=a f. A zero parent must have zero child, and the bottom must be zero. This requires no horizon scan or sampled-power inference. Both public construction and verification use the check.

2. **Mutable cached coefficients — Positive `code/profiles.py:28–57`.** After caching the endpoints of constant1, assigning `f.terms[1]=(-1,)` leaves those cached values1 while uncached values and eventual-sign data become−1. The old positive finite chart still verifies. The repair copies coefficients into immutable tuples behind a read-only mapping/property. Exact integer validation is strengthened. The memoization key uses`typed=True`: checking exact types only inside a cached function would otherwise let warmed integer1 alias BooleanTrue or float1.0 before the check executes. The regression explicitly warms this cache before malformed calls.

3. **Two-point check is not polynomial equality — Positive `code/check_export.py:18–33`, article.tex:1470–1484.** The advertised expansion check tests the sample root and one deterministic off-zero vector. Add(x0−64)(x0−3) to the delivered finite quartic: both tested points are unchanged, the original checker printsPASS, and at the otherwise-zero vector with x0=65 the mismatch is62. The actual delivered expansion is correct: this audit independently convolves every residual with itself and sums all monomial coefficients, obtaining exactly the delivered7,502/8,256 monomials. The repair uses this full sparse coefficient equality, validates exact coefficient/index/domain syntax and keeps validation active under`python -O`. It still checks the equations that are supplied; it does not authenticate an arbitrary JSON file as the output of the intended compiler.

4. **Frozen Machine retains mutable caller containers — Clock `code/clock_certificates.py:99–111,224–259`.** Construct with a rule list, initial list and accepting set; compile a stay transition at state0; then replace the caller's rule by7→7 and initial state by7. The old zero still validates, while the retained descriptor and subsequent export claim initial state7. The repair copies rules/initial into tuples and accepting states into a frozenset, validating each original element *before* set canonicalization can merge an invalid0.0/False with0. Rules must be validated Rule objects. It also rejects nonexact binary stack bits; previously`encode_stack([0.0])` returned float1.0. Deliberate mutation through private internals or Python's frozen-object bypasses is outside the claimed public snapshot boundary.

5. **Exact numeric/schema boundary — Spectral `code/quartic_compiler.py:70–77,188,301–318`.** The original serialized checker accepts a Boolean coordinate, a float coefficient, and a negative variable index aliasing a legal coordinate. The emitter also accepts BooleanTrue as bit width. The repair requires exact positive integer width orNone, an exact Boolean nonnegativity flag, natural exact integer assignments, nonzero integer coefficients, normalized bounded-index monomials, compatible mode/power declarations and coordinate/input schemas. The checker returnsFalse for malformed serialized equations. This is explicitly an equation checker, not a proof that freely replaced residual lists encode the advertised chart. The patch does not claim to harden every low-level mutable Poly/Emitter research object.

The patches are `positive_boundaries.patch`, `spectral_boundaries.patch` and `clock_boundaries.patch`. They apply with zero fuzz to the pinned originals. They do not change the compiler's mathematical residuals on valid inputs, its arity, its power-atom obligations or its universal-scope limitations. All fifteen nonvolatile JSON artifacts, including every complete certificate, regenerate byte identically both before and after repairs. The two runtime-bearing test records agree after removing only the known `elapsed_seconds` or `python` field at its exact path.

## Executed evidence

The portable receipt records all of the following; repeated original/repaired runs are not described as additional distinct mathematical examples.

- 180 independent scalar fixtures,867 finite/infinite chain rows checked against literal sampling,2,748 E−a value identities,531 permanent-tail samples and18 additional emitted spectral systems. Tail samples support the implementation only; the infinite guarantee rests on the audited dominance proof.
- Exact full sparse-SOS identities for both Positive exports, including all7,502 and8,256 monomials and all52 power atoms on each supplied assignment.
- 1,617 natural guard tuples;288 complete clock polynomial comparisons against an independent literal formula,144 with signed coordinates;59 canonical labelled-trace/deadline zeros and110 deadline failures, including nonmonotone deadline tuples.
- A signed guard counterexample(D,s,a,b)=(1,1,1,−1), for whichG=0 despite selectedD≠0. A separate nonnegative-rational zero with duplicate stay rules and selectors1/2,1/2 demonstrates why the natural-domain trace bijection does not extend toQ≥0.
- 65 focused repaired-boundary rejections, two immutable snapshot scenarios, and an optimized-Python expanded-polynomial rejection. The two-point forgery is normalized into a genuine sparse polynomial, so its rejection is due to unequal polynomial coefficients rather than duplicate-term syntax.
- All nine original author commands and the same nine repaired commands pass. The original author suites' own counts are preserved in the receipt and are not relabelled as independent checks.

The replay commands, from each original or private repaired package root, are:

    # Positive Spectrum
    python code/profiles.py
    python code/test_profiles.py
    python code/test_applications.py
    python code/compiler.py
    python code/check_export.py data/finite_certificate.json data/infinite_certificate.json

    # Spectral Guards
    python code/run_tests.py
    python code/supplementary_checks.py

    # Clock Spectra
    python code/test_all.py
    python code/verify_export.py examples/quadratic_certificate.json

The standalone helper's public interface is:

    verify(positive_root, spectral_root, clock_root, patch_dir, *, run_authors=True)

Its CLI takes the corresponding `--positive-root`, `--spectral-root`, `--clock-root`, `--patch-dir`, and optional `--output` or `--expect`. It has no fixed temporary-directory dependency. Source/member and patch authentication precede imported execution; all author scripts run in fresh private copies with timeouts. The receipt removes no mathematical data when normalizing runtime metadata. The source files retain all author assertions; the independent checker and the review assertions themselves use explicit exceptions.

## Concrete relevance to reducing arithmetic complexity

The strongest transferable component here is endpoint sharing for a fixed-dimensional positive-spectrum phase, together with exact canonical sign arithmetic and a declared obligation to pay for power graphs. This could reduce a *specified phase* within an existing universal compiler if that compiler already pays for the needed exponentiation and the number of phases is bounded independently of runtime. The source-pinned exact power/output interface, ordinary input loader and complete operation ledger would have to be supplied before claiming a universal saving.

The clock gadget gives a genuine degree-two natural trace polynomial, but charges9mT rule coordinates and an external horizon. The arithmetic complexity does not disappear because its degree is low. Its canonical inactive helpers are useful for a bounded compiler with uniqueness requirements; an existence-only projection could have different costs and would need a separate proof. No current result here beats the existing fixed87-operation construction, nor closes the unbounded phase/history or ordinary-input obligations.

## Repository archive replay

Run `python replay_spectral_060e08a07.py` from this directory. The
[wrapper](replay_spectral_060e08a07.py) authenticates the three incoming archives,
recovers missing copies from the pinned arrival commit, extracts to temporary
directories and compares the full saved review receipt. The
[three checked patches](spectral_repairs_060e08a07/) remain separate from the
immutable archives. It runs all nine original and nine repaired author commands.
