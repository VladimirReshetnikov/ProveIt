# Independent compatibility audit: unbounded compact clean clocks

## Verdict and dependency boundary

**PASS for the proposed nonempty-start, fixed-source composition, subject to the retained integer-domain contracts.** This audit checks the mathematical interface and the four pinned source fixtures. It does not independently reprove the inherited native/Pell theorem, re-execute the third-party author scripts, or claim that huge native witnesses have been constructed. A separate literal audit must check the newly emitted complete circuits against this composition.

The raw construction and its independent review were read at ProveIt commit `ad634b2d10ad666260f9fdff04ec94b75169ee4b`:

- [Author note](https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.md)
- [Independent review](https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_three_mass_unbounded_interface.md)
- [Author source](https://github.com/VladimirReshetnikov/ProveIt/blob/ad634b2d10ad666260f9fdff04ec94b75169ee4b/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/three_mass_unbounded_interface.py)

The clean-wrapper dependency is the inherited `CLEAN-TARGET-THEOREM.md`, SHA-256 `3d85f8cde66837d8916fb3273c2c57cc1a91ce37de1f3d6c6fe28a4db9103168`. The raw author note, receipt and source hashes agree with the pins quoted by its independent review. They are respectively `d336c8c12d3328eb4b6857ee382f91b2c9363f50effba5a7b1bf75308f25df45`, `fe69f0504c8f68c4130c4b21fed5c817596ab5c0e2fdf9621b0bf5f45c12ac0e`, and `cf9aee77ab78d68a165cbc31e19ded6d1de69663b34e0078f0106777b472340a`.

## 1. The precise theorem that composes

Let R be a fixed reversible separated two-counter source whose initial state q0 has no incoming instruction and whose sole designated halt qh has no outgoing instruction. First assume q0 is distinct from qh. Let x and S be external natural-number coordinates, with natural including zero. Start R at raw payload N0=x+1. If R first reaches qh after a nonempty run, let F be its terminal raw payload and let theta be the sum of its literal native physical instruction durations.

The inherited raw circuit P_R(x,y,T; auxiliaries) has natural x,y,T and strictly positive integer auxiliaries. Its distinguished positive auxiliary F is used to encode the target K(F−1)+qh; a separate comparison F=y restores the natural external output interface. On its complete zero fiber it represents exactly first halt with final payload y and native time T.

Construct Q_R(x,S; auxiliaries,theta) as follows:

1. Remove external y and only the comparison F=y
2. Keep the strictly positive auxiliary F and its existing encoded target port
3. Rename native T everywhere to a fresh strictly positive integer auxiliary theta, including its occurrences in the height and native clock equality
4. Keep all other comparisons and append the affine comparison

   2 theta + 192(F+x+1) + 16 = S

5. Emit the full sum of squares for this resulting comparison list

Then Q_R has a zero with all auxiliaries strictly positive integers if and only if the CA compiled from the clean wrapper of R first reaches its exact canonical target C(H,x+1) at native time S, from C(F:q0,x+1).

Here `F:q0` denotes a forward-copy control label; it is unrelated to the terminal-payload auxiliary F. The target configuration depends on x. The CA is fixed after R is fixed. This statement is a compact certificate for the specified encoded source dynamics, not a verifier for arbitrary microscopic configurations or arbitrary paths in the CA.

### Soundness

All SOS summands are real squares, so a zero annihilates every retained comparison and the new comparison. Set the removed natural coordinate y equal to the retained positive integer F. Set the original natural T equal to theta. This reconstructs a complete raw zero. The inherited theorem therefore decodes a genuine nonempty first-halting R trace, with terminal raw value F and native duration theta.

The clean-wrapper theorem supplies the exact forward trace, a halt bridge, the uniquely determined inverse source trace, and a final entry bridge. Every reversed arithmetic step restores its actual input; every reversed test checks the unchanged payload. Entry freshness prevents an earlier encounter with backward q0, and halt terminality makes both bridges legal. The input raw integer, including its cofactor coprime to 6, is restored exactly. The two bridge durations are 192F+8 and 192(x+1)+8. Each reversed instruction has the same native duration as its paired forward instruction. Thus the first exact target occurs at precisely 2 theta+192(F+x+1)+16=S.

### Completeness

A genuine first halt has positive F and positive theta, because the run is nonempty and every native instruction duration is positive. The raw theorem supplies its positive integer witnesses with y=F and T=theta. Forgetting y and the redundant equality, promoting theta to a positive auxiliary, and setting S to the displayed clean clock produces a zero of Q_R. No second reverse-history packet or reverse native witnesses are needed: the inherited source wrapper and compiler determine the reverse half.

The direct positive-theta version is preferable to the originally proposed W−1 substitution here. Both are correct, but the shifted version adds an unhat subtraction. Direct positivity is justified only by nonempty first halts. The inherited residue packet already has an interface called W for its packed quotient word, so a clock witness should use a fresh, unambiguous name.

## 2. Why output elimination and witness domains are safe

Literal inspection of each pinned fixture confirms that y occurs only in the final residual F−y. No height, target, chronological transport, native comparison, or clock word depends on y. Therefore

   exists y in N, F>0: [remaining constraints and F=y]

is exactly equivalent to

   exists F>0: [remaining constraints].

This is an existential projection, not a claim that the old and new polynomials have equal values away from their zero sets. Merely deleting F as well would be wrong: its positive encoded target is part of the inherited positive-native theorem and its value is needed for the halt bridge duration.

The terminal F is generally different from x+1. All four pinned examples happen to return F=x+1, including INC2;DEC2. Consequently these four examples alone cannot test the terminal-payload dependence. A singleton fresh-start INC2 source gives F=2(x+1), theta=300(x+1)+8 and S=1176(x+1)+32. It is a useful separate boundary test without attributing a full emitted circuit or numerical bound to that extra machine.

The external natural coordinates are exactly x,S. All inherited auxiliaries, including F and the shifted clock-congruence quotient, remain positive integers; theta adds one positive auxiliary. There is no external or hidden fixed horizon parameter. The packet's duration is decoded existentially from its native positive witnesses. Witness tuples need not be unique; the raw unbounded construction has height/native multiplicities.

## 3. The four fixtures satisfy the clean wrapper's structural requirements

| Fixture | Literal source | Entry incoming | Halt outgoing | Nonempty accepted length |
|---|---|---:|---:|---:|
| incdec | s INC2 a; a DEC2 h | 0 | 0 | 2 |
| zero3 | s ZERO3 h | 0 | 0 | 1 |
| nop | s NOP h | 0 | 0 | 1 |
| positive3 | s POSITIVE3 h | 0 | 0 | 1 |

Every incoming and outgoing source group is a legal singleton. The two ZERO3 residues are expanded branches of one zero test, not conflicting source instructions. All fixtures have s distinct from h. The inverse-copy construction and both NOP bridges therefore preserve reversible separated syntax.

For N=x+1, the accepted native and clean times are:

- incdec: F=N, theta=600N+16, S=1584N+48
- zero3, nop and positive3 when enabled: F=N, theta=192N+8, S=768N+32

ZERO3 accepts precisely N not divisible by 3; POSITIVE3 accepts precisely N divisible by 3. At their disabled inputs the source is stuck nonfinally. The raw rejecting totalization sends those configurations to a permanently rejecting trap, so they cannot acquire a false native zero. The clean wrapper also remains in its forward copy and does not reach H.

## 4. No-wrap proof is retained without modification

The raw height remains h=n_initial+n_target+theta+eta with positive integer eta; the radix remains B=C h², with C dyadic and C at least 2384m+2 and the inherited required multiplier. Removing F=y changes neither expression. Directly renaming T to theta changes no numeric value or range on a zero.

The inherited global bounds apply before digit typing. The native theorem forces B dyadic and therefore h dyadic. Its range mask gives actual quotient digits 0<=z<h. The old transport equality, independently of the new clock equality, then gives a deterministic first-halting path whose current encoded values are in [1,mh]. No current value repeats: a repeated deterministic configuration would force a cycle before the eventual first halt. Hence the decoded transition count t is at most mh.

Each current raw payload is at most 6h. Each genuine tick obeys 0<tau<=396N+8<=2384h. Therefore the actual native sum obeys

   sum tau <= 2384m h² < B−1,

where the strict final gap is at least 2h²−1. Independently 0<theta<h<B−1. The retained clock equality still gives sum tau congruent to theta modulo B−1. These two ranges force equality. The clean affine comparison is applied only after this exact native time has been established; it introduces no new modular checksum and needs no new radix bound.

Completeness chooses a sufficiently large dyadic h for the actual endpoints, native time and residue quotients. Positive height slack and all inherited global/native extensions remain available. Promoting positive theta does not constrain this choice. No old Pell tuple at another radix is reused.

This argument depends on first halt and rejecting totalization. It does not establish no-wrap for arbitrary endpoints admitting later loops. It also does not authorize removing any of the 16 native comparisons, the two inherited outer comparisons, or the native clock comparison.

## 5. Zero-step, exact geometry, cofactor and domain limits

### Zero-step first halt

If q0=qh, freshness and terminality make it isolated. The clean wrapper consists of its two NOP bridges and restores the original configuration at S=384(x+1)+16. The raw nonempty packet and the positive-theta interface do not cover this case. A separate polynomial

   (384(x+1)+16−S)^2

is sufficient for that fixed source. There is no hidden zero-step exception inside any of the four fixture totals.

### Exact geometry and stalled continuation

At a canonical native section the fixed right marker is at 0; the clean stage-zero controller and stationary shuttle are at −12(x+1). Every other site/channel is vacuum. The target is equality of this whole finite configuration at absolute coordinates, with the new final control H. Restoring only the two prime valuations would not suffice; the wrapper restores the entire raw integer and hence the location.

The inherited compiler proof excludes earlier H sections and excludes a stuck source's prescribed shuttle escape from creating the canonical target. It also excludes reliance on arbitrary completion rows before the first target, or along the relevant nonhalting/stuck continuations. No stationary halt or claim about later post-target evolution is made.

Spatial blocking gives radius one, left coordinate −3(x+1), zero offset, and exactly the same S. The four-phase construction uses the original coordinates and phase-zero target, with first exact time 4S. These follow from the inherited conjugacy/section statements; the newly emitted formula must specify which clock it represents.

### Raw cofactor and ordinary input

Write N0=2^a 3^b c with gcd(c,6)=1. Guards depend on a,b, but the raw source transports c and the clean wrapper restores it. Multiplication by any positive c coprime to 6 preserves the control sequence and halting truth, while scaling every nonconstant tick contribution. The raw coordinate cannot distinguish x=0 from x=4 after output and clock are existentially hidden; on strictly positive inputs, x=4 and x=6 are similarly indistinguishable. Thus this composition does not yield every arbitrary c.e. subset of an ordinary raw input coordinate.

Neither an abstract universal reversible counter machine nor an effective external encoder supplies a paid ordinary-input loader. The four sources are nonuniversal examples. The composition is compatible with fixed-source encoded-domain statements, but it proves no new universal operation bound or improvement on an unrelated universal bound.

### Rational and global-domain limits

SOS zero is equivalent to simultaneous equalities over the reals, but the trajectory/native theorem relies essentially on integer inputs and positive integer auxiliaries. This audit gives no exact rational-zero, real-zero, arbitrary-signed-integer, or globally positive-extension theorem. In particular, treating positive real theta as though it were a natural requested native clock is invalid. The finite-horizon rational decrement counterexample already shows that similar local arithmetic constraints cannot justify such a domain extension.

## 6. Literal cost obligations and exact degree certificates

Removing the old F=y SOS slot removes one multiplication and two additions/subtractions, including its finalizer accumulation. Given x,F,theta, the new affine clock requires two multiplications and four additions/subtractions. Its new SOS slot needs one multiplication and two additions/subtractions, including accumulation. The net change from each complete raw source is therefore +2M+4A. Retaining 19 raw comparisons and appending the clean comparison gives 20 total.

The anticipated complete totals are incdec 239M+365A=604 with 60 positive auxiliaries; zero3 184M+295A=479 with 58; nop 182M+295A=477 with 58; positive3 189M+291A=480 with 58. These are accounting consequences of the specified literal schedule, pending independent inspection of the actual emitted source. Parameter renaming is free; a W−1 implementation would not have these same literal totals unless a separately justified optimization removes its paid subtraction.

The raw formal degree bounds 2344,1192,1192,1192 remain upper bounds after adding an affine clock square. They may be promoted to exact degrees only with a lower-bound certificate. One compact method substitutes every declared variable v_i=a_i z and computes the coefficient of z^D modulo an integer modulus. For every gate retain its formal propagated bound d. At a sum/difference include an operand's formal-top coefficient only if its bound equals d; at a product multiply the formal-top coefficients. A nonzero final coefficient modulo the modulus proves a genuinely nonzero integer coefficient, so the polynomial's degree is at least D and hence exactly D. Zero intermediate tops do not permit pretending lower-degree terms are absent: retain their formal bounds throughout. No primality assumption is needed merely for the nonzero-modulus implication.

## Final audit conditions

The final circuit review should verify: exact source pins; literal retained comparison identities; absence of y; fresh positive theta substitution at both old T uses; retained positive F and its encoded target; full finalizer reconstruction; closed/live gates; exact net counts; and an independently recomputed degree lower-bound certificate if exact degrees are claimed. It should separately label finite evaluations as implementation evidence and the inherited theorem as the source of unbounded correctness.

### Emitted-degree audit addendum

After the ten complete JSON circuits were emitted, `check_degree_certificate.py` independently recomputed every formal-degree/top-coefficient row directly from their literal gate lists. All ten passed; the authenticated circuit hashes and results are in `degree_crosscheck.json`. No candidate emitter or upstream Python source was imported or executed. Both native/spatial and phase-four incdec circuits have exact total degree 2344, with specialized leading coefficient 135347 modulo 1000003. Each of the other six nonempty circuits has exact total degree 1192, with coefficient 977370. Both separate zero-step circuits have exact degree 2, with coefficients 585225 and 418734 respectively. Thus these degrees are certified exact, not merely propagation bounds. This addendum does not replace the separately requested full source-composition/closure/liveness audit.

The new semantic checker was also inspected as source. Its separate arithmetic tests include unequal terminal payloads, coprime cofactors, initial halt, delayed stalls, a valid separated growing nonhalting prefix, and nonfresh-entry rejection. Its reported finite checks supplement rather than prove the corresponding all-input claims. In particular, bounded nonhalting prefixes are not evidence of an unbounded execution by themselves.

### Final theorem review

The completed `THEOREM.md` was read in full after emission. No substantive interface mismatch or overclaim was found. It explicitly distinguishes first hits from later recurrence, identifies the one/two-step nonuniversal fixture scope, states integer domains, treats initial halt separately, retains the native no-wrap argument, and gives the verified degree lower-bound certificates. Its identity Q=P(x,F,theta)+clean_residual² is valid as an identity of integer polynomials after the explicit y=F substitution; it does not assert equality of the original and new polynomial values with y independently free. The general composition remains conditional on the inherited raw-history and exact-clean-target theorems.

## 7. Stronger witness-fiber audit: every accepted nonempty fiber is infinite

**Confirmed.** Fix an accepted external pair (x,S) in one of the nonempty native/spatial or phase-four circuits. The deterministic first-halting source trace is fixed, and therefore its terminal payload F, positive native time theta, encoded endpoints n0,nf, finite transition count t>=1, and residue quotients q0,...,q_(t−1) are fixed. Determinism of these semantic data does not make the arithmetic witnesses unique.

For every dyadic integer h satisfying

   h > max(n0+nf+theta, q0,...,q_(t−1)),

set eta=h−n0−nf−theta>0, B=C h², P=B^t and J=1+B+...+B^(t−1). There are infinitely many such h. The fixed multiplier C is dyadic and at least the inherited old multiplier K, so B and P are dyadic and B>=K h. The old pretyping and digit bounds therefore continue to hold. Pack the fixed residue indicators, quotient digits and selected quotient digits in this new base B. Every zero packed word has shifted positive coordinate 1 and is allowed.

Let g denote the number of exceptional slope classes. The classes are disjoint, so sum Z_a<=W and W<=(h−1)J. The supplied global slack is exactly

   beta=P−J−(W+1)−sum_a(Z_a+1)
       =(B−2)J−W−sum_a Z_a−g
       >=(B−2h)J−g>0.

The last inequality follows already from B>=K h, K>=4, K>=m+1, g<=m−1, h>=3 and J>=1. Thus increasing h does not merely preserve a weak nonnegative slack: it produces a strictly positive supplied beta at every permitted height.

All selector, range and selected-class AND lanes hold literally for these packed words. Each lane coefficient is below P: selectors and class selectors are at most J; quotient and selected quotient words are at most (h−1)J<P; class masks are at most (B−1)J=P−1; and the range mask is (h−1)J<P. If ell=m+g+1 and v is the least power of two at least ell, the concatenated ports obey

   0<=H,M,A<P^ell<=P^v<Qnative=B P^v.

The scale Qnative is dyadic, and the actual padded words 16H+12, 16M+10, 16A+8 are strictly positive and below the prescribed dyadic native scale 16Qnative. These are the same prescribed-scale extension hypotheses used in the inherited residue-history completeness proof, §4. Its complete native theorem therefore supplies fresh positive native witnesses at each such scale. No old native tuple is assumed to remain valid when h changes.

The native packed clock is Ctau=sum_i tau_i B^i, while theta=sum_i tau_i is unchanged. Their difference is a nonnegative multiple of B−1, because each B^i−1 is. Hence

   clock_quotient_hat=1+(Ctau−theta)/(B−1)

is a positive integer at every selected height, including t=1 when it equals 1. Chronological transport holds for the actual path, the terminal payload F remains positive, and the clean comparison keeps the same fixed external S. Thus every permitted h extends to at least one complete positive zero.

Distinct h give distinct supplied height_slack=eta, so the resulting complete witness tuples are distinct even without making any claim about multiplicities internal to the native extension. Therefore each accepted nonempty external fiber contains infinitely many positive integer witnesses. This is stronger than saying uniqueness was not proved. It is compatible with a uniquely determined source trace and reverse lift, and it differs from the finite-horizon canonical forward-witness uniqueness theorem.

The separate zero-step circuits have no existential coordinates. At an accepted input/time pair their witness fiber consists only of the empty tuple, so this infinite-fiber conclusion explicitly excludes them. No uniform numerical materialization of the large native witnesses, or native-witness uniqueness at a fixed height, is asserted.
