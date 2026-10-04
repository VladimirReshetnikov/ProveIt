# Independent mathematical review of balanced selected-output extraction

**PASS on the corrected frozen companion.** The signed convolution and two-stage balanced extraction preserve the positive-zero projection onto the specified common non-extraction ports. The ordinary-input theorem, positive completeness and degree35,587 follow on the inherited valid fixed-program domain. No remaining mathematical correction is requested.

## Frozen objects and actual review scope

| Author artifact | SHA-256 |
|---|---|
| matrix193_balanced_output_scout.py | e567a5be0cb656dfc984aa86fb306584dd837b7c24568659af222c781266d76a |
| matrix193_balanced_output_scout.json | 63a4b6b269ba177603cbebec51848bc6fbcd3c04115bb3dbb367dd63a2f7c9bf |
| matrix193_balanced_output_scout.md | cfc892b2c7a577d2348c3583d968e04ab271f065003cc0bfa6316a9f05f3abde |

I read the complete author helper and companion as inert text, inspected the receipt's extraction coefficients and degree metadata, and authenticated all six predecessor pins against installed bytes. The packed-output predecessor proof and helper had also received my separate complete mathematical read. The present task does not duplicate the root/Pascal full-array reconstruction and cost audit.

The proof was initially read at MD8e84685b. Root identified an overstatement of the common-port projection, and the author corrected Section4 without changing Python or JSON. I read and authenticated the revised section before this review was frozen. The distinction and its concrete necessity are recorded below.

No author or predecessor Python was executed or imported for this review. I ran a fresh independent finite component enumeration, described in the last section. I did not rerun the enormous83-TILE fixture, evaluate a complete native Pell tuple, or produce a new arithmetic source.

## Bounds before and after native typing

The integer finalizer forces all twenty comparisons to vanish before any interpretation of extraction ports. The retained G-P unit, positive history/SWITCH ports, and two positive block slacks give the same pretyping bounds as the packed-output source. Splitting the selector polynomial into X, Y and SWITCH pieces is an all-value algebraic identity; H,M,Z,q and all native cuts are unchanged on common packing ports.

The native bootstrap and joined AND therefore remain available before a signed convolution is used. After the one-hot controller is recovered, each group selector is Boolean in the time radix B. Each shifted state digit lies in [0,2D-1], so subtracting c0=D-1 gives a selected signed digit in [-(D-1),D]. Summing over selected time positions proves

    |U_l| <= D*J < (B-1)J+1=P.

This is a bound on the absolute integer value of a signed word, obtained by the triangle inequality. It does not require the centered word to have ordinary nonnegative radix digits. Consequently

    Z_block-c0*S_block = sum_l U_l Q^l

is the required polynomial expansion even when its integer value is negative or borrowing occurs.

## Full low-tail bound and unique extraction

For either block, |a_l|<M, |U_l|<P and C>2Ml imply that every coefficient of the complete convolution has absolute value strictly below Q/2. Q is even, so each such integer coefficient has absolute value at most Q/2-1. For T=Q^(l-1), this proves the entire low-tail estimate

    |low| <= (Q/2-1)*(T-1)/(Q-1) < T/2.

The middle coefficient likewise satisfies |dot|<Q/2. The proof controls the full sum of lower powers; a coefficientwise bound alone without this geometric-sum step would not suffice.

The positive offset and slack equations give the open intervals (-T/2,T/2) and (-Q/2,Q/2). Two decompositions of the same product have low terms congruent modulo T and difference of absolute value less than T; hence their lows are equal. Division by T then gives middle terms congruent modulo Q with difference of absolute value less than Q, hence equal. The high integer is determined afterward, with no upper, lower, or sign restriction.

The open intervals omit the ambiguous half-radix residue. The strict convolution bounds prove that the genuine low and middle terms never reach those omitted endpoints. Thus positive offsets and complementary slacks always exist. Every signed high has positive representatives max(high,0)+1 and max(-high,0)+1; these are witness choices, not unpaid circuit operations.

## Positive maps, boundary cases and program scope

The corrected theorem preserves only the common **non-extraction** ports, including block hats and block slacks, native witnesses, history/edge data, height/global slacks, terminal fields, population quotient, SWITCH hats, ordinary input and fixed coefficients. It excludes all middle and word-sum extraction coordinates even if their textual names are reused.

This qualification is necessary. For an empty selected block the older nonnegative extraction has dot_slack=Q and low_slack=T, while the new balanced extraction has dot_slack=Q/2 and low_slack=T/2. Keeping those old slacks would fail the new equations. Root's correction now states the exact valid projection.

With the corrected retained-port set, all native cuts are identically equal, so native witnesses can be kept. Old zeros extend through the proved balanced decomposition. In the reverse direction, joined AND supplies the bounded nonnegative digits needed to reconstruct the old positive coefficient products and word-sum extraction. The signed high-pair offset is free, so this is an equality of projections, not a bijection or unique inverse.

For zero products the balanced low/middle offsets are the positive half-scales and high can be represented by (1,1). No LOAD at x=0 gives the unchanged population quotient1. A mandatory SWITCH ensures at least one physical edge; an empty TILE sequence introduces no new condition beyond the predecessor's endpoint equation. The existing chronology, typed SWITCH pre-state, LOAD growth k<D and population congruence still recover k=x.

The signed coefficient words and C depend only on the fixed matrix table. Context-SWITCH coefficients keep their original paid arithmetic and eight-port valid fixed-program recipe. Nothing in this argument grants universality to arbitrary coefficient assignments, chooses program constants as existential witnesses, or creates duration-dependent coefficient words. The construction remains above the universal84 bound.

## Degree check

The unchanged native packing functions preserve the inherited degree34,039, including the all-value main-norm cancellation. Independently of native zeros, a length-l selector pack has degree2l-1 and its centered block has degree2l. Its reversed coefficient polynomial has degree2l-2 when its first coefficient is nonzero. The leading product is a nonzero constant times

    -c0_top*S_last_top*Q_top^(2l-2),

of degree4l-2. Its right extraction side has degree at most2l+1. The supplied high ports and the positive-offset bounds therefore cannot cancel that leader.

I checked the actual receipt's four first-coefficient pairs. They are (-1,-1) and (0,-1) for the two diagnostic blocks, and (-4858854410439068855,30073112053762492651) and (-490,271) for the actual X and Y blocks. At least one leader is nonzero in every block. For the longest actual block l=194, the residual degree is774 versus right-side upper389. Real sum-of-squares noncancellation yields outer degree1,548, hence total35,587. The diagnostic has residual degree6, SOS degree12 and total1,363. This is a symbolic leading-form check and selected coefficient authentication, not an independent re-expansion of every saved source row.

## Fresh finite corroboration and limitations

A separate inline standard-library calculation enumerated all20,670 arbitrary coefficient arrays of lengths2l-1 for Q in {4,6,8}, l in {2,3}, and coefficient values strictly inside (-Q/2,Q/2). These need not come from a convolution, so they test the general balanced expansion lemma itself. Every entire low tail obeyed the strict bound; all positive offset/slack/high-pair constructions worked. Exhaustive testing of1,174,968 candidate low values, followed by all admissible middle values, found exactly the predicted decomposition. The cases included10,046 negative high quotients and six zero products.

These finite results corroborate the unrestricted inequalities and uniqueness proof; they do not replace that proof, establish native typing by experiment, or materialize any compiler history. The full-source ledgers2,462=1,124M+1,338A/150 witnesses and302/55 are the author's source claims, separately audited by root/Pascal. The present review supports their mathematical semantics and the exact degree argument on the stated valid compiler domain.
