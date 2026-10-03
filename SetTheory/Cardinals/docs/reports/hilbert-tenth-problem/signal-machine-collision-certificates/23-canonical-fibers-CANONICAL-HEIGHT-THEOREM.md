# Canonical dyadic outer height for unbounded clean-clock packets

## Result and boundary

**The proposed height canonicalization is valid, conditional on the same inherited complete native AND, residue-history, and clean-target theorems as the frozen base.** Adding one strictly positive integer coordinate κ and one affine comparison removes the known infinite family obtained by increasing the outer height. Every accepted nonempty external fiber has exactly one outer witness tuple. Its remaining full witness fiber is in coordinate-projection bijection with the complete **22-coordinate positive native AND-extension fiber** at fixed padded ports and scale.

This is not a proof that the native fiber is unique, finite, or infinite. No unique-fold or finite-fold theorem is claimed for the full packet. No positive Pell tuple is numerically constructed. The ordinary-input universal loader remains a separate unpaid obligation. Frozen Report21 and both frozen input packets are unchanged.

The fully emitted nonempty circuits have these counts for both native/spatial and phase4 models:

| Fixed fixture | Multiplications | Additions/subtractions | Complete operations | Positive witnesses | Comparisons | Exact total degree |
|---|---:|---:|---:|---:|---:|---:|
| INC2;DEC2 | 240 | 368 | 608 | 61 | 21 | 2344 |
| ZERO3 | 185 | 298 | 483 | 59 | 21 | 1192 |
| NOP | 183 | 298 | 481 | 59 | 21 | 1192 |
| POSITIVE3 | 190 | 294 | 484 | 59 | 21 | 1192 |

All counts include the entire inherited native block, affine input and final-payload ports, original chronological and native-clock equations, folded five-gate clean-clock bridge, added height comparison, and complete 62-gate final sum of squares. They are counts of the emitted DAGs, not just deltas. The two separate initially halted circuits are unchanged: four operations, no witnesses, degree two.

## 1. Fixed-source scope and precise statement

Let R be a fixed deterministic, reversible separated source over INC2, INC3, positive DEC2, positive DEC3, ZERO2, ZERO3, POSITIVE2, POSITIVE3 and NOP. Its initial control q₀ has no incoming instruction and its designated halt qₕ has no outgoing instruction. First suppose q₀≠qₕ. The source uses positive raw payload N, initially N₀=x+1 for external x∈ℕ (including zero). Disabled guards are nonfinal stuck states. Eligible sources are those for which the inherited separated-source clean wrapper and complete raw residue-history interface apply; no universal source or ability to add a fresh entry to an arbitrary reversible program is assumed.

Assign control codes in {1,…,K}, with a rejecting trap, and encode configurations as

    n = K(N−1)+q,       m=6K.

Every missing guard, original halt, trap, or unused label transitions to the trap with unchanged payload; the trap never exits. A nonempty orbit ending at the original halt therefore describes its first genuine halt. The fixed residue-affine table has the form

    f(mz+r)=aᵣz+dᵣ,   1≤r≤m, z≥0, aᵣ≥0, dᵣ≥1.

The inherited packet supplies positive η, β, all m selector hats, one quotient-word hat, g selected-quotient hats for exceptional slope classes, the positive terminal raw payload F, a shifted clock quotient, and 22 positive native coordinates. The clean composition adds positive θ, the forward native physical clock. Its computed height and radix are

    S=n_initial+n_target+θ,
    h=S+η,
    B=C h²,

where n_initial=Kx+q₀, n_target=K(F−1)+qₕ, and C is the fixed dyadic constant at least the inherited radix multiplier L and 2384m+2. Here L≥max(4,m+1,1+maxᵣ(aᵣ+dᵣ)) is dyadic. C=131072, K=5 and m=30 in the four emitted fixtures.

Let Q_R(x,U;w) be the corresponding five-gate folded complete clean-clock construction, with w all its positive auxiliaries. The frozen folding packet contains the four literal instantiations tabulated above; it does not contain a literal circuit for every eligible R. Introduce κ∈ℤ₊ and define

    Q_R^can(x,U;w,κ)
      = Q_R(x,U;w) + [η+κ−S−1]².                    (1)

This is an identity of integer polynomials once S is replaced by its displayed affine expression. Its runtime circuit does not compute a logarithm, search for a dyadic height, or perform exponentiation.

**Projection theorem.** For all natural x,U, Q_R^can has a strictly positive integer auxiliary tuple if and only if the clean CA for R first reaches its exact cleaned target at time U. In the native/spatial model,

    U = 2θ + 192(F+x+1) + 16.

For the phase4 model the right side is multiplied by four. At every positive zero,

    h = the least power of two strictly greater than S.

The target is the same exact whole finite configuration as in the inherited clean theorem: restored full raw payload and absolute marker/controller geometry, including the cofactor coprime to six. Native and spatial-block clocks agree; phase4 has phase-zero target and four times the native clock. This is a first-hit relation, not arbitrary later target recurrence or stationary halting.

## 2. Why the least admissible dyadic height already bounds every quotient

For an encoded current configuration n=K(N−1)+q with 1≤q≤K,

    floor((n−1)/(6K)) = floor((N−1)/6).             (2)

To verify this, write N−1=6a+b with 0≤b≤5; then
n−1=6Ka+Kb+q−1 with remainder in [0,6K−1]. Thus the inherited residue quotient is below N.

The literal native instruction times as functions of the current payload are:

| Instruction | Native duration τ |
|---|---:|
| INC2 | 300N+8 |
| INC3 | 396N+8 |
| DEC2, when enabled | 150N+8 |
| DEC3, when enabled | 132N+8 |
| ZERO, POSITIVE, NOP | 192N+8 |

Consequently every genuine current state in a nonempty first-halting trace has

    z_i=floor((N_i−1)/6) < N_i ≤ τ_i ≤ θ.          (3)

The weaker uniform bound τ_i≥132N_i+8 suffices. No monotonicity of the payload or endpoint-bound assumption is used. In particular, transient growth beyond both endpoints causes no obstruction: the genuine elapsed native clock pays for the current payload at each step.

Therefore every h>S=n_initial+n_target+θ already exceeds every genuine residue quotient. This closes precisely the extra completeness obligation that selecting the least endpoint-and-clock height might otherwise have violated. It is special to the physical-clock packet; it is not a theorem for an arbitrary endpoint-only residue-affine orbit encoding.

## 3. The dyadic interval lemma, with both boundaries paid

With η,κ positive integers, h=S+η and η+κ=S+1 are equivalent to

    S<h≤2S,
    η=h−S,
    κ=2S+1−h.                                    (4)

The left inequality uses η≥1. The right uses κ≥1, not κ≥0. For every positive integer S there is exactly one power of two in (S,2S], namely the least power of two strictly above S. If S itself is a power of two, the selected h is 2S, with η=S and κ=1. Choosing h=S would force η=0 and violate the original positive domain. A larger dyadic height is greater than 2S and makes κ≤0; a smaller one is at most S and makes η≤0.

The original native theorem forces B and P to be powers of two. Since C is dyadic and h is a positive integer, B=C h² being dyadic forces h dyadic as well: any odd prime divisor of h would divide B. Thus the new comparison does not presume dyadicity independently of the retained native guards. Positivity alone without the native theorem would leave many integer heights in (S,2S].

## 4. Soundness, chronology, and unchanged no-wrap proof

A positive integer zero of (1) annihilates every old residual and the new height residual. The original clean-clock projection therefore supplies the unique actual first-halting source trace, terminal raw payload F and exact positive native clock θ. Equation (4) and native dyadicity then force canonical h. No old zero-set condition has been deleted.

For clarity, the exact-clock implication still has its original noncircular proof. Before typing digits, the inherited global equation forces J≥1, P≥B and all lane coefficients into [0,P). The sixteen complete native comparisons establish a genuine packed AND and dyadic B,P. The relation

    P−1=(B−1)J

then forces P=B^t and J=1+B+⋯+B^(t−1) for some integer t≥1. The selector lanes and sum of selectors type one residue per time. The range mask (h−1)J gives 0≤z_i<h. The retained transport row gives the consecutive deterministic orbit from n_initial to n_target, with all current values in [1,mh]. The rejecting totalization means this is a first halt, with no earlier rejection or earlier halt.

No current encoded state can repeat before a deterministic first halt. Hence t≤mh. Current raw payloads obey N_i≤6h and all genuine branch durations obey

    0<τ_i≤396N_i+8≤2384h.

It follows that

    Στ_i≤2384m h²<C h²−1=B−1.

Independently 0<θ<h<B−1. The retained paid clock equation

    Cτ=(B−1)(clock_quotient_hat−1)+θ

and its typed clock-word digits give Στ_i≡θ modulo B−1. Both integers lie in [0,B−2], so θ=Στ_i. The new height row is only an extra restriction; it does not replace this argument with a checksum. The two old outer rows, all sixteen native rows, physical-clock row and clean-time row remain unchanged as residual polynomials.

This no-wrap argument uses first-halting totalization and does not assert a bound for arbitrary endpoints permitting loops or posthalt continuation.

## 5. Completeness at exactly the canonical height

Suppose the cleaned CA has its specified first target at U. By the inherited clean-target theorem this comes from the genuine nonempty first-halting R trace

    (q₀,N₀),…,(qₕ,F)

of t≥1 instructions, with θ=Στ_i>0 and the appropriate native/phase clean time. Form S from its fixed encoded endpoints and θ. Select the unique dyadic h in (S,2S], and set η=h−S>0 and κ=2S+1−h>0. Equation (3) ensures every residue quotient is below h. Set B=C h², P=B^t and J=Σ_(i<t)B^i, then pack the actual chronological residue choices, quotient digits and selected quotient digits.

Write E_r for the packed selector words, W for the quotient word, and Z_a for each exceptional selected-quotient word. Their supplied hats are E_r+1,W+1,Z_a+1, so zero quotient words and unused classes are fully allowed. Distinct exceptional slope classes are disjoint, giving

    Σ_a Z_a≤W≤(h−1)J.

The original global comparison fixes its positive slack exactly as

    β=P−J−(W+1)−Σ_a(Z_a+1)
     =(B−2)J−W−Σ_a Z_a−g
     ≥(B−2h)J−g
     ≥(L−2)hJ−g>0.                               (5)

Here B=C h²≥Lh, L≥4, L≥m+1, g≤m−1, h≥3 and J≥1. In the present nonempty physical setting S is in fact much larger, but no stronger lower bound is needed.

Every scalar AND lane coefficient lies in [0,P): selectors and class selector sums are at most J, W and every Z_a are at most (h−1)J<P, class masks are at most (B−1)J=P−1, and the range mask is (h−1)J<P. Let ℓ=m+g+1 be the number of lanes and v the least power of two at least ℓ. With joined words H,M,A,

    0≤H,M,A<P^ℓ≤P^v<Q_native=B P^v.

All their AND lanes hold literally. The four prescribed native inputs after padding are

    16H+12, 16M+10, 16A+8, 16Q_native.

They are strictly positive, their first three entries are below 16Q_native, the prescribed scale is dyadic, and the padded AND holds (12 AND 10=8). These are precisely the inherited prescribed-scale native-completeness hypotheses. That theorem supplies fresh positive values for all 22 native coordinates at this exact scale. It is not necessary or valid to reuse an old native tuple from another height.

Chronological transport holds for the actual path. The packed clock Cτ=Στ_i B^i satisfies

    clock_quotient_hat=1+(Cτ−θ)/(B−1) ∈ ℤ₊,       (6)

because each B^i−1 is a nonnegative multiple of B−1. For t=1 this hat is exactly one. The clean-time equality holds by construction and (4) supplies the new row. All 21 comparisons therefore vanish. Completeness holds at the exact canonical height, not merely at some sufficiently large unspecified dyadic height.

## 6. Exactly what becomes canonical

Fix an accepted pair (x,U) and its clock model. Determinism and first-halt semantics fix the entire finite source trace. In order:

1. The trace fixes t, F, θ, every state/payload/residue/quotient, and the encoded endpoints
2. These fix S, the least dyadic h>S, η=h−S and κ=2S+1−h
3. They fix B=C h², P=B^t, J=ΣB^i, each E_r, W, each Z_a and every corresponding positive hat
4. Equation (5) fixes β and equation (6) fixes the positive clock quotient hat
5. They fix every outer arithmetic register, joined word, padded native port and prescribed scale

Thus **all supplied nonnative coordinates** are uniquely determined. For these literal fixtures there are 39 such coordinates for INC2;DEC2 and 37 for each other fixture; the remaining 22 are native coordinates. B,P,J,h and S are derived registers, not extra supplied coordinates. Positive F remains explicitly supplied and unique on the accepted fiber; it is not removed or replaced by an uncharged extraction.

Let o(x,U) denote that unique outer supplied tuple. Let a(x,U), b(x,U), c(x,U), q(x,U) be the four fixed padded native ports just described. Define E(a,b,c,q)⊆ℤ₊²² to be the set of **all** positive solutions of the inherited complete sixteen-comparison native AND block at these ports and scale, with the identical coordinate order used in these circuits.

Then the coordinate projection

    π : { (w,κ)>0 : Q_R^can(x,U;w,κ)=0 }
        → E(a(x,U),b(x,U),c(x,U),q(x,U))

that retains the 22 native coordinates is a bijection. Injectivity follows because the other supplied coordinates are all o(x,U). Surjectivity is stronger than merely knowing that some native extension exists: each of the five nonnative comparisons depends only on outer coordinates; fixing o makes all five vanish. The other sixteen comparisons are exactly the native block at the fixed ports. Therefore **every** positive tuple in E extends by the same o to a complete canonical zero.

The 22 retained coordinates are native__F0, native__F1, native__F2, native__a, native__c, native__d, native__f, native__h, native__i, native__j, native__k, native__o, native__r, native__s, native__w, native__tau, native__eta, native__zeta, native__ga, native__y_aux, native__odd_half, native__bound_beta. Their names do not imply they are all independent or all variable on a particular fiber. Some may be forced by the native equations; this result does not analyze that multiplicity.

This is a **fiberwise** statement at each fixed accepted external pair. The inverse map within such a fiber merely inserts the fixed outer tuple. It is not an all-input polynomial algorithm for finding a first-halting trace, a least dyadic ceiling, packed words, or native ports. Nor is it an all-tuple polynomial coordinate change carrying the old infinite fiber onto the new one. The new polynomial has an extra square and a genuinely smaller projected outer zero set; only its old-polynomial portion is unchanged identically. Without a separate native cardinality theorem, full witness finiteness and uniqueness remain unresolved.

## 7. Literal circuit construction and all-tuple identity

The folded frozen DAG does **not** already contain S. It computes

    d = n_initial+n_target
    old_mid = d+η
    h = old_mid+θ.

In every one of the eight actual frozen DAGs, old_mid is named bridge_height_without_time and has exactly one consumer: the h-producing addition. It occurs in no comparison. The new complete DAG therefore replaces those last two additions by

    canonical_endpoint_clock_sum = d+θ
    h = canonical_endpoint_clock_sum+η.

These two-gate schedules have identical h over every integer tuple. Since the deleted intermediate had no other consumer, every other old register and all twenty old residuals have identical polynomials. This is checked against the literal graph for each fixture/model, not presumed from naming.

After the unchanged five-gate folded clean-clock bridge, two new paid additions compute

    canonical_slack_sum = η+κ
    canonical_sum_plus_one = S+1.

The complete finalizer is rebuilt from all 21 comparison pairs: 21 residual subtractions, 21 self-products and 20 accumulation additions, a total of 21M+41A=62 operations. The old finalizer had 20M+39A=59 operations. Thus the **complete** increase from the five-gate folded parent is 1M+4A and one positive coordinate. No S producer is free; its old two-addition allocation was validly reassociated. Keeping the old core literally without that reassociation would require another producer addition for S, a different schedule.

The resulting entire polynomial obeys the all-tuple identity (1), including on arbitrary signed integer assignments and away from every old zero. The phase4 bridge stays the five-gate formula 768(F+x)+8θ+832, while native stays 192(F+x)+2θ+208. The new canonical condition uses the forward native θ in both models, not U or U/4. The old natural ports x,U and all old positive coordinates retain their order; κ is appended.

The exact degrees are certified directly on each new complete source. Substitute coordinate i in ordered parameters+auxiliaries by (i+2)z and propagate formal degree bounds and coefficients at those bounds modulo 1000003, never lowering a bound when its top coefficient vanishes. The old coordinate weights are unchanged because κ is appended. The new square has degree two, and the reassociation preserves all old residual polynomials. Output coefficients at degree 2344 (INC2;DEC2) and 1192 (the other fixtures) are respectively 135347 and 977370, both nonzero. This gives a degree lower bound matching the propagated upper bound. The independent circuit audit also computes complete univariate specializations. Degrees are exact for these emitted polynomials, not intrinsic lower bounds on every representation or optimal circuit counts.

## 8. Boundary cases and exclusions

- **Initially halted source.** If q₀=qₕ under fresh-entry/terminal-halt assumptions, that control is isolated. θ=0 and F=x+1. The cleaned run is just its two bridges: U=384x+400 native, U=1536x+1600 phase4. The separate four-gate, no-witness SOS circuits are copied byte-identically from the frozen base. They have the empty witness tuple on accepted pairs. The positive-θ nonempty packet, κ and the 22-coordinate fiber theorem do not apply to this case
- **Nonhalting or stuck source.** Its raw totalization never first reaches qₕ; the frozen packet has no positive zero, so adding a square cannot introduce one. The clean wrapper does not enter its backward half or reach H. A bounded simulation prefix alone is not a nontermination proof
- **Zero quotient words.** They are encoded by positive hat one and are permitted. A one-step history has clock quotient hat one as well
- **Wrong requested time.** The unchanged exact native-clock and clean-time comparisons reject it. In phase4, first-hit times are exactly four times native; a natural U not divisible by four cannot satisfy the phase4 clean comparison
- **S at a dyadic boundary.** Strictly greater means h=2S, never h=S. The right endpoint 2S is included because κ=1 is positive
- **Integer domains.** The equivalences require natural external ports and strictly positive integer witnesses. No rational, real, unrestricted signed, or arbitrary-microscopic-state reachability theorem follows
- **Universality.** Raw x+1 still carries its coprime-to-six cofactor and is not a paid arbitrary ordinary-input/program loader. No finite-fold MRDP statement, new universal operation bound, or complete numerical Pell witness construction is made

## 9. Inputs and reproducibility

The unchanged base manifest is pinned by SHA-256

    1bf1225aa950ad1d4f842c8bf098e1935925cd1d52c90453b7696c1321648f95

and the unchanged folded manifest by

    774a4498984ebccf8216897e21bf597084e70b148557ba4fa12b597bba44ba91.

Selected authenticated references are copied under reference/ for portable replay. Only arithmetic JSON/text data and inherited prose are consumed; no third-party Python is imported or executed. The own emitter and independent checkers use standard-library data processing. The proof of arbitrary trace completeness is mathematical and inherited-interface based; finite outer-history and signed/modular tests supplement it without pretending to construct positive native Pell witnesses.
