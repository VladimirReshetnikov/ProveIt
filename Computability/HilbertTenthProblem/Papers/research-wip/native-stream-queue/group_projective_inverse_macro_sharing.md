# Nonempty inverse macro tables in the complete projective compiler

The fixed inverse-closed table below has a proper, nonempty positive-input predicate. Four fully emitted one-kernel sources represent that same predicate. The original private macro controller costs **492=191M+301A**, and exact physical-word sharing reduces it to **432=178M+254A**. Changing to the equivalent Nielsen generators gives a better private-path source, **371=150M+221A**. Its inverse-folded bouquet costs **376=147M+229A** under the general weighted-flow schedule: fewer states save three multiplications but add eight additions. These are complete polynomial costs, including ordinary input, height, native arithmetic, all six comparisons and the finalizer.

This is a numerical fixed-table benchmark with an actual accepting positive input, rather than the [earlier empty-language fixture](group_projective_shared_macro_automaton.md). The table is not claimed universal; none of 492,432,371,376 is a universal operation bound. Computation duration remains existential and unbounded. The source does not impose an external time horizon.

[Source](group_projective_inverse_macro_sharing.py) and [receipt](group_projective_inverse_macro_sharing.json) form a standalone standard-library, authenticated CLI. It reads saved source and graph JSON, imports no historical modules and executes no historical builders or suites. All frozen predecessors remain unchanged.

## 1. Actual words, matrix action and ordinary-input language

Physical letters1,2 add/subtract the second coordinate to/from the first coordinate in the first block;3,4 add/subtract the first to/from the second. Letters5 through8 do the corresponding operations in the second block. Physical words act in chronological order, so their matrices multiply on the left. Define

    U = (1,5),
    R = (2,3,6,7),
    Bcode = U^5,
    Acode = R Bcode.

Their lengths are2,4,10,14 respectively. For a physical word w, inverse(w) reverses the letters and swaps1↔2,3↔4,5↔6,7↔8. The original four-code table is exactly

    Acode = (2,3,6,7,1,5,1,5,1,5,1,5,1,5),
    Bcode = (1,5,1,5,1,5,1,5,1,5),
    inverse(Acode) = (6,2,6,2,6,2,6,2,6,2,8,5,4,1),
    inverse(Bcode) = (6,2,6,2,6,2,6,2,6,2).

All eight physical letters occur. Each code acts equally on both two-dimensional blocks. On either block,

    U : (a,b) -> (a+b,b),
    R : (a,b) -> (a-b,a),
    Bcode = [[1,5],[0,1]],
    Acode = [[6,-1],[1,0]].

The actual paid ordinary-input prefix remains

    input_product = 24*x
    u = input_product + 13
    D = u + height_slack
    c0 = D - 1
    B = 16*D,

where x and height_slack are positive integers. Here B is the history radix, distinct from the macro Bcode. The target remains `(1,u,1,u) -> (0,1,0,1)`.

For every positive x congruent to2 modulo5, u is congruent to1 modulo5. Put e=(u−1)/5. Then the physical word

    Acode Bcode^(e−1) = R Bcode^e = R U^(u−1)

first takes `(1,u)` to `(1−u,1)` and then to `(0,1)`, in both blocks. In particular **x=2,u=61** has the accepted word `Acode Bcode^11`, of physical length124. A valid dyadic height is **D=128**, with positive slack67 and radix2048. The receipt also checks x=7,u=181, duration364 and D=256.

Conversely modulo5, Bcode is identity and Acode equals `M=[[1,-1],[1,0]]`. This matrix has order6. Its orbit of `(0,1)` is exactly

    (0,1), (4,0), (4,4), (0,4), (1,0), (1,1).

If a group word sends `(1,u)` to `(0,1)`, its inverse puts `(1,u)` in this orbit. Necessarily u is congruent to0 or1 modulo5, hence x is congruent to2 or3 modulo5. Thus **x=1,u=37 is rejected**. The sufficient progression and necessary residue condition establish a proper nonempty predicate. They are not asserted to be an exact classification of its language.

## 2. Four graphs and the distinct equivalences

The original private paths have48 nonidle edges and45 states including the distinguished hub0. The prefix-trie/equal-continuation construction from [macro sharing](group_macro_automaton_sharing.md) has30 edges and27 states. It preserves the exact physical word language `(Acode | Bcode | inverse(Acode) | inverse(Bcode))*`; a complete subset-state comparison visits37 pairs. The hub is distinguished throughout. A code that is a prefix of another code does not authorize merging a return to the hub with its continuing edge.

The Nielsen table is

    (R, Bcode, inverse(R), inverse(Bcode)).

It has28 private edges and25 states. Its matrix subgroup equals the original one: `Acode=R Bcode` and `R=Acode inverse(Bcode)`, with inverses included. This is matrix-subgroup equality, not equality of the literal physical word languages. It suffices for equality of the projective endpoint predicate.

The fourth graph is the literal frozen `core.edges` of [the inverse-controller packet](group_inverse_stallings_controller.md). It is the two-cycle inverse bouquet: a four-edge R cycle and a ten-edge Bcode cycle sharing only the hub, with their reverse labeled edges. It has28 directed edges and13 states. The helper independently checks inverse closure, deterministic labeled exits, the two simple disjoint-interior cycles, and that their two orientations account for every edge. Every hub loop reduces, by cancellation of an edge followed by its inverse, to a concatenation of these cycles and their inverses. Conversely both generators and their inverses are literal loops. Its matrix image is therefore the same subgroup. The imported packet proves how it arises from folding the original inverse-closed table.

All graphs have no identity edge or idle hat. The empty word cannot reach the required projective endpoint. Identity hub steps can be removed from an accepted computation without changing its action; a nonempty accepted physical word still has some positive, unbounded duration. The graph-equivalence statements use fresh history/native witnesses. They do not claim a cross-graph positive-zero bijection or a cross-graph polynomial identity.

## 3. Actual complete source and padding changes

The source starts with the authenticated complete saved `source_example` in [label-aligned lanes](group_projective_label_aligned_lanes.md), whose original m8 template includes every physical label and the full seventeen-gate finalizer. It regenerates all graph-dependent instructions and retains the actual native/history instructions. The [product-radix scale](group_projective_product_radix_scale.md) uses top mask2; the [tail quotient](group_projective_tail_quotient_shift.md) uses `X=q*(w+(q−1)F3)`. This packet makes no top-mask1 change and no direct-height projection.

For n nonidle edges set m to the least power of two at least max(8,n). Thus the original private source has **m64** and the other three have **m32**. Every state code is less than the corresponding m. Each emitted controller lane map is injective into0 throughm−1. Unused padded lanes are literal zeros, not extra supplied hats.

For E_e=Ehat_e−1 the exact regenerated scalar ports are

    J = sum_e E_e,
    dS_i = sum_(label=2i+1) E_e − sum_(label=2i+2) E_e,
    S = sum_e E_e P^(label_e−1),
    C = sum_e E_e P^(position_e),
    flow_left = sum_e source_e E_e,
    flow_right = B*sum_e target_e E_e,
    P = (B−1)*J+1.

All positive hats, fixed coefficient products and bias corrections are paid. Private and Nielsen-private sources use the checked private-path checksum identity: every internal state has one incoming and one outgoing edge, and consecutive internal state labels permit its shared sum. The shared and inverse-bouquet graphs use the general weighted flow equation; no incidence-one formula is applied to them.

Padding changes more than a ledger field. The actual source pays all powers and repunits and uses

    origin_mask = J*(1+P+...+P^(m−1)),
    T = P^(m+8),
    T2 = P^(2m+8),
    q = 32*B*T2.

The three respective producers `controller__origin_mask`, `joint_scale` and `range_body_scale` are changed literally. The m64 exponent is136 and the m32 exponent is72. The history range mask reuses all m controller lanes, while the histories themselves occupy the eight physical lanes. No m8 template exponent or range mask is silently retained.

Sparse Horner evaluation, repunit decompositions, and exact repeated gates are charged in the source. The inverse-closed tables permit a small paid hatted-selector bias: if physical counts are `(c,c,1,1,d,d,1,1)`, its exact polynomial is

    (P+1)*((P^4+1)*(P^2+d)+(c−d)).

The helper proves this as part of the full scalar S identity, together with all offsets and powers. The complete circuit receives no uncharged AND, variable exponentiation, matrix multiplication or sequence primitive.

For each graph, five explicitly specified lane maps are tested: consecutive order; label-group order in each of two edge orders; and physical-label layers with deterministic overflow in those same two orders. Each is paired with direct hatted Horner packing, per-edge correction to S, or grouped-offset correction to S. These are60 literal schedules, not all permutations or arbitrary arithmetic circuits. The receipt includes each complete source hash and ledger and saves the four winning arrays; all four winners use direct packing.

## 4. Positive compiler theorem with the actual margin

For any one of the four graphs and every x>0, a positive zero exists exactly when some graph hub loop has the specified paired endpoint. The theorem is at the existential ordinary-input level and retains all current native conditions.

The full output is literally

    U*(1+R0²+R1²+R2²+R3²+Rflow²)−1,

where U is the product of the six native factors and the joint bound factor. At a positive integer zero the five outer residuals vanish and each factor is a sign. For either sign of the joint factor `G−P`, the positive histories, selected-source hats and global slack give P≥12, H_i<P and Zhat_i−1<P. The hats give E_e≥0. Then `P=(B−1)J+1` forces J≥1 and B≤P before any radix typing.

The actual fixed radix margin is unconditional:

    x≥1 => u≥37 => D≥38 => B=16D≥608>64≥m.

The older sufficient program-data guard `alpha+beta+1≥m` does not hold for m64, since37<64. It is not assumed here. The source needs the actual B>m inequality, supplied directly by the retained factor16 and the height prefix. All state digits are also below B. This replaces a sufficient syntactic guard with its proved underlying inequality; it does not erase a residual or weaken the radix margin.

Each E_e≤J, and each physical selector sum is at most J. Thus C≤J R_m(P)<P^m, while the physical mask coefficients `(B−1)S_i` and the range coefficients `(2D−1)J` are below P. The physical, controller and range regions are disjoint. Writing the joined interface as

    H=H0+B*T2,  M=M0+2*T2,  Z=Z0,

one has `0≤H0,M0,Z0<T2` before typing. The four reconstructed truth fields

    F0=16(2B*T2−H−M+Z)−15,
    F1=16(H−Z)+4,
    F2=16(M−Z)+2,
    F3=16Z+8

are strictly positive, sum to q−1, and have residues1,4,2,8 modulo16. For example the three relevant differences are at least `(B−4)T2+2`, `(B−1)T2+1`, and `T2+1`. These scalar inequalities depend on padding and positivity, not on disjoint paths or a prior matrix interpretation.

The [tail-quotient bootstrap](group_projective_tail_quotient_shift.md#3-native-recovery-including-both-index-signs) therefore applies unchanged. It recovers native signs, the exact native exponent and positive old quotient without assuming the old X>r prematurely. It restores all native factors to1 and hence the joint bound to1. The positive product identity `q=32B*P^(2m+8)` forces B and P to be dyadic; the repunit relation gives `P=B^t` at some t≥1. Separating the joined AND gives the original physical selection, controller Boolean and history range conditions. The top block is valid because dyadic B has B AND2=0.

Every E_e is now a Boolean radix-B word. Their sum J has digit1 at each time; since n≤m<B there is no carry and exactly one edge is selected per step. State digits are below B, so `sum_e source_e E_e = B*sum_e target_e E_e` enforces source0 at the low end, target0 at the high end, and matching target/source at consecutive times. The remaining selected-source/range constraints and four unchanged signed transports recover the genuine matrix trajectory. The retained D>u prevents input wrapping. This proves soundness for arbitrary branching in the two graphs where it occurs.

Conversely any accepted nonempty hub word has a finite trajectory. Choose a sufficiently large dyadic D greater than u and one plus every absolute coordinate, and set the positive height slack, B=16D, P=B^t, the true repunit and all chronological edge/history/selected-source words. Increasing D supplies the positive global slack. The true joined AND holds at the paid product scale. The prescribed native converse and tail-coordinate theorem supply fresh positive native witnesses. All six comparisons and the finalizer vanish. No duration bound is imposed. Combining this compiler theorem with Section2 gives the same full positive-input predicate for all four sources.

## 5. Complete paid ledgers and exact degrees

| Saved full source | Nonidle edges / states / lanes | Certificate | Full polynomial | Positive witnesses | Comparisons | Exact degree |
|---|---:|---:|---:|---:|---:|---:|
| Original private |48 /45 /64|475=185M+290A|492=191M+301A|74|6|9069|
| Exact-language shared |30 /27 /32|415=172M+243A|432=178M+254A|56|6|4909|
| Nielsen private |28 /25 /32|354=144M+210A|371=150M+221A|54|6|4909|
| Inverse bouquet |28 /13 /32|359=141M+218A|376=147M+229A|54|6|4909|

The finalizer costs17=6M+11A in every case: five subtractions, five squares, four sum additions, addition of1, multiplication by U and subtraction of1. Every supplied coordinate and every paid gate reaches the full output. The best operation count in this stated family is371. The bouquet's lower multiplication count is also recorded; minimizing the state count is not the same objective as minimizing total arithmetic.

The exact-degree calculation uses all supplied coordinates, including x, at degree1 and fixed compiler numerals at degree0. The naive upper bounds are9343 and5055. At the literal guarded main norm it instead uses the ring identity

    (X+ac+gamma)^2−(a²+4a+3)c²
      =X²+2Xac+2Xgamma+2acgamma+gamma²−(4a+3)c².

Every producer of that cone is checked. No equation valid only at zeros is used to reduce degree. In the inherited notation `nu=2`, `a_scale=2m+8`, the full degree is

    73 + 2*(29*a_scale + 7*m + 106).

For m64, the seven factor degrees in order first, main, auxiliary, index, linear, strong, joint are

    1255,2234,1652,980,980,1960,2.

For m32 they are

    679,1210,884,532,532,1064,2.

The outer sum contributes degree6. The formula yields9069 and4909. Notice `deg F3=1+2(m+15)`, independent of a_scale; it is not `deg(q)−2` for these reused-range layouts.

For every one of the60 actual schedules, a recorded positive integer weight substitutes each free coordinate by that weight times an indeterminate. Exact top-coefficient propagation modulo1000000007, after the proved main cancellation, gives a nonzero coefficient at the claimed full degree. Hence the guarded upper bound is attained by the actual fixed-numeral polynomial. This is a coefficient certificate, not a conclusion from numerical value samples.

## 6. Reproducible evidence and limits

The writer checks720 exact coefficient polynomials for the twelve complete graph/scale ports, then11100 retained-register expressions, all360 comparison expressions and every whole output across the60 schedules. It recounts all28436 paid live gates and certifies all60 exact degrees. The four saved complete winners additionally undergo24 full signed/rational evaluations, including8 rational cases, with their literal finalizers. These algebraic checks assert no rational-domain compiler theorem.

The eight genuine accepting outer fixtures use x2 and x7 in each graph. They verify the actual physical endpoint, positive height/hats/global slack, chronological controller, all five outer residuals, the full joined AND, exact q scale and all four positive native truth fields. The x2 word has124 physical steps and D128. **No huge native Pell zero is materialized.** The positive extension of these outer fixtures is supplied by the inherited theorem. The full positive-input equivalence is proved for arbitrary accepted duration, not inferred from these fixtures.

Exact ring-polynomial identities are asserted for the regenerated ports and their complete static-source interface. Different lane assignments and different graphs generally change the packed native fields, so their whole polynomials need not agree; fresh witnesses establish the represented-language statements. The input predicate is proper and nonempty, but no numerical universal alphabet, global arithmetic optimum, graph-independent operation bound, zero-fiber bijection across graphs, or improved height projection is claimed.

Run from any working directory:

    python3 group_projective_inverse_macro_sharing.py --root /absolute/path/to/native-stream-queue --expect /absolute/path/to/group_projective_inverse_macro_sharing.json

Use `--output` to write the deterministic receipt. Authentication prefers the supplied root and uses a sibling file only when that exact relative file is absent from the root; existing wrong-pin files never fall through. All parent pins are checked on every CLI run. This is a bounded pinned source/proof CLI, not a maintained general public compiler API.
