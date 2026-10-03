# A fully paid bounded-word Diophantine interface

Authored 2026-10-03. This packet concerns one fixed numerical matrix semigroup. It is a new sibling of, and makes no changes to, the source matrix construction. Its only computational source dependencies are the copied literal JSON data and a saved witness. No upstream Python is imported or executed.

## 1. Fixed matrices, exact statement, and domains

`data/semigroup.json` is byte-for-byte the numerical source with SHA-256

    506144b361b2bea634d468a94921644d91868dc089a257fe289a0bf51b74cec9

It lists 114 matrices A_i, 114 matrices B_i, and C, in that order, all in SL_4(Z). Let U_i be the upper 2x2 block of A_i; let V_i be the inverse of the **whole** upper 2x2 block of B_i. These are fixed integral determinant-one matrices. Let

    D = C_top = [[157,4],[-6712,-171]],
    P = [[1,2],[0,1]].

Fix a numerical integer r >= 0. The external parameter T=(t_ab) is an arbitrary 2x2 matrix over Z: four signed integer slots. The compiler emits an integer polynomial

    F_r(T; x),    x in N^(130r),    N = {0,1,2,...}.

Its zero fiber is in explicit bijection with the tile-index sequences (i_1,...,i_r) in {1,...,114}^r for which

    A_(i_1)...A_(i_r) C B_(i_r)...B_(i_1) = diag(T,P).       (1)

The exact counts are 130r natural auxiliary variables and 17r+4 squared residuals. The total degree jointly in external and auxiliary variables, before specializing external inputs, is 2 for r=0, and exactly 4 for every r>=1. After fixing a particular T at r=0, the auxiliary-free polynomial is of course constant. There are no hidden selector Booleanity variables, signed quotients, arithmetic-gate witnesses, determinant witnesses, or exponentiation variables.

The source marker lemma says every positive generator word with lower block P has precisely the form in (1). Consequently this interface expresses factorization of diag(T,P) at the **exact generator length 2r+1**. For the source semigroup S,

    diag(T,P) in S  iff  there is an r>=0 and x in N^(130r)
                                with F_r(T;x)=0.

This last statement is a union of polynomial families, not a claim that variable r is encoded by this same fixed-arity polynomial. An upper bound on word length can be handled by the finite disjunction of the separate r instances up to that bound; no uncharged fixed-arity selector for that disjunction is claimed here.

## 2. Why the lower marker is an exact constraint

For clarity, the algebraic fact used from the source construction is recalled here. Put

    E_j = [[1+4j,2],[-8j^2,1-4j]],   t=E_0=P,   x_i=E_i.

The numerical lower blocks are x_i, t^(-1)x_i^(-1)t, and t for A_i, B_i, C respectively. This is checked directly by the independent literal-data audit. The matrices t,x_1,...,x_114 freely generate: E_j=Q^(-j)P Q^j for Q=[[1,0],[2,1]], and P,Q freely generate by ping-pong on |z|<1 and |z|>1 in the real projective line. Expanding a nonempty reduced product of distinct conjugates leaves a nonempty reduced P,Q word.

The t-exponent sum in a positive A/B/C word is its number of C occurrences. Lower block t forces exactly one C. The kernel of t-exponent sum has free basis y_(i,h)=t^h x_i t^(-h). Before C, A contributes y_(i,0), and B contributes y_(i,-1)^(-1); after C, A contributes y_(i,1), and B contributes y_(i,0)^(-1). No positive inverse of any height -1 letter and no negative inverse of any height +1 letter occurs. Those letters therefore cannot disappear in free reduction. Thus there is no B before C and no A after C, and the remaining positive and negative height-0 words cancel exactly when their indices match in reverse order. The converse cancels immediately. This proves the marker assertion for arbitrary positive words, without a constrained-word oracle.

## 3. Every variable and every residual

For each step s=1,...,r, allocate:

* 114 natural selectors e_(s,i), i=1,...,114
* positive and negative natural parts h^+_(s,a,b), h^-_(s,a,b), g^+_(s,a,b), g^-_(s,a,b), a,b=0,1: 16 more variables

Use the abbreviations H_(s,a,b)=h^+_(s,a,b)-h^-_(s,a,b) and G_(s,a,b)=g^+_(s,a,b)-g^-_(s,a,b). These abbreviations are linear expressions, not additional variables. H_0=G_0=I_2 are literal constants, not allocated slots.

The residuals at step s are:

    S_s = sum_(i=1)^114 e_(s,i) - 1                          [1 residual]

    U^H_(s,a,b) = H_(s,a,b)
                  - sum_i e_(s,i) sum_(k=0)^1 H_(s-1,a,k) (U_i)_(k,b)
    U^G_(s,a,b) = G_(s,a,b)
                  - sum_i e_(s,i) sum_(k=0)^1 G_(s-1,a,k) (V_i)_(k,b)
                                                               [8 residuals]

    K^H_(s,a,b) = h^+_(s,a,b) h^-_(s,a,b)
    K^G_(s,a,b) = g^+_(s,a,b) g^-_(s,a,b)                        [8 residuals]

There are four terminal residuals:

    L_(a,b) = sum_(k=0)^1 H_(r,a,k) D_(k,b)
               - sum_(k=0)^1 t_(a,k) G_(r,k,b).              [4 residuals]

Finally, literally define

    F_r = sum_(s=1)^r (S_s^2
               + sum_(a,b) ((U^H_(s,a,b))^2+(U^G_(s,a,b))^2
                            +(K^H_(s,a,b))^2+(K^G_(s,a,b))^2))
                + sum_(a,b) L_(a,b)^2.

No inequality other than each quantified variable's N domain is needed. In particular S_s=0 alone forces exactly one selector equal to 1 and all others 0: nonnegative integers summing to 1 have that form. We do not claim this implication over signed integers or arbitrary reals.

## 4. Soundness, completeness, canonicity and multiplicity

A sum of squares of integers is zero if and only if every summand is zero. Thus a natural root determines exactly one tile choice i_s at each step. Each update equation then becomes ordinary right multiplication H_s=H_(s-1)U_(i_s), G_s=G_(s-1)V_(i_s). Inductively,

    H_r=U_(i_1)...U_(i_r),  G_r=V_(i_1)...V_(i_r).

For any signed integer z there is exactly one pair (p,n) in N^2 with p-n=z and pn=0: (max(z,0),max(-z,0)). For z=0, both parts are zero. This covers all sign and zero cases. Hence all 16 state parts at each step are forced uniquely by the sequence. The terminal equations say H_r D=T G_r. All G_r are unimodular, so this is equivalent to

    T=H_r D G_r^(-1).

The product on the right is the upper block of (1): the B factors appear in reverse sequence order, so their upper product is V_(i_r)^(-1)...V_(i_1)^(-1)=G_r^(-1). The lower block is P. This proves soundness.

Conversely, a sequence satisfying (1) gives one-hot selectors and the canonical positive/negative parts of each prefix H_s,G_s. Every residual vanishes. The preceding induction proves this is the **only complete auxiliary tuple for that specified sequence**. Reading the unique nonzero selector at every step gives the inverse map. Thus for every fixed external T,

    #{x in N^(130r): F_r(T;x)=0}
      = #{sequences of length r satisfying (1)} <= 114^r.

The count includes zero if there is no sequence. It is not a uniqueness assertion for target factorization. In fact the tests exhibit distinct length-two sequences with the same target. Nor does the per-r finite bound prove a finite number of witnesses after allowing all r; no unbounded finite-fold conclusion is made.

## 5. Zero length and invalid targets

At r=0, N^0 has its one empty tuple and H_0=G_0=I_2. There are no selectors, state parts, or complements. Explicitly,

    F_0(T) = (157-t_00)^2 + (4-t_01)^2
                       + (-6712-t_10)^2 + (-171-t_11)^2.

There is exactly one natural auxiliary solution, the empty tuple, precisely when T=D; otherwise there are none. The corresponding positive generator word is C, of length one. We are not replacing it by an empty semigroup product.

Every satisfying target has determinant one, because T=H_r D G_r^(-1) and every factor has determinant one. Therefore matrices with determinant different from one automatically have empty fibers; adding a determinant residual is unnecessary. Arbitrary signed T entries, including negative entries and zeros, remain valid inputs. Wrong T values give no root unless they are independently realized by another length-r sequence; a fixed sequence's certificate cannot certify a changed T because G_r is invertible.

The mathematical external domain is Z^4. A noninteger is not a point of that domain; the implementation rejects malformed shapes, booleans, floats, missing/extra assignment names, and negative auxiliaries. The full-4x4 helper accepts only the structural interface diag(T,P) and rejects wrong lower/off-diagonal blocks. This structural rejection is **not** a claim that every other 4x4 matrix fails membership in the original S, and is not an extra hidden polynomial constraint: the four external slots already parameterize exactly diag(T,P).

## 6. Optional all-natural external target interface

Replace each t_ab by t^+_ab-t^-_ab, using **eight external natural input slots**. Add the four residuals t^+_ab t^-_ab and square them along with the others. External slots are parameters, not extra quantified auxiliaries. There are still 130r auxiliaries; now there are 17r+8 residuals and total degree exactly 4 even when r=0.

For canonical external pairs the same bijection applies to their signed difference T. Noncanonical pairs have a strictly positive complement square and therefore no roots, even if their differences encode an otherwise valid target. Negative external parts are outside this interface's domain. There is no hidden identification of many external pairs with one valid canonical encoding. The optional variant is fully charged separately throughout the machine-readable ledgers.

## 7. Literal coefficients, degrees, and sparse-size counts

The authored loader verifies the pinned JSON, extracts U from A and V by an explicit determinant-one 2x2 inverse of B's whole upper block, and never executes the source compiler. All 456 U entries and all 456 V entries are nonzero. Their exact maximum absolute values are 63,038,000 and 11,924,776 respectively. The maximum absolute D entry is 6,712. Thus residual coefficients have absolute value at most 63,038,000 (26 magnitude bits), attained for r>=1. At r=0 the maximum is 6,712 (13 magnitude bits).

The first-step update residuals are linear because H_0=G_0=I_2. Later updates are bilinear in a selector and a previous state part. Canonicality residuals are quadratic. For signed T, the terminal residuals are bilinear for r>=1 and linear for r=0; for natural target pairs they remain quadratic for r>=1. Squaring gives degree at most four. For r>=1 the square of any state complement contributes a degree-four part; sums of real polynomial squares cannot cancel all nonzero top-degree parts. Thus the degree is exactly four. The analogous external complement proves the natural r=0 claim. The displayed F_0 proves signed r=0 degree exactly two.

The literal JSON format keeps the residuals as sparse polynomials and declares F to be the sum of their squares. This is an explicit integer polynomial representation, not a numerical oracle or a symbolic coefficient placeholder. Every coefficient, monomial, variable name and square is materialized for r=0,1,2 in `examples/`. Expanding the final squares is mathematically unnecessary and would obscure the accounting.

Let N_d be the number of degree-d monomial occurrences across residuals, with like monomials combined **within each residual**, not across different residual squares. In the signed interface:

    r=0: (N_0,N_1,N_2) = (4,4,0), R=4
    r>=1: (N_0,N_1,N_2) = (r,130r+928,3656r-3632), R=17r+4.

Derivation: each selection has one constant and 114 linear terms. Each of the eight first-step updates has 116 linear terms. Each later update has 2 linear and 456 quadratic terms. There are eight one-monomial complements per step. Each signed terminal has four linear and four quadratic terms for r>=1. All tile coefficients involved are nonzero, and distinct selector/entry indices prevent monomial mergers in these formulas. The total residual monomial count for r>=1 is 3787r-2704.

For the natural-target variant, at r=0 the triple is (4,8,4), R=8. For r>=1 the triple is (r,130r+928,3656r-3612), R=17r+8: replacing signed T doubles the terminal's 16 total quadratic terms and adds four external complement terms. The total becomes 3787r-2684.

Each later update has at most 458 monomials; no residual exceeds that size. If full SOS expansion is desired, its coefficients are integers bounded in absolute value by

    R * (458 * 63,038,000)^2.

This deliberately conservative bound follows from the l1 norm of each residual and submultiplicativity for squaring; it applies to both interfaces and all r. No expanding step is needed for verification. The bit length of that coefficient bound is O(log(r+1)).

## 8. Arithmetic resource charges and integer growth

The compiler's `ledger` reconstructs variable sets, monomial degrees, coefficient maxima and residual counts by traversing actual emitted polynomials, rather than copying these formulas. The generic sparse evaluator has an intentionally unoptimized arithmetic convention:

1. Start every monomial product at 1 and multiply once per variable occurrence
2. Multiply that product by its integer coefficient, even for coefficients 1 or -1
3. Add every monomial into a residual accumulator initially 0
4. Square each residual and add its square into an SOS accumulator initially 0

Thus multiplication count is N_1+2N_2+(N_0+N_1+N_2)+R, and addition count is N_0+N_1+N_2+R. For signed inputs these are respectively 16 and 12 at r=0; for r>=1 they are

    multiplications = 11246r-9036
    additions       = 3804r-2700.

For natural inputs, r=0 costs 40 multiplications and 24 additions; for r>=1 the signed counts increase by 64 multiplications and 24 additions. These are **this evaluator's** explicit scalar-integer arithmetic counts, not algebraic minimality claims. Parsing, hash checking, comparisons, variable lookup, loop control, validation, source loading and polynomial construction are separately excluded; all are finite ordinary implementation work. This is not, and does not inherit, any earlier 244-operation claim. For transparency, the fixed loader itself calls the 2x2 inverse routine 572 times (229 upper blocks, 229 lower blocks, and 114 extracted V blocks): 1,144 scalar multiplications, 572 subtractions and 1,144 negations, apart from hashing, parsing, shape/domain checks and control. The copied coefficient-source JSON occupies 117,288 bytes. Sparse-polynomial construction and symbolic name handling are charged by the output-size bounds below rather than by the evaluation census.

Let K_H=64,675,047 and K_G=12,234,453, the maximum absolute row-sum norms of the U and V matrices respectively. The literal audit verifies these numbers. They satisfy K_H<2^26 and K_G<2^24. At prefix s>=1,

    ||H_s||_infinity <= K_H^s < 2^(26s),
    ||G_s||_infinity <= K_G^s < 2^(24s).

Every canonical H part therefore needs at most 26s magnitude bits, and every G part at most 24s. In a canonical pair at most one part is nonzero, so all natural auxiliary slots together need at most

    100r(r+1)+r magnitude bits,

counting zero as zero bits and each selected one-hot 1 as one bit. This is a census of mathematical values, not a JSON file-size bound. With an ordinary minimum one-bit representation per slot there is an additional O(130r) charge. The maximum row-sum norm of D is 6,883<2^13. For 2x2 determinant-one G, ||G^(-1)||_infinity <= 2||G||_infinity. Hence each product target entry has at most 50r+14 magnitude bits. This is a safe upper bound, not a lower growth rate.

Certificate construction uses two 2x2 multiplications by fixed matrices per step: 16 fixed-integer multiplications and 8 additions, plus sign comparisons/canonical splitting and selector output. Its prefix arithmetic costs O(r^2) bit operations using elementary fixed-integer arithmetic and O(r) working bits when prefixes are streamed. Keeping the complete certificate costs O(r^2) value bits; explicit names/zero slots add O(r log(r+1)) textual overhead. If a target is supplied, copying/checking its encoding adds its bit length. Computing the default target also requires two terminal 2x2 products (16 scalar multiplications and 8 additions, eight multiplications having fixed D factors) and the determinant-one inverse check (2 multiplications, 1 subtraction, 2 negations and swaps). The first target product and prefix operations use fixed constants; the final product involves O(r)-bit values and costs O(r^2) with schoolbook multiplication. No target construction cost is hidden in the polynomial's auxiliary count.

For arbitrary assignments whose signed external entries and natural auxiliary entries have absolute values <2^B, B>=1, every residual has magnitude <2^(2B+35): at most 458 monomials, degree at most 2, coefficient magnitude <2^26. Thus the SOS has magnitude-bit length at most 4B+70+ceil(log2 R). The evaluator uses O(r+1) counted arithmetic operations on O(B+log(r+1)) bits, or O((r+1)(B+log(r+1))^2) schoolbook bit operations as a conservative upper bound. This accounts for coefficient/value growth; integer arithmetic is not treated as unit-cost in that bound. A streaming residual generator avoids storing an expanded SOS. The explicit polynomial compiler itself emits O(r+1) residual monomials (with the displayed large constants) and O((r+1)log(r+2)) variable-name characters. Its iteration count is linear in numerical r, not polynomial in the binary length of r.

## 9. Verified artifacts and limits

The authored standard-library compiler and test suite are self-contained. The copied fixed JSON is their coefficient source; tests independently multiply literal 4x4 generators and independently evaluate the exported JSON. The audit separately reconstructs the numerical source formulas without importing upstream code. `evidence/tests.json`, `evidence/tests-optimized.json`, and `audit/` record exact test counts and checks. The full accepting source example is independently checked through 94 inner tiles and 189 generator factors, with 12,220 natural auxiliaries and 1,602 squared residuals, and its SOS is exactly zero. The long example is evaluated/count-checked without emitting or expanding its huge SOS.

Finite tests do not prove absence of all alternative roots, universality, or nonhalting. The bijection, canonicality, and invalid-determinant statements are algebraic proofs above. The source construction's universality theorem remains a separate mathematical dependency; this packet does not reimplement an arbitrary-machine universal loader. No claim of novelty, optimal degree, minimal auxiliary count, target-factorization uniqueness, unbounded finite-foldness, fixed arity uniform in r, or a constant-operation implementation is made.
