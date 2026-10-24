# Independent review of the three-root valuation merger

Status: the following unbounded mathematical reduction is sound on independent review. It is an existence equivalence relative to the exact CRT17 parent, not a new proof of its inherited native/compiler/refutation calibration. The review is by another AI research worker, not external peer review.

## 1. Parent interface and retained information

Use the literal `transport/degree88_17.json` in incoming `con_zfc_pell_congruences_2026-10-23.zip`, pinned at ProveIt `cfbf118b4ad9b2c651fe96b571d9415261766328`. Its five residuals are the half-centered first norm, main Pell norm, ordinary strong norm, auxiliary norm, and shared positivity row. The proposed merger retains the ordinary strong row and shared positivity row, and replaces the other three.

Parent definitions include

    J=3J3+1, q=beta J+1, W=4(3w3+1), X=qW,
    Y=(2v+1)q^3, E=XY, a=(X+1)Y, H=4a+3,
    Delta=a^2+H, k=R+1+hE, eta=c-kY, zeta=k-eta,
    I=(2r+1)c^2, Q=I^2, V=fcT-f^2R-c,
    u=EYk, P=2u+k, A=u(u+k)+1,
    D0=X+ac, Cmain=Delta c^2+1.

The authentic beta is `2^1064921-1`, hence beta=1 modulo3 and beta>17. The candidate keeps its entire six-integer tuple unchanged.

The shared guard is

    d*Zeta - (pair_root^2-d-Zeta+1)^2 = Pos,
    Zeta=eta*zeta,
    Pos=1+s1^2+s2^2+s3(s3+1).

It implies d>0 and Zeta>0. Pos is always positive on integers. The product d*Zeta is positive; if d=-b,Zeta=-e were both negative, the squared expression would be at least (b+e+1)^2>be, a contradiction.

Thus eta and zeta have the same nonzero sign, |k|>=2, and |eta|<|k|. Since c=eta+kY,

    |c| >= |k||Y|-|eta| > (|Y|-1)|k|.

J cannot vanish, so |q|>=beta-1>16, and |Y|>=|q|^3. Therefore |c|>1. I is an odd nonzero multiple of c^2, giving Q>1 independently of all three deleted root equations.

## 2. All three radicands are 3-adic units

The literal restrictions give

    q=2 mod3, W=1 mod3, X=2 mod3, a=0 mod3,
    H=0 mod3, Delta=0 mod3.

The retained strong row Q=Delta(f^2-1) implies 3|I and Q=0 modulo3. Write delta=Q-1. Then delta=-1 modulo3 and delta>0.

Writing b=XY^2 gives A=b(b+1)k^2+1. Since b is either0 or-1 modulo3, A=1 modulo3. Also b(b+1)>=0 for every integer b, so A>=1.

Cmain=1 modulo3. Moreover Delta=(a+2)^2-1 is nonnegative: the only integer a making this expression negative is a=-2, excluded by a=0 modulo3. Its zero cases are excluded by the retained strong row Q>1. Thus Delta>0 and Cmain>0.

Let B=(QV^2-1)/(Q-1). Its numerator and denominator are both-1 modulo3, so v3(B)=0 and B=1 modulo3 in the localization of Z at3. B cannot be zero, since Q>1 and V is integral. It can be negative only when V=0; that branch is excluded by the norm as below.

H=4a+3 is odd and never zero. Let h=v3(H)>=1. No division by H or delta is introduced into the polynomial itself.

## 3. Elementary valuation separation lemma

Let nonzero positive rational radicands d_i have v3(d_i)=0. Let rational nonzero weights w_i have pairwise distinct 3-adic valuations. If a signed sum of w_i sqrt(d_i) is rational, every sqrt(d_i) is rational.

Proof: partition the radicands by Q-squareclass. Within one class choose a representative d. Each sqrt(d_i)=r_i sqrt(d) with r_i rational, and v3(r_i)=0 because both radicands have valuation0. Thus the rational coefficients epsilon_i w_i r_i have pairwise distinct valuations. A nonempty sum of rationals with a unique lowest valuation cannot vanish: clear denominators and divide by the lowest power of3, then reduce modulo3. Distinct squareclasses give linearly independent square roots over Q (equivalently, distinct characters in their multiquadratic field). A rational sum requires each nontrivial class coefficient to vanish, which is impossible. Therefore no nontrivial class occurs. This does not presume independent sign-flips for dependent radicands.

The weights in the candidate are

    6H, 18H, 2,

whose valuations are h+1,h+2,0. They remain pairwise distinct for arbitrary signed H. The lemma therefore applies to A,B,Cmain once B>0.

### A shorter proof specific to three roots

The general squareclass lemma is not needed to formalize the actual15-variable endpoint. The carrier defined below is identically1 modulo3:

    p=2(X+ac)+H(...)=1 mod3,

so p is nonzero. The three *weighted* radicands have valuations 2h+2,2h+4,0, so they are pairwise distinct. For any three signed nonzero roots x,y,z with distinct rational squares a,b,c and nonzero rational sum s, set

    u=(s^2-a-b-c)/2,
    v=(u^2-ab-ac-bc)/(2s).

Then u=xy+xz+yz and v=xyz. The identity

    x=a(a+u)/(as+v)

expresses x rationally, because its denominator is x(x+y)(x+z), nonzero by the distinct squares. Cyclically y,z are rational. Thus the actual15-variable proof can use only elementary rational identities and integer valuations. The more general squareclass lemma is a useful extension, not an indispensable imported theorem.

## 4. Centered carrier and cleared norm

The proposed new integer coordinate is xi. Set

    p=2D0+H(xi+3P+18V).

Use the ordinary three-root polynomial

    F8(t;a,b,c)=[(t^2-a-b-c)^2-4(ab+ac+bc)]^2-64abc t^2.

It is the product over the eight signed sums of square roots. The proposed norm is delta^4 times

    F8(p; 36H^2 A, 324H^2 B, 4Cmain).

For a literal denominator-free definition put

    alpha=36H^2 A, betaN=324H^2(QV^2-1), gamma=4Cmain,
    L=delta(p^2-alpha-gamma)-betaN,
    K=L^2-4delta^2 alpha gamma-4delta betaN(alpha+gamma),
    N=K^2-64delta^3 alpha betaN gamma p^2.

All quantities here are integer polynomials and delta>0 on retained-row zeros. Any algebraic reduction of N must preserve this exact polynomial identity up to a fixed nonzero scalar or a retained-row multiple; its metrics need separate checking.

If N=0 and B<0, each signed factor has exactly one nonzero imaginary contribution from sqrt(B), while the other two radicals and p are real. No factor can vanish. Therefore N=0 forces B>0.

The factorization then supplies signed roots tau,y,D with

    p=6H tau+18H y+2D,
    tau^2=A, y^2=B, D^2=Cmain.

Valuation separation makes all three roots rational. Rational-square-root integrality gives tau,D in Z. The adjacent-coefficient Pell descent lemma, applied to QV^2-(Q-1)y^2=1, gives y in Z. The Q>1 hypothesis was established before invoking the merger.

## 5. Exact restoration of all parent coordinates

Define

    tau_half=2tau-P,
    y_gap=y-V.

Both are integral and restore the first and auxiliary parent rows. For the main coordinate,

    2(D-D0)=H[xi+3P+18V-6tau-18y]
            =H[xi-3tau_half-18y_gap].

Since H is odd, the bracket is even. Hence

    gamma_old=(xi-3tau_half-18y_gap)/2

is an integer and D=D0+H gamma_old, restoring the main Pell row. In particular, merely writing a rational quotient by H would be insufficient; the parity argument or cancellation of2 modulo odd H is essential.

Conversely, from any parent zero the first half-centered row implies tau_half+P is even: modulo4 the row is (tau_half+k)^2=0, and P=k modulo2. Set tau=(tau_half+P)/2 and y=V+y_gap, retaining D=D0+H gamma_old. Then

    xi=2gamma_old+3tau_half+18y_gap

is integral and makes a factor of the proposed norm vanish. Thus the transformation preserves existence on each fixed tuple of the other fourteen coordinates. It is not generally a one-to-one map of full zero sets because a norm packages several sign choices.

The retained strong and shared-guard rows plus N yield three residuals in15 unrestricted integer variables. Sum of their squares is a single equation. A possible alternative finalizer is `(1+N)(1+S)-1`, where S is the sum of squares of the two retained rows: 1+S is a positive integer, so this also forces N=S=0 without a sign or modulo4 premise on N.

## 6. Repository novelty audit

Searched all available DiophantineConsistency Markdown, TeX and Lean sources plus all ten incoming ZIP text extractions for p-adic/3-adic separation, valuation/root/weight combinations and squareclass discussions. Existing root mergers use archimedean majorants, dominance, pairwise radicand separation, or rational-residue growth. Existing valuation uses concern divisibility, Pell nonsquares and intersective polynomials. No inspected source uses distinct prime valuations of radical weights to force rationality of the merged roots. This is a scoped repository search, not a literature-wide priority claim.

## 7. Remaining verification scope

The mathematical merger and its exceptional cases are settled above. Literal circuit generation, symbolic cancellations, degree certificates, operation counts, actual coefficient bytes, and end-to-end calibration remain separate obligations. This review does not infer any consistency decision or an encoded ZFC proof from finite computations.
