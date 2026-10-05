# Strictly positive integer matrices with one terminal equality

There is an exact boundary beyond the recently proved finite cap theorem: allowing a single terminal equality between two evolving coordinates already transfers the accepted universal signed-matrix substrate to strictly positive integer matrices. A uniform one-coordinate extension realizes any finite signed integer alphabet. Applied to the pinned Gram interface, it gives a fixed eight-dimensional strictly positive alphabet, one common integer row sum, and a complete14=5M+9A positive ordinary-input loader.

This is a substrate transfer and a sharp distinction between fixed thresholds and variable equality. It supplies no fixed-arity Diophantine certificate for the unbounded selected word, and no reduction of the complete universal operation frontier. The particular universal matrix alphabet remains the effectively specified, unmaterialized alphabet of the accepted group theorem; no small numerical alphabet cardinality is claimed.

## 1. An exact positive lift with one extra coordinate

Let M_sigma be any nonempty finite family of integer r-by-r matrices, r>=1. Write 1 for the r-dimensional all-ones column and set

    kappa=1+max_(sigma,i) sum_j |M_sigma[i,j]|,
    C=(r+1)kappa.

Define the (r+1)-dimensional integer matrix

    L_sigma = [ M_sigma+kappa*1*1^T    kappa*1-M_sigma*1 ]
              [ kappa*1^T             kappa             ].       (1)

Every entry is at least1. Indeed |M_ij|<=kappa-1 and |sum_j M_ij|<=kappa-1. Every row sums to the same C, independently of sigma. If the whole original family is zero, kappa=1 and the construction is still valid.

Use the fixed signed decoder

    D=[I_r | -1],          D(z,h)=z-h*1.                         (2)

Direct block multiplication gives

    D L_sigma=[M_sigma | -M_sigma*1]=M_sigma D.                  (3)

Consequently, for every finite word w=(sigma1,...,sigmat), including the empty word,

    D L_sigmat ... L_sigma1 = M_sigmat ... M_sigma1 D.           (4)

This is proved by induction with ordinary integer matrix multiplication. There is no division, rounding, integrality promise or duration normalization in (3)--(4). All positive initial coordinates remain strictly positive under every selected letter.

For an arbitrary integer input vector v, choose an integer h>=1 with v_i+h>=1 and initialize (v+h*1,h). The differences then evolve as the exact signed M-history. Choosing h can be done effectively from v; this general statement does not claim a paid arithmetic cost for that choice. For the already positive input used below, h=1 is fixed and the entire loader is charged explicitly.

If the original acceptance is that the first signed coordinate is zero, (4) gives precisely

    first lifted coordinate = last lifted coordinate.          (5)

No intermediate guard, additional endpoint condition or variable initial witness is used in this transfer. Any inherited finite control restriction can also be retained, but the application below allows all finite words over its fixed alphabet.

## 2. The exact inherited ordinary-input interface

The accepted group_gram_zero_mortality.md, Sections2--4, provides a fixed finite signed integer alphabet A_sigma in dimension7, a fixed row

    u=(1,0,1,1,0,1,-4),

and positive input v(x)=(a,b,c,a,b,c,1)^T. For every recursively enumerable set S of positive integers, effectively fixed positive program numerals alpha,beta give

    x in S iff some word w satisfies u A_w v(x)=0,
    r=alpha*x+beta,
    a=(r-1)^2+1,
    b=(r-1)r^2+r+1,
    c=r^4+(r+1)^2.                                             (6)

The actual universal slice uses alpha=12*2^(p+1), beta=12*2^p. These are fixed program numerals; no run-time exponentiation of a varying program coordinate is being supplied. The alphabet is independent of both p and x. Its construction and effective group-embedding premise are inherited, not newly materialized or externally re-proved here.

The same note uses the unimodular matrix Q obtained from I_7 by replacing its first row by u. Since u_1=1, Q is invertible over the integers, and

    e1^T Q=u,
    w(x)=Q v(x)=(f,b,c,a,b,c,1)^T,
    f=2a+2c-4=2(r^2+1)^2>0.                                   (7)

Let F_sigma=Q A_sigma Q^(-1). This is still one fixed finite integer alphabet, and

    e1^T F_w w(x)=u A_w v(x).                                  (8)

Apply Section1 to the F_sigma, taking r=7 there. The resulting fixed L_sigma are strictly positive8-by-8 integer matrices with one common row sum C=8kappa. Initialize

    z(x)=(f+1,b+1,c+1,a+1,b+1,c+1,2,1)^T.                       (9)

It is strictly positive and D z(x)=w(x). Equations(4),(6),(8) therefore prove the exact contract

    x in S iff exists a finite word w:
                  (L_w z(x))_1=(L_w z(x))_8.                  (10)

All letters are fixed, all intermediate vector entries are positive integers, and the only test is the one terminal coordinate equality. The empty word never accepts: its coordinate difference is f>0. Thus permitting or forbidding the empty word makes no difference for these inputs. There is no inference from bare undecidability to the all-r.e.-sets interface; (10) uses the already proved ordinary-input theorem (6).

## 3. Complete14-operation input source

Literal copies and fixed entries cost no arithmetic, and every product, including alpha*x, is charged. Compute these fourteen binary operations:

| Row | Operation |
|---|---|
|1|rx=alpha*x|
|2|r=rx+beta|
|3|eta=r-1|
|4|s=r*r|
|5|u=s+1|
|6|aa=eta*eta|
|7|a_hat=aa+2|
|8|bb=eta*u|
|9|b_hat=bb+3|
|10|v=u*u|
|11|cc=v-a_hat|
|12|c_hat=cc+4|
|13|ff=v+v|
|14|f_hat=ff+1|

The output column is (f_hat,b_hat,c_hat,a_hat,b_hat,c_hat,2,1)^T. The five multiplications occur at rows1,4,6,8,10; the other nine rows are additions/subtractions. There are no supplied auxiliary witnesses. The formulas give a_hat=a+1, b_hat=b+1, c_hat=c+1 and f_hat=f+1 exactly. In particular

    c_hat=r^4+r^2+2r+2,

so every output is positive for r>=1, in particular on every valid program slice. The internal subtraction in this finite loader is allowed and charged; it is not a claim that the loader's intermediate expression has only nonnegative coefficients in every independently supplied register.

A straightforward extension of the prior13-operation positive-column loader by four distinct +1 rows gives the valid but looser17-operation bound. Absorbing the shifts into the three constant terms above reduces that bound to14. No false claim that17 was necessary is made. The14 count is only an input-column count, not the cost of deciding (10), selecting w or certifying an unbounded matrix history.

## 4. Strict positivity and uniform contraction do not decide exact equality

Every normalized matrix P_sigma=L_sigma/C is row stochastic and has each entry at least1/C. For a real vector z define osc(z)=max_i z_i-min_i z_i. Subtract the common all-ones matrix contribution1/C from P_sigma. The remainder is nonnegative and each row sums to

    theta=1-(r+1)/C=1-1/kappa.

The removed contribution acts identically in every coordinate, so for t>=1

    osc(P_sigma z)<=theta*osc(z),
    osc(C^(-t)L_w z)<=theta^t*osc(z).                          (11)

The empty word simply preserves the original oscillation. For kappa=1 the original family is zero, the remainder vanishes and one step makes all coordinates equal. For kappa>1 the factor is strictly between0 and1. This elementary estimate applies to every switching word, not merely to repeated powers of one matrix.

Along an infinite word, the minima of normalized states are nondecreasing and maxima nonincreasing, because each next state is a stochastic average. Their difference tends to zero by(11), so every coordinate converges to one common positive number when the initial vector is positive. This convergence is a statement about normalized trajectories; it does not replace the exact finite-word equality in(10).

**Review remark 1 (approximate agreement is not exact acceptance).** Take the one-dimensional signed matrix M=[1], so kappa=2,C=4 and

    L=[3 1; 2 2],             z0=(2,1)^T.

Its coordinate difference remains1 after every finite number of steps, by(3). Hence it never passes the equality test, although the normalized difference is4^(-t) and the coordinate ratio tends to1. This explicit example refutes replacing the exact terminal test by eventual arbitrary approximation. It is a boundary example, not a universal alphabet.

**Review remark 2 (the lift does not preserve full matrix identities).** Formula(4) is an intertwining statement through D. It does not say L(MN)=L(M)L(N), that the identity letter lifts to the identity matrix, or that inverse signed letters lift to inverse positive matrices. Every lift maps the common all-ones vector to C times itself, so a two-letter product has eigenvalue C^2 on that line. For the preceding identity example L^2 is therefore different from L and from I. The signed word action is recovered exactly on differences; full-operator mortality and group inversion are different interfaces.

## 5. What the boundary permits and what remains paid

The committed nonnegative_threshold_reachability_boundary_aristotle.md proves decidability for nonnegative integer polynomial updates with finite Boolean combinations of effectively fixed threshold and congruence guards. Every update in(10) is even strictly positive and linear. Its single terminal predicate compares two unbounded evolving values; it is not a fixed threshold atom over nonnegative-coefficient polynomials. The accepted nonrecursive instances of(10) therefore show that this guard restriction is essential even under strict positivity and a common row sum.

In particular there can be no total effective faithful replacement of this equality by only the capped theorem's fixed-threshold/congruence interface, even if the replacement may choose a computable finite cap, finite extra control and nonnegative polynomial updates from the ordinary input. Otherwise that theorem would decide a nonrecursive instance of(10). This is a precise interface obstruction, not a claim that all positive matrix problems are undecidable.

**Open question 1 (credited compiler task).** Root requested a substrate outside the capped model that could guide arithmetic compression. Equations(1)--(10) isolate the variable-equality endpoint while removing signed update coefficients and adding only one state coordinate. A competitive fixed-arity positive-integer certificate for the selected unbounded word is still absent. Its selectors, chronological consistency, length/radix data, endpoint equality and ordinary-input binding must all be paid. No gate saving over the complete group, matrix or U9 compilers follows from this transfer or from the14-operation loader.

The older Gram note already distinguishes nonnegative mortality from nonannihilating equality interfaces and credits an external two-generator result based on universal Diophantine polynomials. This note does not claim the first undecidable nonnegative equality problem and does not re-verify that external result. Its contribution is the explicit one-coordinate strictly positive constant-row-sum transfer, the direct ordinary-input loader, and the exact comparison with the new finite-quotient boundary. The earlier positive Markov-mask lift is related but different: it realizes signed matrices in Fourier coefficients up to a rational duration scale. Here the states and updates themselves are positive integers, and the signed differences are an exact proof decoder with no scaling.

## 6. Source and execution scope

The new lift, loader, contraction estimate and examples above are elementary handwritten derivations. No supplied, archived, committed, predecessor or frozen program was executed or imported; no saved source array was evaluated or used for degree propagation. Only inert document reading and fresh metadata are needed. The general effective group embedding and full accepted universal alphabet are inherited through the named proof interfaces, not newly constructed or certified against external literature.

Exact dependency hashes and declared read spans are recorded in the accompanying metadata: the complete capped-quotient note; the complete348-line Gram note; the complete ordinary-input commutator note, including its fixed-universal-alphabet Section5; and the already read finite Markov-lift interface. These bindings do not widen any prior external or machine-proof scope. All new files are in /tmp; no repository or Git mutation is performed.
