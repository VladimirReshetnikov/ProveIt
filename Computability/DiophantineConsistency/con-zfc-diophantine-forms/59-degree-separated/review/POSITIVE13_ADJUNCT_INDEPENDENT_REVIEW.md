# Independent review of the degree-126 thirteen-positive adjunct

Status: PASS for the new algebraic adapter, its sign/completeness proof, literal circuit, and exact degree. This is an ordinary mathematical review with independent finite checks, not a proof-assistant kernel certificate or a fresh proof of the inherited native compiler.

## Result and comparison

The reviewed literal polynomial has thirteen strictly positive unknowns, exact total degree 126, and 91 live binary operations: 51 multiplications, 24 additions and 16 subtractions. It is a lower-degree/higher-operation tradeoff against the preserved thirteen-positive parent of degree 132 and 83 operations. It does not dominate that parent in both metrics, change the variable count, or establish global minimality.

## Exact adapter and soundness

The two new abbreviations M=a+1 and C=(a+3)(f^2-1) satisfy M C=Q because Delta=(a+1)(a+3) and Q=Delta(f^2-1). Here C is the auxiliary abbreviation, not the fixed coefficient port MC. Direct ring expansion gives

    M Z = Q V^2 - (Q-1)(M y-1)^2 - 1.

Suppose Nt(1+N)Ns(1+Z)=1. All four factors are integer units. The norm N is a square modulo 4, so 1+N cannot be -1; therefore N=0. Independently of transport recovery, Ns=-1 is impossible by the standard negative-Pell descent for discriminant (a+2)^2-1. Thus Ns=1 and Q=(Delta I)^2.

The final version correctly uses 1+Z, not the initially conservative 1+4Z. To justify its sign, put m=Delta I. A solution of x^2-(m^2-1)v^2=-b with 0<b<2m-2 would satisfy, after taking absolute values,

    (m-1)v < x < mv.

Indeed v>=1 and (2m-2)v^2>b. The norm-one transform has new positive integer ordinate mv-x<v and preserves the norm; the exact preservation identity is independently checked. Descent excludes every such negative value. If 1+Z=-1, the adapter gives the forbidden value b=2a+1. The needed strict bound follows before Nt is known:

    2Delta I-2-(2a+1) >= 2a^2+6a+3 > 0.

Consequently Z=0 and Nt=1. The recovered old ordinate is y_old=M y-1>0, since M>1 and y>=1. Thus the new solution maps to the parent's genuine positive thirteen-variable system. No sign argument assumes transport bounds prematurely, and no division occurs at an unchecked denominator.

## Canonical completeness

Completeness is an existence-preserving reconstruction, not a restriction on every old witness. The preserved parent proof, Section 9, supplies the explicit canonical choice

    m=Delta I, V=chi_m(R)/m, y_old=psi_m(R), R=3 modulo 4.

The odd-index identities give V=-c modulo f^2, V=-R modulo c, and y_old=-1 modulo m^2=Q. The last congruence also follows directly from the Pell recurrence: at odd indices the ordinate is an even polynomial in m with constant coefficient (-1)^((R-1)/2), which is -1 here.

Since M divides Q, y=(y_old+1)/M is a positive integer. The canonical strong relation gives gcd(c,f)=1 and f^2=1 modulo c. Hence T=(V+c+Rf^2)/(cf) is a positive integer and realizes exactly the retained literal expression V=c(Tf-1)-Rf^2. Replacing T and y leaves the main carrier and all other supplied coordinates unchanged. The adapter then gives Z=0. The inherited source and K215 interpretation remain explicit dependencies.

## Exact degree and literal arithmetic

The independent checker verifies the full new circuit suffix and byte-for-byte identity of its retained 73-gate prefix with the authenticated parent JSON. Every gate, every witness and all four coefficient ports are live. The complete package-39/44 coefficient tuple is authenticated against its binding and all 46 read-only source pins; beta=2^590069-1.

The potentially misleading main-norm cancellation is checked as a universal ring identity, not inferred from sampled rays. With D0=b0^2-G and the parent's cancellation register C2, direct substitutions give deg D0<=16 and deg C2<=32. The four terms in the norm identity have degree bounds 66,68,64,62, hence deg N<=68. Its displayed nonzero homogeneous form attains 68. The remaining bounds are deg Nt<=2, deg Ns<=34 and deg Z<=22. The top part

    Z22 = E0 f^2 (c0^2 T^2 f^2 - E0^2 y^2)

is nonzero because its two monomials in T and y are distinct. The product of the nonzero leading forms has degree 2+68+34+22=126 in an integral domain. Three independent univariate finite-field evaluations using the actual fixed tuple also attain degree 126 with nonzero leading coefficients; these certify a lower bound and corroborate the literal implementation, not the universal upper bound by themselves.

## Reproduction and limits

The independently authored `independent_check.py` uses only Python's standard library. It imports neither builder nor primary checker. Its normal and optimized outputs are identical in `INDEPENDENT_REVIEW_NORMAL.json` and `INDEPENDENT_REVIEW_OPTIMIZED.json`. It checks four universal ring identities, exact new wiring, source/payload hashes, topology/liveness, operation counts and three exact finite-field degree witnesses. The primary author's `check.py` separately requires SymPy, as declared in `requirements.txt`.

The proof hash and circuit hash are recorded in the receipts. Any later change to the proof, circuit, parent interface or coefficient tuple requires review again. No original late archive or frozen wave8 family was modified by this review.
