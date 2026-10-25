# Completing the shared-marker radix49 consistency equation

## Result and attribution

At ProveIt commit `55d1f72aedebf892e446c90d35fa1ae37689b0f2`,
`research/compact66-shared-marker-radix49/README.md` supplies a complete
ordinary native/Pell construction conditional on three explicit controller
unit conditions, a prime, and a valuation-one lift. Those numerical
conditions were not supplied there. The shared-marker encoding, its
carry-reset argument, and the fifteen-variable P66 polynomial are prior
repository work. This completion does not claim those ideas as new.

The new finite result is an explicit controller prime `lambda=434011`, all
required units and orders, a fully materialized coherent coefficient tuple,
and independent reproducible checks. Under the retained ordinary
syntactic-refutation calibration, there is no remaining controller premise:

    ZFC proves: P49 has no strictly positive integer zero iff Con(ZFC).

The equivalence is proved by composing the pinned ordinary conditional
theorem with the finite arithmetic certificates below. This is not a new
Lean derivation, a proof that ZFC is consistent, a reduction in the number
of variables or degree, or a global minimum claim.

## 1. Exact polynomial

There are exactly fifteen independent positive integers:

    J,F,alpha,z,f,h,i,T,s,w,tau,eta,zeta,y,gamma.

Every other symbol in the following display is a polynomial abbreviation:

    q=beta*J+1; C=q-F-alpha; X=w*q; Y=s*q^3; E=X*Y;
    k=eta+zeta; ell=E*k*Y; c=k*Y+eta; a=E+Y;
    H=4*a+3; Delta=a^2+H; D=X+a*c+gamma*H;
    R=[(q-1)*(q-F)+alpha]*(q^2-1)+(MC+q*MF)*J;
    V=f^2*(c*T-R)-c; S=i*Delta*c^2;
    N0=tau^2-ell*(ell+k);
    N1=D^2-Delta*c^2;
    Na=S^2*(V^2-y^2)+y^2;
    Nk=k-h*E-R;
    Nt=(K0+w)*C+(q-F)-z*(q-1);
    Ns=Delta*f^2-S^2;
    P49=N0*N1*Na*Nk*Nt*Ns-Delta.

The equation is `P49=0`. Its entire 66-row straight-line program is in
`polynomial.json`. It uses 38 multiplications, 15 additions and 13
subtractions. Every row and every input is live. The four named constants
are fixed integers, not unknowns or number-theoretic predicates.

## 2. All four constants

Let `L=8807`, `rho=2^49`, `B=rho^L`, `beta=B-1`, and
`Lambda=rho^4393+rho^5495`. Use the ordered 943 tile tuples
`(w_i,n_i,p_i,s_i)` fixed by the supplied 436-character seed and complete
closed decoder. The decoder is implemented in `radix_probe.py`; its result
is compared pointwise with all 943 published tuples. In particular the
Start, Forbidden and initializer tiles are unchanged.

Set `u_i=w_i+2^8*n_i+2^17*p_i+2^25*s_i`. The 3297 coefficients of
`Phi(x)=sum(c_e*x^e,e=0..3296)` are exactly:

    c_i=1+2^10*(2^34-u_i), i=0..942;
    c_(1023+j)=2^(10+j), c_(1003+j)=2^(27+j), j=0..7;
    c_(1013+j)=2^(18+j), c_(983+j)=2^(35+j), j=0..8;
    c_e=2^44, e in {992,1011,1022,1031,1095,2195,3296};
    c_e=0 otherwise.

There are 984 nonzero coefficients. Let `Ephys` be their support together
with the two zero-coefficient dummy positions 1063 and 1064; its cardinality
is 986. Then

    K0=rho^30+rho^62+rho^1100+rho^2201+rho^8849
       +sum(c_e*(rho^(4393-e)+rho^(5495-e)),e=0..3296);
    MC=beta-sum(rho^e,e in Ephys except 1)-2*rho^1063;
    Ccore=sum(rho^e,e=1013..1022)+sum(rho^e,e=1065..1073)
          +rho^2195+rho^3296;
    MF=2*B+3+(2^47-2)*Lambda+Ccore-rho^8792
       +(2^41-3)*rho^7693-rho^7691.

In particular `MF` already includes the single shift by `beta` from the
native high mask. No port from the old radix55 or radix67 tuple is mixed
with the new tuple. The raw arrays are canonical little-endian unsigned
integers stored in deterministic gzip files in `coefficients/`.

The entire changed Phi array was also reconstructed independently by
factoring the checksum-verified old radix67 integer K. After subtracting
its five bare monomials, exact division by `rho67^1097+rho67^2199`
recovers its reversed 3297-slot coefficient polynomial. Every original
coefficient, including every zero, agrees with the typed-tile route.
Changing precisely the seven marker slots gives the complete new array.

## 3. Finite controller theorem

Put `d=49*8807=431543` and `lambda=434011`. The latter is prime: the
standalone checker divides it by every integer from 2 through 658 and
finds no divisor. Moreover

    lambda-1=434010=1887*230=2*3*5*17*23*37,
    lambda>d.

For `Hctrl=1+B*K0+B^2`, the exact modular associations are:

| Modulus | B | K0 | Hctrl |
|---:|---:|---:|---:|
| 7 | 4 | 5 | 2 |
| 49 | 18 | 47 | 44 |
| 8807 | 1901 | 973 | 3135 |
| 434011 | 398487 | 335571 | 6522 |

All required Hctrl values are units. The prime-square modulus 49 is
retained explicitly; checking only modulus 7 would not establish the
annihilating-order claim modulo the entire d. Exact orders are

    ord_49(B)=3;
    ord_8807(B)=629=17*37;
    ord_lambda(B)=18870=2*3*5*17*37.

The checker proves each exact order by its annihilating power, a complete
prime factorization, and every maximal proper-power nonidentity. In
particular `B^2-1` is a unit at 7, 8807 and lambda, and `1887` is a common
multiple of the two fixed-modulus orders. Finally,

    B^(lambda-1) = 96356084144
                 = 1+222013*lambda       (mod lambda^2).

Since `0<222013<lambda`, this proves
`v_lambda(B^(lambda-1)-1)=1`. These facts discharge every condition in
section 9, equation (3), of the pinned conditional49 proof. The controller
prime does not occur in any of the four coefficients: it is a witness used
only in the converse proof.

## 4. Why these finite facts close completeness

Here is the proof composition, with the unbounded ingredients stated
explicitly rather than confused with finite tests.

The inherited conditional49 proof first recovers one genuine tile in each
occupied low cell from bounded cyclic carries. Seven equal marker weights
recover all seven Boolean markers by counting; no physical marker is
deleted. Its carry bound drops from 24 before decoding to 3 after decoding.
Local zero predecessors protect both phase anchors, the 19 copy tests,
the clause tests and every padding field. This proves unconditional
soundness for the entire new coefficient tuple.

Conversely, a finite refutation supplies a padded canonical marked tiling
whose width and height are independently cofinal. Take fresh dimensions
`width=lambda^r_w`, `height=lambda^r_h`, and
`N=lambda^(r_w+r_h)`, sufficiently large. Then `q=B^N` and the actual
native words yield

    0<F<q/rho^15, 0<C<q/rho^5510, 2*C+F<q/3.

These estimates hold after every simultaneous subset of safe low-dummy
changes. Such a change in cell j has an ordinary, unwrapped increment
`deltaF=(K0+B^width)*rho^1063*B^j`. Therefore the actual rank changes by

    deltaR=-Gamma*B^j,
    Gamma=rho^1063*(q^2-1)*[1+q*(K0+B^width)].

The certified units make Gamma invertible modulo the full `d*N`,
including `7^2`. The valuation-one lift and CRT imply that the first
`N/lambda` powers of `B^(lambda-1)` enumerate the complete progression
`1+d*lambda*z` modulo `d*N`. The pinned Boolean subset-sum argument then
tunes the actual rank to `d*width` modulo `d*N` without altering any tile,
mask, padding field or positivity margin. This is a change to actual
native witnesses, not an independent choice of a desired rank.

The native population identity gives `pc(R)=3*d*N+2` and `R=3 mod 4`.
The retained Pell/half-binomial converse reconstructs all positive P66
variables, with the required odd and square phases. The reverse
implication extracts the marked computation and a finite refutation from
any positive polynomial zero. Composition with the retained K215 and
syntactic ZFC calibration therefore proves positive existence iff finite
ZFC refutation. Negation gives the stated consistency equivalence.

The complete ordinary proof of each carry, seam, sign, Pell and calibration
ingredient is retained as a pinned source dependency. This completion
does not replace those proofs by runtime tests or assert that their Lean
formalization has been finished.

## 5. Exact degree and measurable improvement

Let `Z=X+gamma*H`. The identity

    N1=2*a*c*Z+Z^2-H*c^2

cancels the apparent degree-22 terms. Thus the six factor degrees are
22, 18, 62, 7, 2 and 46, and the polynomial degree is at most 157.
Setting all fifteen inputs equal to an indeterminate t gives leading term

    2^17 * beta^91 * t^157.

Since beta is positive, the degree is exactly 157. The two modular
univariate circuit computations independently attain this coefficient
at primes 1000000007 and 1000000009; the symbolic degree upper bound is
the displayed identity, not an inference from numerical samples.

| Tuple | beta bits | K0 bits | MC bits | MF bits | Raw bytes |
|---|---:|---:|---:|---:|---:|
| Maintained radix55 | 484385 | 486696 | 484385 | 484386 | 242484 |
| Verified radix53 | 466771 | 468998 | 466771 | 466772 | 233666 |
| Completed radix49 | 431543 | 433602 | 431543 | 431544 | 216030 |

The new tuple saves 17636 bytes against the verified radix53 tuple and
26454 against the maintained radix55 tuple. The four new gzip files total
8774 bytes. Raw coefficient storage and gzip storage are different metrics.
This note makes no printed-page-length or expanded-polynomial-height claim.

## 6. Reproduction and dependencies

From the directory containing these scripts run:

    python3 radix_probe.py
    python3 materialize_radix49.py
    python3 verify_radix49.py

The verifier uses only the Python standard library and imports neither
builder. It checks full arrays and tuple bytes, modular associations,
primality, exact orders, the lift, circuit liveness and degree attainment.
Sixteen deliberate coefficient/certificate corruptions are rejected for
specific reasons. Normal and optimized verification output is byte-identical.

`DEPENDENCIES.json` separates copied proof dependencies from newly emitted
finite artifacts. The 24 directly pinned prior files are copied byte for
byte into `sources_pinned/`; the source commit and original SHA256 records
are preserved. The new construction is a completion of the conditional49
proposal, not a new machine calibration or a fresh transitive formal audit.

AI assistance: this finite completion, programs and explanatory note were
prepared with ChatGPT in the present research iteration.
