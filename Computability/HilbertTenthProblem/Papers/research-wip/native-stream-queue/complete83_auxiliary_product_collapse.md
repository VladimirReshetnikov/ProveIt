# Retaining the square does not repair the auxiliary-product deletion

Deleting only `auxiliary_Tf=auxiliary_quotient*f` from the actual84 circuit,
and supplying that product as a positive witness U, gives a complete
**83=46M+37A** source with **18 positive witnesses and exact degree185**.
Its inherited universal representation is **refuted**: every positive
ordinary input has infinitely many full positive zeros on every valid
fixed-program slice. The paid square `L16=f*f` is retained.

This identifies the missing divisibility `f|U` as sufficient to destroy
soundness, even when f remains an actual positive integer square root.
It is a different83 candidate from independent-gamma83, free-coefficient83
and outer-slack83. In particular it does not resolve the ordinary-input
language of independent-gamma83. The established universal bound remains84.

## 1. Full source and exact forward maps

The [helper](complete83_auxiliary_product_collapse.py) authenticates eleven
frozen files before reading their JSON arrays as inert data. Their exact
SHA256 values are stored in its PINS table and the [receipt](complete83_auxiliary_product_collapse.json).
No predecessor or archived Python is imported or executed. The three main
dependencies are [current84](complete84_scaled_strong_output.md), the
[square/product82 chart](complete82_auxiliary_square_product_chart.md), and
its later [all-input outer collapse](complete82_all_input_outer_collapse.md).
The early82 note's historical unresolved status is superseded by that later
collapse proof.

Only one producer is deleted. Its quotient witness is replaced by U, and
its sole consumer becomes `auxiliary_Tf_minus_one=U-1`. Every other row is
retained literally. The receipt emits all83 gates, all25 supplied ports,
the ordinary input x, the same six fixed compiler numerals and all18
positive witness names. Every row and supplied port is live. The complete
factor finalizer costs6M+1A; all factor producers cost40M+36A.

Formal expression interning through every emitted row proves the all-ring
identities

    F83prod(U=T*f) = F84,
    F83prod(f,U) = F82(F_aux=f²,U_aux=U).

Here T is the old auxiliary quotient, not the transport quotient. The
first map preserves every parent positive zero, but no positive integer
inverse is asserted. The second identity alone does not transfer the82
counterfamily: an actual square and its strong Pell equation must be
constructed together. That additional argument is given below.

## 2. Exact positive auxiliary projection

Use mathematical Pell base A=a+2, so the literal source register named
`A` is Delta=A²-1=(a+1)(a+3). Let c be `R10a`, R be `r_lhs`, and P5 the
product of the unchanged first, main, input, index and transport factors.
The literal child rows give

    S = Delta*i*c²,
    V = c*(U-1)-R*f²,
    Na = S²*(V²-y²)+y²,
    Ns = f²-Delta*i²*c⁴,
    F83prod = Delta*(P5*Na*Ns-1).

The actual strong factor is Delta*Ns. All symbols here abbreviate paid
source expressions; no factor or multiplication is omitted from the count.

Fix the fourteen outer witnesses, ordinary input and compiler numerals,
and assume c is odd and positive and R>0. Then

    there exist positive f,i,U,y with F83prod=0  iff  P5=1.       (1)

For necessity, Delta>0 allows cancellation. Delta is0 or3 modulo4, so
Ns cannot be-1 modulo4: when Delta=0 it is a square, and when Delta=3
it is a sum of two squares. Na modulo4 is V² if S is odd and y² if S
is even, so Na also cannot be-1. Since the integer product P5*Na*Ns=1,
both Na and Ns must be+1 and then P5=1.

For sufficiency, P5=1 forces each of its five integer factors to be±1.
The main factor cannot be-1 by the same Delta modulo4 argument. Its
literal positive root D and c thus satisfy D²-Delta*c²=1. At an integer
base A>1 this means D=chi_A(p), c=psi_A(p) for some p>0. We use the
standard definition `(A+sqrt(A²-1))^j=chi_A(j)+psi_A(j)*sqrt(A²-1)`.

Set

    m=2*c*p,  f=chi_A(m),  z=psi_A(m),
    i=z/c²,  S=Delta*z.

The quantity i is a positive integer: expand `(D+c*sqrt(Delta))^(2c)`.
Its term of square-root degree1 contains the factor2c², and every higher
odd-degree term contains c³. Therefore c² divides z. The Pell identity
gives Ns=1, and also f²≡1 modulo c. In particular the retained square
and strong factor have their exact intended values.

Because c is odd, choose any positive CRT solution

    v≡R (mod c),  v≡3 (mod4).

Put V=chi_S(v)/S and y=psi_S(v). For odd v this quotient is an integer
polynomial in S² with constant term `(-1)^((v-1)/2)*v`. Since c divides
S and v≡3 modulo4, it follows that V≡-R modulo c. Consequently

    U=1+(V+R*f²)/c

is a positive integer and restores the literal V expression. The Pell
equation at base S gives Na=1, completing (1). All four auxiliary
witnesses are refreshed together; (1) does not hold with an arbitrary
preassigned i. No congruence modulo f is imposed or used.

## 3. Full ordinary-input collapse

Sections1–3 of the pinned [all-input outer proof](complete82_all_input_outer_collapse.md)
construct, for every valid fixed-program numeral tuple and every x>0,
infinitely many positive choices of the fourteen outer witnesses with
each of the five factors individually+1, c odd, R>0 and main Pell rank
p>R. These are full source fields, including the original outer slack,
transport quotient, positive shared input quotients and first-index factor.
The packed R is the actual computed register, not a freely chosen host.

Those sections precede the old82 auxiliary completion and do not depend
on it. Applying Section2 above to each such outer tuple supplies positive
f,i,U,y, giving the actual seven factor values

    (1,1,1,1,1,1,Delta).

Their product is precisely the final target Delta. Thus all18 supplied
witnesses are positive and the complete83 polynomial is zero. The
ordinary input and all fixed compiler numerals are unchanged. Even a
valid compiler for a rejecting program therefore accepts every positive
input in this proposed representation. The construction uses the
inherited irrational-rotation existence argument for the outer family;
it does not assume the existence of primes in a new progression or a
realization by an actual accepting computation.

On these p>R examples, f cannot divide U. If it did, T=U/f would be a
positive integer and the all-ring forward identity would yield a complete
parent84 zero. The parent's retained local rank theorem would force p=R,
a contradiction. This diagnoses the lost divisibility; the all-input
proof above establishes the language failure independently of this
failure of a tuple inverse.

## 4. Uniform exact degree185

Give every supplied witness and x degree1, and each fixed numeral degree0.
Write

    Q=Bm1*Jrep,  k=eta+zeta,  gamma=rho+sigma,
    C1=Q-F-Z-alpha-twice_cell_bits*x,
    Nt_top=w*C1-transport_quotient*Q.

The literal retained rows and current84 degree proof give

    c_top=k*s*Q³,  Delta_top=w²*s²*Q⁸,
    R_top=Q³*(Q-F),  (S²)_top=i²*Delta_top²*c_top⁴.

Unlike82, both summands of V now have degree6. Its leading form is

    V_top=Q³*[k*s*U-(Q-F)*f²].

Hence Na has degree58 with leader `(S²)_top*V_top²`, and the scaled
strong factor has degree46 with leader `-(S²)_top`; the other five
factors are unchanged. Their exact degrees are22,18,32,58,7,2,46,
summing to185. Multiplication of their leading forms gives

    32 Q^111 h gamma delta² i⁴ k^11 w^18 s^29
        *Nt_top*[k*s*U-(Q-F)*f²]².                    (2)

Lowercase delta here is the input witness, distinct from Delta. The
f-free monomial

    Jrep^112*h*rho*delta²*i⁴*eta^13*w^18*s^31
        *transport_quotient*U²

has coefficient `-32*Bm1^112`, nonzero on every valid compiler slice.
The f-bearing cross terms cannot cancel it. Subtracting degree12 Delta
cannot cancel this leading form either. Thus the complete formal degree
is185 uniformly, while naive gate propagation gives only the upper195.
No relation that holds only at zeros is used to reduce degree.

## 5. Evidence boundary and replay

The fresh helper checks every full-source expression identity, liveness,
all83 paid gates,72 complete signed/rational assignments and two dense
univariate coefficient executions. Fourteen exact positive auxiliary
extensions evaluate the literal saved auxiliary/strong rows;2048 residue
cases corroborate the negative-unit exclusion. These finite checks are
supplements to the projection and inherited full outer proof. No giant
full compiler tuple is materialized, and the diagnostic numeral tuples
are not represented as valid program instances.

The [mathematical review](review_complete83_auxiliary_product_collapse_math.md)
independently checks the square-preserving all-input extension. The
[source review](review_complete83_auxiliary_product_collapse_source.md)
checks the emitted edit, identities and degree evidence.

    python3 complete83_auxiliary_product_collapse.py --root /absolute/native-stream-queue --expect complete83_auxiliary_product_collapse.json
    python3 -O complete83_auxiliary_product_collapse.py --root /absolute/native-stream-queue --expect complete83_auxiliary_product_collapse.json

The CLI uses explicit exceptions under both modes, rejects duplicate and
noninteger JSON fields in input receipts, and compares exact generated
receipt bytes. This packet rejects this particular inherited83 chart;
it makes no impossibility claim about unrelated83-operation universal
polynomials or different coefficient recipes.
