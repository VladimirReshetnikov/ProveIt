# One auxiliary Pell solution and CRT base for all indices

This strengthens the simultaneous-power construction in
`shared_power_proof.md`. The main Pell base A remains shared. For the finite
set of distinct positive exponents k_i, retain individual X_i,Y_i,S_i,R_i
but use one U,V,B for every index certificate. Write

    U^2-(A^2-1)V^2=1,
    B=A+U b,
    X_i^2-(A^2-1)Y_i^2=1,
    S_i^2-(B^2-1)R_i^2=1,
    Y_i=k_i+e_i,
    V=Y_i^2(v_i+1),
    B=1+4Y_i(q_i+1),
    S_i=X_i+U s_i,
    R_i=k_i+4Y_i r_i,

with natural witnesses throughout. Each individual family is a valid
Matiyasevich index certificate, so soundness is unchanged. In particular,
sharing U,V,B cannot introduce a false index.

For simultaneous completeness set X_i=X_{k_i}(A),Y_i=Y_{k_i}(A), all Y_i>0.
Let L=4 product_i Y_i^2. In the finite ring

    R=(Z/LZ)[s]/(s^2-(A^2-1)),

the element u=A+s is a unit with inverse A-s. Its powers lie in the finite
group of units. Therefore some positive r satisfies u^r=1. Equivalently,

    U=X_r(A)=1 mod L,    V=Y_r(A)=0 mod L.

As r>0 and A>=2, V>0. Thus each Y_i^2 divides V; U is odd and is coprime to
every Y_i. Put M=4 product_i Y_i. Then gcd(U,M)=1. The finite Chinese
remainder theorem supplies

    B=A mod U,    B=1 mod M.

Raise B by a positive multiple of UM until B>A. Set
S_i=X_{k_i}(B),R_i=Y_{k_i}(B). Polynomial dependence of Pell coordinates on
the base gives S_i=X_i mod U and R_i=k_i mod 4Y_i. Monotonicity in the base
gives S_i>=X_i, and Y_k(B)>=k gives R_i>=k_i. The displayed natural
quotients therefore exist, including b=(B-A)/U and
q_i=(B-1)/(4Y_i)-1. This proves a simultaneous extension for every finite
family of true positive power calls.

The finite-ring argument is used only in the proof of completeness. Its
modulus L and its group order do not appear as additional symbols or
unknowns in the delivered polynomial. This is ordinary finite arithmetic
formalizable in ZFC; it needs no unproved statement about primes or
uniform primitive roots.

## Product strengthening of the two divisibility families

There is a smaller materialization of the same simultaneous completeness
argument. Replace all individual divisibility witnesses by

    V=(product_i Y_i^2)(v+1),
    B=1+4V(q+1),
    B=A+U b.                                       (P)

The product is built by ordinary multiplication gates after the finite list
of index graphs is known. The original common V remains a natural witness,
so this late identity creates no cycle among definitional gate outputs.

For soundness, (P) implies V>0, Y_i^2|V and 4Y_i|(B-1) for every i. Together
with the other index equations it restores every condition of each original
index graph. Since Y_i>=k_i>=1, V>=1 and B>=5.

For completeness use the same finite-ring choice with
L=4 product_i Y_i^2. It yields U odd and gcd(U,V)=1: the latter also follows
directly from the Pell norm U^2-(A^2-1)V^2=1. Therefore gcd(U,4V)=1.
Choose B by CRT in the classes A modulo U and 1 modulo 4V, and raise B
above A. All displayed quotients in (P) are nonnegative integers. In
particular V is a positive multiple of product_i Y_i^2. Define S_i,R_i at
this new B as before. No soundness premise is lost, and simultaneous
completeness is preserved.
