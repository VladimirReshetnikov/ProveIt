# The compact 15-variable companion: degree214, 139 operations

This companion keeps the ordinary signed strong-Pell source, with
J=3j+1, I=(2r+1)c², Q=I², V=fcT-f²R-c. In particular f is an
independent integer unknown. The three eliminated parent coordinates are
its half-centered first root tau, auxiliary gap y_gap, and main congruence
quotient gamma; they are replaced by xi. The source has17 integer coordinates,
so the new equation has15. Its ordinary semantic proof is PROOF15.md.

The literal DAG uses the same abbreviated quantities as that proof, with
u=EYk, Pfirst=2u+k, D0=X+ac, delta=Q-1, and

    p=2D0+H[xi+3Pfirst+18V],
    A=36H²[u(u+k)+1],
    D=4(Delta*c²+1),
    Bnum=324H²(QV²-1),
    U=delta*(p²-A-D)-Bnum,
    L=U²-4delta²*A*D-4delta*(A+D)*Bnum,
    N=L²-64delta³*A*D*Bnum*p².

The compact expression is the standard symmetric three-root identity:

    N=delta^4 product_(eight signs)
       [p ±sqrt(A) ±sqrt(D) ±sqrt(Bnum/delta)].

It is a fixed ordinary polynomial. The expression displays no variable
exponent or rational denominator. The fraction occurs only in its norm
interpretation in the proof.

The complete single equation is

    (1+4*strong)(1+4*guard)(1+4*N)-1=0,

with strong=Q-Delta*(f²-1) and the retained joint-positivity guard.
As every factor is1 modulo4, the product equals1 exactly when all three
residuals vanish.

To compare this compact polynomial with the generic568-term resultant in
PROOF15.md, write p=H[xi+3Pfirst+18V]+2D0. Over the rational-function field,
both polynomials have exactly the same eight linear factors in xi and the
same leading coefficient delta^4*H^8. They are therefore equal. Because both
sides are integer polynomials, the equality also holds identically before
specialization. The degree156 norm proof in PROOF15.md thus transfers without
change. The strong and guard residuals have respective degrees14 and44.
The final polynomial has exact degree14+44+156=214.

The supplied full arithmetic DAG has139 live binary operations under the
same count convention as the13/14-variable forms. Exact modular polynomial
specialization with the authentic coefficient bytes independently produces
degree214 and a nonzero leading coefficient. This comparison is a literal
algebra check, not a consistency decision or a new compiler formalization.
