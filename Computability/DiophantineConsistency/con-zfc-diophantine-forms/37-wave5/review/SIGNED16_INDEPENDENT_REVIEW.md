# Independent review of the proposed sixteen-integer reduction

Status: the mathematical guard-removal and weight-refinement arguments pass independent review, subject to the inherited Jones-ratio/compiler interface stated below. This is an ordinary proof audit, not a proof-assistant certificate. Generated circuit fidelity and exact complexity must be checked separately against the final builder.

## Source and scope

Source 29 is pinned at [SIGNED17_PROOF.md](https://github.com/VladimirReshetnikov/ProveIt/blob/8c6eec9d19ef80538c8e61ff6e0180040583446a/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/29-simpler-forms/signed17/SIGNED17_PROOF.md), especially Sections 1–5. Its entire T4 coefficient tuple, quartic32 normalization, factorial-weighted index recipe, Jones ratio theorem, compiler proof, and K215 calibration are imported. Replacing that tuple requires a separate whole-interface argument and rebuilding every coefficient and index leaf.

The proposed reduction keeps eight base coordinates unrestricted, imposes five explicit coordinate guards (epsilon, g0, s0, w0, phi nonnegative), and imposes m>0. Six stack variables encode those six inequalities. Together with two finalizer variables, there are exactly 8+6+2=16 integer unknowns. The old explicit j0 guard is replaced by an existential witness-restoration argument. This is not a claim that every initial j0 is already nonnegative.

## 1. Preconditions really precede j restoration

Suppose the relaxed ratio predicate has a0 and a1 integer squares, JF dividing QF+J(H−C), m>0, i nonzero, and the five coordinates above nonnegative.

Source 29's proof of its h lemma does not use j or H anywhere. It proves R>=2 and h>=1 from precisely these hypotheses. In particular Y,U>=1, A=RY(U+1)>=4, C=2R+1+bw+phi>0, and J=4A−5>0. These statements are available before restoring j.

Now D=(A^2−1)C^2+1>=A^2>1. Since i,J,D,C are nonzero, E=iJDC^2 is nonzero and F=(A^2−1)E^2+1>1. Also CD+1−A>=A^2+1−A>0, so G1=A+F(CD+1−A)>A>1. Therefore I=(G1^2−1)H^2+1 is positive even for negative or zero H.

## 2. The three square factors can be separated

Because E is divisible by both J and D,

- F is 1 modulo J and D;
- gcd(J,F)=gcd(D,F)=1;
- JF dividing QF+J(H−C) implies F dividing H−C.

The defining expression G1=A+F(CD+1−A) gives G1=1 modulo D and G1=A modulo F. Consequently,

- I=1 modulo D;
- I=(A^2−1)C^2+1=D modulo F.

Thus gcd(D,I)=gcd(F,I)=1 as well. The positive integers D,F,I are pairwise coprime. Since their product a1 is a square, each is an integer square. Positivity is important here: it avoids any signed-square ambiguity.

## 3. Pell orbit restores positive j without moving another condition

Put delta=G1^2−1. As G1>1, delta is positive and strictly between (G1−1)^2 and G1^2, hence nonsquare. Let x be the positive integer square root of I. Then x^2−delta H^2=1 and alpha=x+H sqrt(delta)>0, including when H is negative or zero.

The integer matrix M=[[G1,delta],[1,G1]] has determinant 1. Modulo the positive integer C F it lies in a finite group, so M^k is the identity modulo C F for some positive k. Write

    x_n+H_n sqrt(delta)=alpha (G1+sqrt(delta))^(kn).

Both coordinates remain integers; the norm remains one; H_n=H modulo C F; and H_n tends to positive infinity, because alpha>0 and G1+sqrt(delta)>1. Choose n with H_n>2R+1. Since H=2R+1+jC, the integer

    j_n=(H_n−(2R+1))/C

is strictly positive. Therefore its base coordinate j0_n=j_n−1 is nonnegative.

Only H and j change. All of R,U,Y,A,C,D,E,F,G1,m,a0,D0 remain fixed. The new I_n is a square, and D and F were already squares, so a1_n=D F I_n is a square. T0 changes by J(H_n−H), a multiple of JF. The divisibility condition is preserved. Signed-i restoration is unaffected.

This proves existence-equivalence of the relaxed and original natural-coordinate ratio predicates. The reverse implication is immediate by forgetting the j guard. No assumption that H was initially nonzero, positive, or in a nontrivial Pell orbit is needed: the unit power itself makes the zero-H case nontrivial.

## 4. Weight refinement is valid for all integer assignments

Every stack factor is 1 modulo 4, so Cstar is always 1 modulo 4. Thus Cstar is either at least 1 or at most −3. For Cstar>=1,

    (Cstar+1)^2−|Cstar|=Cstar^2+Cstar+1>0.

For Cstar=−t with t>=3,

    (Cstar+1)^2−|Cstar|=t^2−3t+1>=1.

Therefore w1=Cstar+1 is never zero and |w1|>sqrt(|Cstar|). With w2=w1(P^2+K^2+2), source 29's universal radicand bound gives

    |w2|>sqrt(|Cstar|)+|w1| sqrt(|a0|).

The separated-root proof must use absolute weights, because both weights can be negative before square recovery. With that wording, its largest-index triangle inequality and Galois argument are unchanged, including negative radicands, repeated square classes, zero roots, and negative S. Squaring the weights in the literal norm formula is compatible with this proof. After the norm proves Cstar is a square, Cstar>0 and the ordinary converse is immediate.

## 5. Remaining obligations for the final artifact

1. The actual builder must remove only the j guard and its stack variable, not j itself. H still depends on the unrestricted j coordinate.
2. Stack nonzero enforcement must use exactly i times the six stack variables. Removing a guard does not permit a zero stack coordinate.
3. The global D0!=0 and homogeneous-intersective nonvanishing lemmas must remain intact before positivity is recovered.
4. The theorem must state existence-equivalence, not pointwise positivity of j.
5. State every fixed leaf and the entire coefficient binding. Neither modular agreement nor the present proof validates a changed compiler tuple.
6. Recompute exact degree after the shorter stack and linear w1. Structural upper bounds require a nonzero leading-term certificate before being called exact.
7. Attribute the signed17 source, Pell-orbit restoration, and the source compiler separately; make no global minimality or end-to-end kernel claim.
