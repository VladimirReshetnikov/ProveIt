# Independent mathematical review: the 286-integer direct quartic

Reviewed sources: `PROOF.md`, `PROOF_ORIENTED.md`, and the retained package-131 ordinary proof, in this workflow. This is a scoped AI-assisted mathematical review of the new unbounded reasoning. It is not an external human endorsement, an independent rebuild of the final coefficient file, or a new formal proof-assistant verification.

## 1. Even frame and signed anchor

The new W is even and at least 514 because the actual horizon atom is at least sixteen. The equation A=2a^2-1 gives A>=-1; the lower-frame norm excludes A=-1 and A=1 since W>0 and 2z+1 is nonzero. Thus A>=2 and odd before any Pell classification.

For completeness A=X_W(W+1), a=X_(W/2)(W+1) satisfy the doubled trace identity. The odd frame ordinate follows from Y_n(W+1)=n modulo 2W. At odd base A, X_n is always odd and v_2(Y_n)=v_2(n), by parity and repeated Pell doubling. The binomial expansion of the C-th power of the unit at index W proves C^2 divides Y_(WC). Therefore l=2WC gives J=Y_l divisible by 2C^2 with odd quotient. The proposed e is integral. H is odd and gcd(H,J)=1, so the comparison CRT is compatible. In soundness a negative J changes only the sign of its Pell ordinate, and the inherited index and comparison arguments use its absolute value; the required divisibilities and D=1 modulo 4C remain intact.

## 2. Pooled abscissa signs

Adding (x_i-1)^2 to the existing pooled row adds no raw coordinate. The cap bounds the actual indices, not the abscissas. Reducing X_j modulo A-1 legitimately replaces each huge signed x_i by sigma_i. Each resulting small summand is at most 4(W-1)^2+4<4W^2, and fifteen times this is less than 4W^3<A-1. The conclusion simultaneously fixes all abscissa signs and identifies all signed indices. The zero-index case is included.

## 3. Negative exponents and the order of sign recovery

The identity (X_h-(A-n)Y_h)(X_h+(A-n)Y_h)=1+T Y_h^2 has the correct sign, with T=2An-n^2-1. For a negative requested index the power row therefore implies m*n^h=1 modulo T. The frame bound makes its absolute error strictly smaller than T, forcing an impossible integral inverse at n>=2. This does not assume m positive.

The bootstrap order in Section 5 is acyclic: odd-square q gives only q>=1; positive t first certifies the base F^2+1, including its possible base-one case. The ceiling then makes F positive and B>=2. The q+1 powers independently recover all nine actual representatives as nonnegative, making H0>=3. B^K then gives K>=0; the beta endpoint strictly excludes K=0. Only after q=(BH0)^K>=36 is the q-based exponent x+1 used to infer x>=-1, and the endpoint excludes x=-1. Thus neither the removed x guard nor the removed q-B-1 guard is used prematurely.

For the K=0 exclusion I checked the exact inequality: L-(3+t+y+F)=t(y-1)-F-2>0. For the endpoint-quotient recovery, a negative first quotient would force x<=F-y<0, while a negative last quotient would force x<=1-L<0. These are valid once the preceding signs are established.

## 4. Zero representatives and common radix

The actual representatives, not their stored minus-one coordinates, enter the binomial and constructor proofs. An actual zero is legitimate for natural polynomial constructors and binomial coefficients. The range conclusion a mod p^e<k is immediate when a<k (including zero); the inherited valuation proof covers a>=k. Thus relaxing a_i>=1 to a_i>=0 preserves the decoded natural source. H0=3+2 sum a_i both guarantees oddness and bounds max(1,a_a,...,a_d)+1 even when the syntax arguments vanish.

The completeness odd-square condition is compatible: each factor 1+F^2/i is odd because i divides even F, so B is odd; H0 is odd and K=2R is even. The displayed radix-square witness is integral. All later carry estimates use the recovered nonnegative actual arguments and q>=B^2>V.

## 5. Linear cofinal modulus

The new y=V-1 was derived independently in the parallel natural branch and checked here. For padded labels at most t and multiplicity at most t+1, each accumulator is at most ((t+1)F)^(t+1). The bound F=t!>(t+1)^2 for t>=16 makes this strictly smaller than F^(2t), which is at most V-1. Also F divides V-1. These are the needed beta-CRT hypotheses. Soundness recovers y>=F+1 already from the exact power and F>=1, without factorial correctness. The linear relation is therefore licensed in both directions and supports the claimed extra linear elimination.

## Conclusion and boundaries

No flaw was found in the new sign, parity, cofinality, and completeness arguments at the reviewed revision. The proof depends on the retained general indexed-Pell anchor, source compilation, factorial fixed-point theorem, prime-power CRT/Horn-flow argument, and named C222/ZF/ZFC calibration. Those are explicitly inherited rather than silently replaced by finite tests. The exact 286-variable coefficient count and all transformation bytes should be attributed to the component's executable verification receipts, not to this mathematical review alone.
