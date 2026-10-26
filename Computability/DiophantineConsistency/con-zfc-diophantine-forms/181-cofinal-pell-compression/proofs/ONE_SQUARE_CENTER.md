# One scaled square suffices for an even Pell frame

Research scratch note, 25 October 2026. Derived for the current ProveIt iteration.

## Exact statement

For an integer a >= 2 define X_j(a), Y_j(a) by

    (a + sqrt(a^2-1))^j = X_j(a) + Y_j(a) sqrt(a^2-1), j >= 0.

Let W >= 2 be **even**, and let q,M be positive odd integers with every prime divisor of M dividing q. Put n=q+1 and let

    a0 = (n^2+1)/(2n) = 1 + q^2/(2(q+1)) modulo M.

Division here means inversion modulo the odd number M; gcd(2(q+1),M)=1. There exist a positive odd integer k and an integer u such that

    L = X_(Wk)(W+1),
    A = L^2 + 2u^2,
    A = a0 modulo M.

For this same k, A can be made arbitrarily large by replacing u by u+jM. Moreover Y_(Wk)(W+1)/W is an odd positive integer, so the inherited odd frame equation

    L^2 - W^3(W+2)(2z+1)^2 = 1

holds for some integer z. Every constructed center satisfies A >= L^2. No new quantified symbol is required in the final polynomial to record k; k appears only in the existence proof for the already existing Pell-frame variables L,z.

## Proof

The case M=1 is immediate, with k=1. Assume M>1. Write D=W(W+2) and work in the finite commutative ring

    S_M = (Z/MZ)[s]/(s^2-D).

The element e=(W+1)+s has norm one and is invertible, with inverse (W+1)-s. Let the multiplicative order of e^W be 2^r k, with k odd. Then g=e^(Wk) has power-of-two order in S_M. Write g=L+Ys; its coordinates are reductions of the integer Pell coordinates at index Wk.

Fix p^a exactly dividing M, with p odd. Put c=(a0-L^2)/2 modulo p^a. We prove that c is a square modulo p^a.

### Case 1: L = epsilon modulo p, epsilon in {1,-1}

If p does not divide D, the norm relation L^2-DY^2=1 gives Y=0 modulo p. If p divides D, the image of s in S_p is nilpotent with s^2=0. A power-of-two-order element epsilon+Ys must have Y=0 modulo p: raising to its 2-power order gives a nilpotent coefficient equal to an invertible multiple of Y. Thus in either event g=epsilon in S_p.

The kernel of the reduction map S_(p^a)^times -> S_p^times is a p-group: it consists of elements 1+pv, and has p^(2a-2) elements. The element epsilon*g lies in that kernel and has power-of-two order, so epsilon*g=1 in S_(p^a). In particular L^2=1 modulo p^a. Therefore

    c = q^2 / (4(q+1)) modulo p^a.

Since p divides q, the unit q+1 is 1 modulo p. The root 1 of t^2-(q+1) modulo p has invertible derivative 2, so it lifts to a unit root b modulo p^a. Hence c=(q/(2b))^2 modulo p^a.

### Case 2: L is neither 1 nor -1 modulo p

First p does not divide D: in the ramified ring S_p, every power-of-two-order norm-one unit is +1 or -1, by the same nilpotent argument as above. Also Y is nonzero modulo p, and the reduction of g has order at least four. Indeed a norm-one unit of order at most two is +1 or -1 in either the split or nonsplit quadratic algebra over F_p.

The order of e modulo p is divisible by eight. In fact the order of e^(Wk) is at least four and is a power of two, while W is even and k is odd. Taking an even power removes at least one factor two from the order. Choose a power h of e having exact order eight in S_p, and write h=H+Zs.

In the norm-one group of S_p the unique element of exact order two is -1. This does not need a group-size formula: if z=a+bs has norm one and z^2=1, comparing z+z^-1=2a with z=z^-1 gives z=a, so b=0 and a=+1 or -1. Therefore h^4=-1. It follows that h^-2=-h^2. The inverse of a norm-one element is its conjugate; hence the scalar coefficient of h^2 is zero. That coefficient is 2H^2-1, so 2H^2=1. The norm equation H^2-DZ^2=1 then gives

    DZ^2=-1/2, and consequently -D/2=(DZ)^2 modulo p.

Since p divides q, we have a0=1 modulo p. Consequently

    c = (1-L^2)/2 = -D Y^2/2 = (DZY)^2 modulo p

is a nonzero square. Choose this nonzero root; its derivative 2u is invertible modulo p, so the root lifts successively to a root of c modulo p^a. This argument avoids quadratic reciprocity and the order formula for the norm-one group. An equivalent check is that an order-eight norm-one element can exist only when p=1 modulo8 in the split case or p=7 modulo8 in the nonsplit case, precisely where (-D/2|p)=1.

### Completion and odd frame

Both cases give u_p with 2u_p^2=a0-L^2 modulo p^a. Apply the Chinese remainder theorem to obtain u modulo M. Integer representatives u+jM make A=L^2+2u^2 arbitrarily large without changing the residue class.

Finally, Y_W(W+1) is divisible by W because at a=W+1 the recurrence Y_(m+2)=2aY_(m+1)-Y_m reduces modulo W to Y_m=m. Because W is even, a=W+1 is odd. Every X_m(a) is odd. For odd j, Y_j(a) is odd, and the doubling identity Y_(2m)(a)=2X_m(a)Y_m(a) implies v_2(Y_W(a))=v_2(W). Thus Y_W(a)/W is odd. The composition identity

    Y_(Wk)(a)=Y_W(a) Y_k(X_W(a))

and the oddness of k show that Y_(Wk)(a)/W is again odd. All these numbers are positive. Substitution into X_(Wk)^2-DY_(Wk)^2=1 gives exactly the displayed frame equation. QED.

## Application to ProveIt package 166

Immutable snapshot: 02a78a08603cbae248c19c23a75907c6c6bd6443.

The package is

    Computability/DiophantineConsistency/con-zfc-diophantine-forms/166-fixed-base-modular/

Its proofs/TWO_SQUARE_CENTER.md currently proves the weaker center A=L^2+u^2+v^2, by the same odd-order stripping followed by local representation as two squares. Its proofs/FRAME_AND_AFFINE_PROOF.md specifies

    W=2+sum a_i^2,

with twenty-one affine frame atoms. There are two valid applications.

### Generic even frame

To apply the new theorem without a parity hypothesis on semantic data, replace this row by

    W=2+2 sum a_i^2.

This is still a quadratic residual, uses the identical variables, and dominates the old lower bound 2+sum a_i^2. All old frame magnitude inequalities remain valid. Completeness chooses W after the semantic requests, so this stronger frame remains available.

### Preferred application: only shift the frame constant

The canonical completeness construction of package166/proofs/MODULAR_PROOF.md Section10 chooses x even, J even, the actual CRT representative a odd, and the eight other actual CRT representatives even. Consequently its H is odd. Let the nine actual representatives be a_0,...,a_8. The exact list of twenty-one frame atoms in stages/compressed/raw_source.json is

    t, x, y+1, R+t, B,
    a_0,...,a_8,
    N, J, q, D_t, D_y, M_power, BH.

Here M_power=q^x; the modulus of the center theorem is Omega=N*M_power. The constant 2 in the frame is separate from these atoms.

Under the canonical completeness choices, R=16^t and y are even; x and J are even; the seven quantities B,N,q,D_t,D_y,M_power,BH are odd; and the sum of the nine representative squares is odd. The squares of t and R+t cancel modulo2, while (y+1)^2 and the seven odd squares sum to0 modulo2. Thus the sum of all twenty-one atom squares is odd. The frame

    W=3+sum a_i^2

is therefore even for the required completeness witnesses. It dominates the previous frame by exactly one. On arbitrary zeros, W need not be even: this causes no problem because soundness uses only the lower bound A>=L^2, and the new theorem is needed only to construct completeness witnesses. No parity condition is omitted from the polynomial's theorem.

This preferred application changes only the constant term in the literal shared.frame_definition residual, from -525 to -526. All its nonconstant coefficients remain unchanged. The cofinal-center row becomes

    A-L^2-2u^2=0,

and the old free-center variable v has no remaining occurrence. Both applications save one independent integer coordinate before subsequent algebraic simplification. They are zero-existence equivalences, not polynomial identities or pointwise inverses to arbitrary old center witnesses. The entire Pell frame and its common center can be chosen afresh in completeness.

Suggested literal starting point: stages/compressed/raw_source.json, before Horn factoring, monic eliminations and translations. The changing rows have labels shared.frame_definition and free_A.cofinal_constructor. The existing code/build_frame_compressed.py identifies these rows and then runs the inherited exact factor/project/translate pipeline. Endpoint coefficients must be freshly recomputed; the variable-saving theorem does not predict the final support or height.

The target residue in package 166 is M=Omega=N*q^x, q=(BH)^x, N=B^x; B and q are odd and every prime of Omega divides q, exactly as required above. Its other semantic and refutation calibrations remain inherited, and must be retained explicitly in the delivered report.

## Negative controls

The evenness guard is real. Take W=5, q=3, M=3. Then D=35=-1 modulo 3, e=6+s=s, and e^(5k) has scalar coordinate L=0 modulo 3 for every odd k. But a0=1 modulo 3, and 2u^2 is never 1 modulo 3. Thus the theorem fails for odd W with coefficient 2.

The coefficient 2 also does work. For W=6, q=3, M=27, every frame index 6k has L^2=1 modulo 27 because 3 divides Y_(6k)(7) and 3 divides D=48. Here a0=19 modulo 27, so a0-L^2=18 modulo 27. The residue 18 is not a square modulo 27, whereas 18=2*3^2. Hence a single unscaled square cannot replace the two-square center for this frame. The scaled square is not merely the unrestricted assertion that a nonnegative integer is a square.

The special cofinal choice of k is essential. The new result, like the inherited two-square theorem, does not assert that every preselected Pell frame L admits the claimed square correction.

## Attribution and proof status

The finite quadratic-ring and odd-order-stripping setup is inherited from package166. The use of an even frame and the coefficient 2, with the order-divisible-by-eight argument, is the proposed new refinement in this iteration. Literature-wide novelty has not been established. This is an ordinary self-contained number-theoretic proof, formalizable using finite arithmetic and elementary number theory in ZFC; it is not a checked Lean/Rocq proof term. Finite regressions are corroboration only.
