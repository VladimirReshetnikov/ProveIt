# Every periodic target of the directed Toffoli rule has a periodic preimage

This note proves an obstruction to a proposed inexpensive inverse-layer
verifier. It changes none of the published universal or finite-history
certificates. The rule under consideration is the binary CA on Z^2

    F(x)(i,j) = x(i,j) XOR (x(i,j+1) AND x(i+1,j)).       (1)

The six-operation packed Toffoli relation from
`REVERSIBLE_FINITE_HISTORY_MODELS.md` checks this local equation, once
its Boolean and alignment hypotheses have been established. However,
**every totally periodic binary target has a totally periodic preimage
under (1)**. Thus unrestricted periodic-preimage existence for this
rule is the constant-yes problem. Its low local arithmetic cost cannot
replace Life's periodic-preimage hardness theorem with the same
acceptance semantics.

The proof below is an original finite-state argument. It does not rely
on a universality or reversibility assertion about this particular CA.

## 1. Diagonal coordinates and target periods

Suppose a target y has horizontal period p>=1 and vertical period q>=1.
Let K=lcm(p,q). Use coordinates

    t=i+j, s=i modulo K,
    y_t[s]=y(s,t-s).

The last definition is independent of the representative chosen for s:
replacing s by s+K changes the physical coordinates by (K,-K), both
components being target periods. Also y_(t+q)=y_t.

The north and east neighbors of (i,j) lie on diagonal t+1, at positions
s and s+1 respectively. For a K-bit vector z, define

    Phi_t(z)[s] = y_t[s] XOR (z[s] AND z[s+1]),          (2)

with s+1 taken modulo K. A sequence of diagonal rows is a preimage
exactly when

    x_t = Phi_t(x_(t+1)).                              (3)

The direction is important: the row at t+1 determines the row at t,
not conversely. The map Phi_t need not be injective or surjective.

## 2. A cycle closes the required torus

Let

    G = Phi_0 composed with Phi_1 composed with ...
        composed with Phi_(q-1).                      (4)

Thus G sends a proposed row x_q to the row x_0 obtained by applying
Phi_(q-1) first, then Phi_(q-2), and so on down to Phi_0.
This is an endomorphism of the finite set of 2^K row vectors. It has
a cycle: there are z and 1<=ell<=2^K with G^ell(z)=z.

Set T=q*ell and x_T=z. Recursively apply (2) for
t=T-1,T-2,...,0. Since Phi_t is q-periodic in t, this computes
x_0=G^ell(z)=z=x_T. Extend the obtained T rows periodically to every
integer t. Equation (3) holds at the seam as well as internally.

Define the physical configuration by

    x(i,j)=x_(i+j)[i modulo K].                        (5)

Equations (2)--(3) prove F(x)=y at every site. The configuration has
period vectors (K,-K) and (0,T). In particular it has the rectangular
periods

    horizontal H=lcm(K,T), vertical T,
    T<=q*2^K, H<=K*q*2^K.                            (6)

It also has H as a common period in both coordinate directions. These
are computable bounds from the supplied target periods. No assumption
that the preimage has the *same* periods as the target was made.

For example, the constant-one target has no constant preimage: both
constant-zero and constant-one configurations map to zero. But the
checkerboard x(i,j)=(i+j) modulo two maps to the constant-one target.
Here p=q=K=1 and the row map is the flip z -> 1-z, with a two-cycle.
Allowing the period to grow is essential even in this smallest case.

## 3. A bounded generalization

The same conclusion holds for any finite alphabet A and any local
rule which is a permutation of its center symbol when the other
arguments are fixed, provided every other offset (u,v) obeys

    1<=u+v<=d

for some finite d. The north/east rule has d=1. Such a rule can be
solved uniquely for x_t[s] from its target symbol and the future
diagonal rows x_(t+1),...,x_(t+d).

With the same K and target period q, take as state a block of d
successive K-symbol rows. Solving for the preceding row, and shifting
the block, defines a map on A^(K*d). Compose the q phase maps and
choose a cycle of length at most |A|^(K*d). The overlapping rows in
successive blocks agree by construction, including at the cycle seam.
This yields a consistent row sequence with period

    T<=q*|A|^(K*d), H=lcm(K,T)<=K*q*|A|^(K*d).

Thus strict one-sided diagonal dependence plus permutivity in the
center is already sufficient for a computable periodic-preimage bound.
The proof does not assume that the full CA is reversible. It also
does not claim this conclusion for rules whose other arguments occur
on both sides of the chosen diagonal.

## 4. Consequence for the proposed hardness interface

Life's target predicate is different in an essential way. Salo and
Torma prove that existence of a totally periodic preimage of a totally
periodic Life target is Sigma^0_1-complete (Theorem 9, page 16 of
[*Structure and computability of preimages in the Game of Life*](https://www.utupub.fi/bitstream/handle/10024/188843/1-s2.0-S0304397525001756-main.pdf?sequence=1)).
The predicate allows the witness periods to be arbitrarily larger
than the target periods; see `EXPLORATION_LIFE_PERIODIC_PREIMAGE.md`
for its exact finite-witness formulation.

For (1), every target is positive and a witness is found by the
bounded construction above. Hence an encoding into periodic targets
alone cannot transfer that hardness. Additional restrictions on the
preimage could define another problem, but their arithmetic and
soundness would have to be supplied separately. This obstruction says
nothing about forward dynamical universality or about such restricted
preimage problems.

## 5. Exact finite verification

`../verification/explore_toffoli_periodic_preimages.py` enumerates every
binary p-by-q target for 1<=p,q<=3: 682 period presentations in total,
including all 512 targets at p=q=3. It constructs the map (4), detects
a cycle, reconstructs rows in the explicitly stated backward order,
and checks the CA equation at every site of the resulting rectangular
torus. It verifies both seams, all period bounds, and the constant-one
checkerboard example. Period-one or period-two neighbors retain their
proper multiplicities; no distinct-neighbor assumption is used.

The finite receipt corroborates the proof. The theorem for arbitrary
periods follows from the finite-state construction, not from the
small enumeration.
