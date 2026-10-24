# Supplementary ordinary peer: scalar twelve-integer carrier

The independent read of `candidates/scalar-carrier12/PROOF.md` found no
ordinary arithmetic gap. This review supplements the separate full literal
peer in `scalar-carrier12-peer.*`; it does not duplicate that peer's circuit,
coefficient or degree claims. Exact source bytes as read are retained in the
companion JSON. No Lean or native/emitter code was run.

The changes eliminate the main radical and replace its quadratic-algebra
intersective carrier by `Phi_H(H*T+K)`, where
`K=X(X+2ac)-1`, `Phi_H(z)=(z²+3H²)(z³−19H³)` and `S=I*H^5`.
The following dependency order was checked against the actual retained proofs.

1. H is nonzero, Delta>1, delta is nonzero and the affine scale is cubic
   without using a polynomial zero. At I=0 the new norm is Ac^16. Its
   nonvanishing uses the absence of a rational zero of `(x²+3)(x³−19)`;
   it does not assume a remaining main root. Thus I,s,r,c are nonzero.
2. The prime-order separation applies directly to the four normalized
   terms, with squared 3-adic valuations 0,2,4,at least6. The last term
   may initially be imaginary or zero; the lemma is over the multiquadratic
   field and omits a zero term. No sign or gamma is needed. Integer roots
   of the integer radicands and the adjacent-coefficient descent yield
   integral f,tau,g,y. The guard square then yields the two strict guards.
3. The integral factor gives S|Ac. Comparing p-adic orders in the complete
   homogeneous quintic proves H|K. For v_p(z)<v_p(H), the leading z^5
   term has uniquely lowest order, including at p=3,19 or p|I. No cancellation,
   division by a nonunit, or H/I coprimality is used.
4. The strong pair and auxiliary Pell classification recover the omitted
   main ordinate C0=|c| by absolute folding before orienting a or c.
   The inequality C0≤I0 and f>2I0 excludes both wrapping and the negative
   residue. Thus no assumed main projection enters the main classification.
5. The possible even strong multiplier is harmless. C0²|I0 and Pell
   multiplication give C0|m0. More directly, for the auxiliary odd index
   nu=2h+1 write `chi_rho(nu)/rho=Q_h(rho²)`. The identities
   `Q_h(0)=(-1)^h nu` and `C0|rho` give nu=±R modulo C0 from V=-R.
   Folding already gives nu=±p modulo2m0. Hence R=±p modulo C0;
   the pre-projection first-index bounds 0<R,p<C0/2 force p=R.
   This closes the nonodd signed step-down without an old odd-coordinate
   normalization. Root inserted these explicit identities into Section4
   during review. They use no gamma, sign of X or assumed native decoding.
6. The cited signed-bootstrap ratio estimates use only the strict guards,
   cubic scale and recovered main classification. The whole-product bound
   `|H|>2^(2R+2)|X|²` therefore precedes gamma. H divides the *whole*
   product `(sign(c)X−2^R)(2^R sign(c)X+1)`; its absolute value is
   smaller than |H|. Its odd second factor is nonzero, giving the required
   signed power and then an integral restored gamma. This is not primewise
   cancellation under a composite modulus.
7. In completeness, K/H depends only on the canonical outer native
   witness. It is fixed before choosing the strong I,f and remains
   independent of the later auxiliary T. The retained interpolation theorem
   chooses one strong pair first and covers every T residue modulo that
   same I, using the squared-modulus period 4*m*f. Intersectivity of
   pi(T+K/H) therefore supplies the requested residue without changing I.
   The final n is unrestricted and integral. The integral companion uses
   delta*y in exactly the place of the rational companion's y.

The named native/compiler and syntactic-refutation boundary is inherited
from the pinned complete six-coefficient parent. This review does not prove
Con(ZFC), absence of zeros, global optimality or a new internal-ZFC theorem.

The separate helper contains no candidate generator or norm implementation.
It checked exact odd-index polynomial values and constant terms, the monic
homogeneous divisibility conclusion for positive and negative H, roots modulo
all moduli through200, and nontrivial squared-ordinate rank instances.
Normal and optimized Python both passed. These are diagnostics supporting
the unbounded argument above, not substitutes for that argument. The normal
receipt is retained beside this note; the optimized receipt was produced at
`scalar-carrier12-consistency-peer_OPTIMIZED.json`.

The proof pin was refreshed from `48f7a1de...` to
`5c229a688b3ed90f69e97c231c8c5f32afd619447639079083ab752e38f31602`.
Replacing only the new introductory status sentence (checks "pass") by
its former "are in progress" wording reconstructs the exact old full
SHA256 `48f7a1deb42bcd2083e7db2c9d1ed02a05304f000a1895ada8a6dadd5e0343d1`.
Thus the entire mathematical body, source pins and both equations are
unchanged. The independent helper was replayed in normal and optimized
Python, and both retained receipts now pin the final proof.
