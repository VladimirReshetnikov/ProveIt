# Independent review of the round-8 local adapters

Reviewed files and their exact hashes are recorded in
`NEW_LOCAL_ADAPTER_CHECKS.json`. This review does not import or execute
received programs and does not certify an unbounded compiler theorem by
finite testing.

## 1. Conditional radical weights (1,b,b)

The proof in `../integer/CONDITIONAL_SEPARATOR_PROOF.md` is valid on
independent inspection. In particular, its new bound does not assume
the two square predicates it is intended to recover.

The required order is:

1. The exact eight-factor norm identity and nonvanishing quintic exclude
   Sigma=0. The homogeneous norm divided by Sigma^8 is a monic integer
   polynomial with rational root m-Theta/Sigma. Rational-root integrality
   therefore gives Sigma dividing Theta and a rational signed radical sum.
2. If |b|>1, the coefficient of any nontrivial signed squarefree class of
   r0 would have to be an integer multiple of b. This contradicts
   gcd(b,J)=1. Negative radicands cause no problem: distinct signed
   squareclasses remain independent over the rationals in a multiquadratic
   extension. Zero is already a nonnegative square and is separately
   excluded afterward.
3. For b=1, f=0 and r0=1-4z^2 is odd and negative, while r1 and r2 are
   divisible by four. In any common nontrivial radical class its coefficient
   is odd and the others are even, so cancellation is impossible. The case
   b=-1 is unavailable because b=1 modulo three.
4. Recovering r0 square gives b a positive square and O>0, hence f,l are
   nonzero and Delta>0. Only now is the source's implication cap>0 used.
   Delta>0 excludes K=0 and g<=0, then gives 0<g<2cap. Only now are the
   source lower bounds X>=1 and Y>=2 invoked.
5. Consequently |L|>=2, |U|>=4, V is divisible by four, |A|>=4 and C is
   odd. Delta>0 also gives K^2>4g(C-KL)^2, hence
   |C|>|K|(|L|-1/2)>|K|. The elementary inequality
   |V|<=(V+1)^2 holds for every multiple of four, including zero and
   negative multiples. Thus |Pn|<=A^2 and
   r1<=A^4 K^2+4<A^4 C^2+4.
6. Independently of the sign of r1, D>=A^2>=16, E^2>=C^2,
   F>=A^2 C^2+1, and I>=1 because G is odd. Hence
   r2>=A^4 C^2+A^2>A^4 C^2+4>r1. These estimates require neither a Lucas
   classification nor r1 or r2 square.
7. After subtracting the integer first radical, the remaining rational
   signed sum cannot vanish because r1 differs from r2. The elementary
   two-root rearrangement makes both roots rational, hence integer. This
   recovers exactly the old finalizer's three square conditions.

The converse follows immediately: the old square and divisibility
conditions make every signed weighted root sum integral, and m can be
chosen to annihilate one norm factor. All ten coordinates are unrestricted
integers, so no additional sign restriction on this m is needed.

The proof correctly retains its source-interface condition. It is not a
valid arbitrary-radicand relation-combining formula. The bridge still uses
Sun's ten-integer theorem and the inherited source/compiler calibration.
Exact norm expansion, the Delta regrouping, the factored G identity, and
the modulo-four radicand statements were independently checked as ring
identities by `check_new_local_adapters.py`.

## 2. Twelve guarded source coordinates

The proof in `../source/SELECTIVE_POSITIVITY_PROOF.md` is also valid on
independent inspection. The exact pinned parent JSON has the transport
identity `(K0+w)C=F+z*beta*J`, not a silently exchanged source45 variant.
All 22 displayed source rearrangements were independently reconstructed
from its literal arithmetic DAG and verified symbolically.

The recovery is noncircular. Positivity of F and K0+w first forces C>0.
Then q=F+alpha+C>=3 and q=1+beta J force J>0. The remaining defining
quadratic rows successively force L,N,X,Y,E,a,Q,c,T,P,tau,D,Delta,C2,I
and Baux positive. The strong row gives F2>1, and f^2=F2 with f natural
gives f>=2. Finally y^2=Baux*g+1 with Baux,g positive gives y>0, while
V^2=(Baux-1)g+1>=1 and V natural give V>0. The row of=V+c then gives
o>0. Every one of the nineteen unguarded old coordinates is covered.

The argument needs only beta,K0>0; MC and MF do not enter its positivity
steps and may be arbitrary integers. It neither assumes a refutation
witness nor calls a Pell-rank result. The inverse map subtracts one from
exactly the twelve guarded coordinates, so it proves a literal bijection
between the two zero sets, not only equisolvability.

The independent affine expansion agrees with every published term and
factorial-weighted coefficient: 109 coefficient records, 62 active
monomials. The second row at the all-zero natural tuple is -1, confirming
the nonzero-source requirement. None of these facts alone establishes a
smaller numerical packing instance; a separately checked weight/target
certificate is still necessary.

## 3. Authentic native rank phase for the squared-modulus quotient

The new complemented-receiver tuple retains the stronger phase
R=3 modulo four. This is not inferred merely from an odd clock or the
bound R>3q.

For the canonical native witness, let B=2^429959, q=B^N and
J=(q-1)/(B-1)=1+B+...+B^(N-1). Then q=0 and J=1 modulo four.
The independently reconstructed mask has MC=2 modulo four. The unchanged
native origin condition is

    (C-1) AND (MC*J+1) = 0.

Its mask has both low bits set, so C=1 modulo four. With

    G=q(q-F)-C,
    R=G(q^2-1)+(MC+q*MF_source)J,

one obtains G=-C and R=C+2=3 modulo four. The already-shifted convention
for MF_source does not affect this residue because q=0 modulo four.
The native source explicitly states the same phase near the end of its
completeness argument; the algebra above independently explains it.

The padding controller changes the actual rank while preserving native
origin disjointness and the canonical masks. Therefore it does not break
this phase. The population formula and oddness of d,N provide additional
rank information, but are not substitutes for the displayed low-bit proof.

Consequently the new tuple is compatible with the squared-modulus
completeness reconstruction requiring R=3 modulo four. It is unnecessary
to retain the older tuple merely for this phase. This statement concerns
authentic native witnesses supplied by the inherited compiler theorem,
not arbitrary assignments to the four coefficient ports or raw variables.

## 4. Interior-padding sparse source and exact-popcount bridge

The source-parametric proof in `../integer/SPARSE_SOURCE_PROOF.md` passes
independent review, including the changes needed when the padding exponent
is not zero. The exponent for a degree-d source monomial is
`(2-d)p+sum(alpha_i*w_i)`, so the square of `B^p+g` retains the same
factorial extraction identity. Merely reusing the padding-zero exponent
formula would have been wrong; the new proof does not do that.

The supplied source coefficient bound C0 is an absolute sum, not an
unjustified maximum after packing collisions. At B>C0, a positive integer
leading coefficient therefore gives D(B)>0. The gap `K>=max(H_j)+2`
provides enough room for sparse padding and the mask. Before binary-base
recovery, the proof establishes nonnegative Scode,Tcode and the strict
bound Scode+Tcode<N. Thus the two-block complement/popcount identity is
used under its actual hypothesis.

One intermediate bound deserves its full justification: since targets
are distinct nonnegative integers at most K-2,

    Z <= (B^(K-1)-1)/(B-1),
    (B-2)Z < B^(K-1).

The second inequality does not follow from the weaker displayed bound
Z<2B^(K-2) alone, but it does follow immediately from this geometric sum.
No correction to the final estimate is necessary.

The signed-borrow induction is sound: every incoming carry is -1 or0;
at a target the normalized digit is0 or1 exactly when its formal source
coefficient vanishes. The ordinary binary interpretation is justified
by the already-established positivity of Jcode. The source coefficient
at a marked exponent is2r_j, and Jcode doubles it again; this harmless
factor four preserves the zero predicate.

The mask population calculation correctly removes31 binary k-bit fields
and adds22 high fields of width v-1. It yields the exact threshold
`Y=2^(e*Hpop+1-22)*b^(2*Hpop-31)`. The short division-free form uses
`Yscale=2^(16e+1-22)` because its remaining factors contribute
`B^(Hpop-16)*b`. The polynomial exponents agree exactly. The modulo-three
test for X is proved with arbitrary b=1 mod3 before b is known to be a
power of two, avoiding a potential circular premise.

For forward completeness, both unshifted coordinates D and Delta are
strictly positive at every source zero. Their positional weights are
distinct; at least one is positive. Therefore the packed g is at least B,
not merely nonzero, giving the required g>=b. Choosing b among arbitrarily
large powers of four preserves b=1 mod3 and gives g<cap. The interior
padding does not change this digit argument.

`check_new_local_adapters.py` independently rechecked all nine supplied
selective12 positional certificates, including every one of the57552
source-term/possible-square-pair interactions per certificate. Each has
exactly109 intended target hits, distinct nonnegative reversed exponents,
a positive leading coefficient, and the required sparse-padding headroom.
The170 shifted packed instance has padding169, maximum weight170,
Dmax4086, K4426, and headroom134. This check rebuilds the coefficients
from the pinned source, rather than trusting the certificate's expressions.

## Verdict and boundary

No local error or missing sign/bootstrap premise was found in either new
adapter or the adapted sparse source. The native phase needed by the short-circuit composition is
preserved. The check receipt records exact local algebra and source data,
not a new Lean/Rocq proof, not the inherited unbounded compiler semantics,
and not a proof of ZFC consistency.
