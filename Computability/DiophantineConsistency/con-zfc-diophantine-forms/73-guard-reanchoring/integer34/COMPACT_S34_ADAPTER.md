# A complete compact-tuple adapter for the integer sextic

## Assessment and statement

**The entire compact source44 tuple can instantiate the same 34-integer
sextic.**  This conclusion uses the source44 native compiler theorem and
its explicit canonical parity transfer, together with the coefficient-
independent signed Pell argument of source64.  It is not inferred merely
from matching numerical bounds.  The original source34 instance and its
literal binding remain available and unchanged.

Let S34(beta,K0,MC,MF;v) be the symbolic polynomial defined in
`sextic34.json`, treating the four ports as parameters for this statement.
Let theta_c be the **whole** tuple identified by
`../compact_coefficients/native/COEFFICIENT_BINDING.json`, whose instance is

```text
wang943-complement67-shared-anchor-length8807-prime581197.
```

Its polynomial ports are beta=B-1, K0=K, MC=MC, and MF=MF_source,
with B=2^590069 and MF_source=MF_native+B-1.  Then the inherited ordinary
proofs and the local sextic reduction prove, by mathematics formalizable
in ZFC,

```text
(exists v in Z^34, S34(theta_c;v)=0)
  iff (the literal blank K215 computation halts)
  iff (there is a finite syntactic ZFC refutation).
```

Taking negations gives the requested ZFC-provable consistency equivalence
for the compact instance.  The domain is still 34 unrestricted integers,
and the exact degree is still six.  No new end-to-end formal-assistant or
internally encoded ZFC derivation is claimed.

## Exact documents and bindings

All documents below were inspected at ProveIt commit
`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`.  Their historical source pins
are retained in their unchanged contents and provenance ledgers.

| Document | Local location | Git blob |
|---|---|---|
| Source44 compact native proof | `../compact_coefficients/native/PROOF.md` | `8085a4ca9baca13eea001a3c8537937c5b3f0753` |
| Source44 complete tuple manifest | `../compact_coefficients/native/COEFFICIENT_BINDING.json` | `c54f7f1ce0698a5aad3bf56722c3dde343db6dff` |
| Source36 canonical parity proof | `../compact_coefficients/native/source/coefficients__PROOF.md` | `cd766747a2d3685800842776c3ad7437e4983837` |
| Source64 Q44 proof | `../integer_coefficients/proofs/PROOF44.md` | `a2dd852beca2b9d61e8177d479f475f97448d691` |
| Source64 Q41 proof | `../integer_coefficients/proofs/PROOF41.md` | `56d15933cecaa86cd568d6ab9870e027a2c19eee` |
| Literal Q41 skeleton | `upstream/quartic41.json` | `521f16a310f49e736ea8ffac3fe13847ff71adcb` |

The original repository paths are recorded in
`../compact_coefficients/UPSTREAM_FILES.json` and
`../integer_coefficients/SOURCE_PINS.json`.  The first two proofs are at
`44-b4-sparse/native/PROOF.md` and
`36-small-tuple/coefficients/PROOF.md` within the collection; the latter
appears locally under a flattened source filename to preserve its bytes.

## Complete interface audit

The Q41/Q44 proofs use the following tuple-dependent ingredients.
Everything else in their signed Pell argument is an arithmetic statement
about the displayed residuals and the inequalities derived from them.

| Required ingredient | Compact source supplying it | Consequence for Q41/S34 |
|---|---|---|
| beta=2^d-1 with d>=3; beta>=17 | Source44 §§1,4: d=590069 | Absolute-radix bootstrap and exclusion of negative dyadic q |
| 0<MC<beta, beta<MF<2beta, K0>=0 | Source44 §§4–5, complete literal payloads | The same bounds Q(Q^2-1)<R<Q^4-2 in both signs of q; eventual positive transport quotient |
| Authentic ordinary Pell/native interface, with the same shifted transport | Source44 §7 explicitly gives the seven-equation ordinary-strong system | The Q41 post-power recovery has exactly the source's native arithmetic input |
| Native soundness for arbitrary solutions and arbitrary binary rotations | Source44 §5, aggregate lemma §2, unchanged marked Wang language | Decodes a blank accepting tableau after masks and powers have been recovered |
| Canonical completeness with actual rank tuning | Source44 §6, including its new prime controller | Produces native/Pell witnesses from every finite halt, with the required temporal rotation |
| t=dN odd, q=2^t | Source44 §6: d odd and N a power of odd lambda=581197 | Canonical dyadic exponent has the required parity |
| pc(R)=3t+2 and R=3 modulo4 | Source44 §6 explicitly retains these identities; source36 §6 proves them from the unchanged low congruences and population balance | Exact half-binomial scale valuation and X=2u^2 witness |
| Y=sq^3 with s positive odd | Source44 §6 explicitly retains the odd-scale promises; source36 §6 gives v2(Y)=pc(R)-2=3t | Supplies v_scale=(s-1)/2 in Q41 |
| Ordinary strong multiplier i positive odd | Same canonical parity transfer; source36 §6 distinguishes normalized and ordinary Delta-scaled i | Supplies r=(i-1)/2 in the literal ordinary-strong row |
| R>t and w_source=2^(R-t) divisible by4 | Generic strict rank bound R>3q and odd R,t | Supplies integer w_scale=w_source/4 |
| eta,zeta,F,alpha,C strictly positive and the required exposed quotients integral | Source44 §6 canonical Pell converse and §7 positive ordinary system | Supplies the common-sign guards and literal quotient rows |
| Same literal blank machine and syntactic refutation calibration | Source44 §§3,7 and its pinned inherited marked-language/calibration sources | Transfers the accepting tableau to finite ZFC refutability |

The canonical restrictions are used only to build witnesses from a halt.
They are not imposed on an arbitrary decoded solution during soundness.

## Soundness in detail

Start with a compact-instance S34 zero.  The restoration identities in
`PROOF.md` are identities in the polynomial ring
Z[beta,K0,MC,MF,v], before coefficient specialization.  The common-sign
guard equivalence is also independent of the ports.  Therefore the zero
restores to the Q41 **skeleton** with all four compact ports together.
This is a new coefficient instance of that skeleton, not an assertion
that the original source34 literal numerals changed invisibly.

Write q=beta*J+1, Q=|q|, X=4q*w_scale=2u^2, Y=(2v_scale+1)q^3,
and i=2r+1.  The common-sign simplex and compact mask bounds give

```text
Q>=16,  Q(Q^2-1)<R<Q^4-2,  R>3Q+3.
```

As in source64 PROOF41 §§2–3, the main norm modulo H=4a+3 excludes
X=0.  Thus X>=4Q and |E|>=4Q^4>3R+1.  This rules out the negative
common sign of eta,zeta: the first Pell congruence gives n>R, while the
ordinary strong-rank and signed auxiliary lemmas give p=R with p>n.
None of these steps refers to the native block width, tile labels,
population controller, or the original value d=1064921.

Once eta,zeta>0, source64 PROOF44 §5 applies the signed Pell lemmas using
only the displayed bounds, the ordinary strong equation, and the two
exposed quotient congruences.  It rules out Y<0, recovers the exact main
and first indices, selects the positive main root, and gives X=2^R.
This part is coefficient-independent after the mask-bound bootstrap.

Now q divides 2^R.  The Mersenne sign lemma (source64 PROOF44 §6) for
d>=3 excludes q=-2^t, because -2^t cannot be 1 modulo 2^d-1.  Hence
q=2^t>0.  Since q=1 modulo 2^d-1, division of t by d shows d|t:
if t=ad+r with 0<=r<d, then 2^r=1 modulo 2^d-1 forces r=0.
Consequently q=B^N for the integer N=t/d.  This preserves the native
word-length interpretation for the compact radix.

The same half-binomial and inverse-population stages now recover the
source44 native masks, and the literal transport is

```text
(K0+w_source)C=F+z(q-1),  w_source=X/q.
```

This is exactly the shifted ordinary interface in source44 §7.  Source64
PROOF44 §7 shows z>0 from R>3q; if the old unshifted factor convention
is used, its coordinate is z_source=z+1.

At this point source44 §5 supplies the complete native soundness theorem
for its own DC,DR and mask geometry.  In particular DR=rho^42 is used
with the compact geometry: it is not replaced by source34's DR=rho.
The compact adapter proves arbitrary binary rotation alignment, edge
matching and marked-language decoding.  An accepting tableau is thereby
obtained for the unchanged literal blank K215 language.  Its inherited
calibration yields a finite ZFC refutation.

## Completeness and all parity obligations

Given a finite ZFC refutation, use the inherited calibration to obtain
a finite blank K215 halt.  Source44 §6 pads its marked tableau to a
rectangle with spatial width W and temporal height H, each a sufficiently
large power of the odd prime lambda=581197.  Put N=WH and t=dN.
Both d and N are odd, so t is odd and q=B^N=2^t.

The source44 controller is not inherited by numerical guess.  It proves
the required orders, valuation-one lifting and unit residues for this
specific tuple, and uses Boolean dummy choices to make the **actual**
rank obey

```text
R=dW modulo dN.
```

This is the exact temporal rotation needed by X=2^R; the choices avoid
the origin and all helical seams.  Thus the horizontal/temporal meaning
of dN and dW is retained with the new compact radix.  Source44 §6 then
invokes the same Pell converse to supply positive arithmetic witnesses.

Source44 §6 explicitly preserves the two population/parity identities
pc(R)=3t+2 and R=3 modulo4, and explicitly preserves source36's square
and odd-scale promises.  The mechanism is spelled out in source36 §6:
C=1 modulo4 at the unique Start, the mask populations sum to d, and
MC=2 modulo4 and MF_native=4 modulo8 imply the canonical packed mask
has population t+2.  The two-block packing identity gives pc(R)=3t+2
and R=3 modulo4.  The authentic half-binomial identity then gives
v2(Y)=pc(R)-2=3t, so s=Y/q^3 is positive odd.

The canonical main Pell parameter A is even and c=psi_A(R) is odd.
Taking strong index m=cR yields a positive odd normalized multiplier
psi_A(m)/c^2.  The ordinary multiplier is Delta times that value;
Delta=A^2-1 is odd, so the ordinary multiplier i is also positive odd.
This explicitly matches Q41's ordinary strong row

```text
(i*c^2)^2=Delta*(f^2-1),  i=2r+1.
```

The generic rank bounds give R>3q>t.  Since R and t are both odd,
R-t is a positive even integer and is therefore at least two.  Hence

```text
w_source=2^(R-t) is divisible by4,
w_scale=w_source/4,
u=2^((R-1)/2),
v_scale=(s-1)/2,
r=(i-1)/2
```

are all integers, with X=4q*w_scale=2u^2.  Supply ternary Pos witnesses
for the positive products F*alpha, F*C, and eta*zeta.  The canonical
ordinary source rows, with their exposed quotients, give a zero of the
compact Q41 skeleton.  The local transport pivot, guard reanchoring and
monic eliminations then give a zero of compact S34.

This completes both directions using the entire compact compiler adapter.

## Degree, size and verification boundary

The sextic coefficient of r^2*c^4 is 4, independent of all four ports.
Consequently specializing the compact tuple preserves exact degree six
and the 34-unknown count.  Its four raw coefficient files total
295,388 bytes, compared with 532,479 bytes for the original source34
instance: a reduction of 237,091 bytes (44.5259%).  The compact largest
port has 592,884 bits instead of 1,065,043 bits.  This is a coefficient
size improvement, with the same local polynomial skeleton.

`verify_compact_adapter.py` checks the actual compact payload hashes,
all numerical Q41 tuple hypotheses, the parity/population data, and the
exact source proof identities.  The compact coefficient bundle also
reproduces the complete upstream native finite audits.  These finite
checks supplement the argument above.  They do not turn the inherited
unbounded compiler/calibration proof into a new formal certificate.

The compact binding is a separately identified instance.  The original
`sextic34.json` source34 binding is preserved for provenance and direct
comparison.  The literal compact instance is `sextic34_compact.json`,
emitted by `build_compact_instance.py`; its checker proves that its
unknowns, residuals, restoration identities and exact degree are unchanged,
and checks its four port aliases against the compact manifest.  A
deliverable selecting that instance should identify this adapter and the
compact manifest explicitly.
