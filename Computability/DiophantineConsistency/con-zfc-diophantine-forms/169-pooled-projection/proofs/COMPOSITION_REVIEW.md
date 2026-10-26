# Independent audit: linear CRT source with pooled powers and strict ranges

Prepared 25 October 2026 within the AI-assisted research workflow.

## Scope and verdict

The proposed composition of source 157's factorial-free arithmetic source
with source 158's strict-range transformation and two-row pooled-power lemma
is mathematically valid. The concrete 235-to-223 pooling stage also passed
the independent exact frame and residual checks in Section 5. Earlier source
edits and later projections have their separately identified certificates.
This audit is an ordinary mathematical review, not a new
proof-assistant derivation and not an external human referee report.

The inspected proofs are source 157 `proofs/MAIN_PROOF.md` and
`proofs/INDEPENDENT_DERIVATION.md`, and source 158 `proofs/POOLED_POWERS.md`
and `proofs/STRICT_HORIZON_AND_BETA.md`, at ProveIt commit
`953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4`.

The following source 157 choices remain intact:

    t = 16 + 4d^2, F = t^t, R = F, C = 2c,
    H = 2 + 4(C + A1 + ... + A8), y = F(2v+1).

The three power requests producing F=t^t, N=B^x and q=(BH)^x remain
individual. Pool the eleven requests at q+1 and the three retained requests
at q. The latter must include the request with exponent y+1. Tighten only
the five binomial lower indices for the four schema parameters and the
derived label, from t+1 to t. The exact B digit and encoded-index range
already use t. Source 158's separate factorial-dependent change y=V-1 is
not part of this composition.

## 1. The pooled-power estimate works for signed and unit bases

Assume W>=258, |A|>W^W, n!=0, and n^2,m_i^2,k_i^2<W for at most 15
requests. Let (X_i,Y_i) be the canonical signed-index Pell pair at A and
k_i and Z_i=A Y_i. Set

    D_i=m_i-X_i+Z_i,
    H0=sum_i Y_i(m_i-X_i),
    S=sum_i(D_i^2-Y_i^2),
    T=2An-n^2-1.

The polynomial identity

    sum_i(D_i-nY_i)^2 = S-2nH0-T sum_i Y_i^2

follows by direct expansion, using only Z_i=A Y_i. The two proposed rows

    K-2H0-(2A-n)L=0,  S-nK+L=0

give S-2nH0=T L, and therefore divisibility of the left side by T.

Because T=-1 modulo n, n is invertible modulo T. The signed Pell
congruence is consequently valid even for negative k_i. Put
b=floor(sqrt(W-1)). Multiplication by n^b gives divisibility by T of

    E=sum_i(m_i n^b-n^(b+k_i))^2.

Every exponent is now nonnegative. Since b>=16 and each absolute atom is
at most b, each squared summand is at most 4b^(4b). Thus

    0 <= E <= 4r b^(4b) < W^(2b+1) <= W^W < |T|.

The strict middle inequality uses 4r<=60<W and b^2<W. The last uses
|T|>=2|A|-W>W^W. Hence E=0, proving all exact powers. If |n|>=2,
negative k_i would imply m_i n^(-k_i)=1, impossible over integers. At
n=+/-1 the signed-index unit powers are correct without forcing k_i>=0.
The converse follows from the same congruences, with
L=(S-2nH0)/T and K=2H0+(2A-n)L. Neither quotient is inserted as an
operation in the final polynomial.

## 2. Noncircular bootstrap for the combined source

The first retained individual request gives F=t^t, so F is positive and
even, and F>=2^64. The equation B*h_B=C+F+1 has an odd right side;
therefore B is odd and nonzero before any representative sign is known.
The literal H is 2 modulo 4, so |H|>=2 and |BH|>=2. The retained BH
request gives x>=0 and q=(BH)^x.

The unchanged y=F(2v+1) gives |y|>=F. Therefore
|1+(t+1)y|>1. If x=0, the terminal endpoint
x=1+[1+(t+1)y]u_t would make this integer divide -1, a contradiction.
Thus x>=1 and |q|>=2.

At precisely this point the q pool is licensed: its base is nonzero and
its exact signed frame is already available. Its y+1 request implies
y+1>=0. A negative y would have y<=-F<-1, so y>=F>0. The first endpoint
x=F+1+(y+1)u_0 excludes u_0<0 and gives x>=F+1. The terminal endpoint
then excludes u_t<=0 and gives x>=2+(t+1)y. Consequently
|q|>=2^x and |q+1|>=2. The q+1 pool now proves nonnegativity of all
requested representative exponents and the required derived exponent.
H becomes positive. The signed-digit argument of source 157 recovers
B=binom(F+t,t)>0 and hence q>0.

The order is therefore retained individual powers, raw parity/nonunit
bootstrap, q pool, endpoint bounds, q+1 pool, and binomial interpretation.
There is no assumption that q or B was positive in the first pooled step.
Removing q^(t+1) does not affect this bootstrap: its sign and size inputs
come from q^(y+1) and the endpoints, not the deleted ratio.

## 3. Strict ranges and cofinal completeness

Choose a finite calibrated proof tree first. List its rule parameters and
the full local derived-label expression for every used tuple, including
unused branch codes in that expression and the fixed truth-padding tuple.
Choose t=16+4d^2 strictly larger than this finite list and the number of
rule-expansion steps. This is possible by cofinality. Compute F=t^t only
after choosing t. Hence all intended local values lie in [0,t-1].

Source 157's spacing construction still chooses an arbitrarily large odd
multiple w of the odd part of t!, and puts y=Fw. Since v_2(F)>=2t>
v_2(t!), t! divides y. Enlarging w bounds every pending accumulator.
The usual beta moduli remain pairwise coprime. This construction requires
no use of source 158's factorial-specific V-1 spacing.

For any full prime power p^e in the range modulus N=B^x, e>=x. The
precision-2x CRT construction gives each relevant global representative
a the residue w in [0,t-1] modulo p^(2e). If a<t, binom(a,t)=0.
Otherwise the numerator of binom(a,t) contains a-w, while
v_p(t!)<=t-1<x<=e. Thus p^e divides binom(a,t). Polynomial congruence
gives the identical conclusion for the derived label. These are exactly
the five tightened range tests. In soundness the inherited range lemma
now yields strict local bounds, which imply all former weak bounds.

All seven t-based normalized remainders may therefore share the ratio
M/q^t. The deleted q^(t+1) request used a derived pair rather than an
independent principal anchor. Removing its private output, quotient,
discriminant wire and ratio leaves the principal signed orientation family
unchanged.

## 4. Required finite bindings

The mathematical composition depends on a literal identity

    W = 2 + sum_j atom_j^2,

not merely on the weaker consequence |atom_j|<W. Every retained actual
base, index and output must occur among these affine atoms. In particular
check actual BH, t, F+t, y+1, all q and q+1 outputs, and centered coordinate
offsets. Removing the square of the deleted q^(t+1) output is permitted;
omitting a retained actual atom is not. Keeping a redundant t+1 atom is
harmless. Since t>=16 remains present, W>=258 remains available.

The signed Pell-frame and semantic-anchor argument must continue to give
|A|>W^W and canonical signed pairs before arithmetic sign recovery.
Changing the finite family of requested powers does not license replacing
that argument with sampled Pell tests. Retain the complete incoming
ordinary proof dependencies and identify the exact inherited C222/ZF/ZFC
syntactic calibration.

The source edits, private-slot deletions, frame identity, per-request atom
coverage, pool residual identities and every subsequent integral projection
must be checked against the actual emitted coefficient data. This note
does not identify finite checks with the unbounded argument above.

## 5. Actual independent finite checks

The standalone `check_composition_binding.py` imports no producer or
optimizer. It was written separately from the composition builder. It
reconstructs the exact squared frame from the semantic affine atoms, then
compares every coefficient of that identity with the actual source row.
It checks all 17 actual base/index/output triples, including the duplicate
t growth-base slot, the actual C=2c representative, F+t, y+1 and BH.

It additionally reconstructs the raw parity-safe bootstrap equations and
all three retained individual power congruences. For each of the 14 pooled
requests it checks the actual former modulus, congruence, A*Y row, Pell norm,
and output coordinate. Crucially, it also reconstructs the retained
14-pair canonical-index aggregate as

    sum_j [(X_j-1)^2+(Y_j-k_j)^2]-(A-1)Q,

and compares it coefficient by coefficient. Thus the semantic index labels
are checked against the actual orientation/recovery row rather than merely
declared in a frame metadata list. All affine offsets are accounted for.

The checker independently constructs the two pooled rows per base and
compares all 160 emitted residuals, including every unchanged residual,
under the full coordinate map. It verifies the deletion of exactly 16 old
modulus/quotient coordinates and introduction of four new pool coordinates,
giving 235-16+4=223 coordinates. Corruptions of the frame constant, a signed
Pell coordinate offset and an emitted pool coefficient are all rejected.
Both normal and optimized Python runs passed; the checks use explicit
exceptions, not assertions.

The exact audited inputs have these SHA-256 identities:

* Before pooling, `basis235/equation.json`:
  `d5ebe63b6ccb44141d3a3128e8e943e87ac566ef1889b84809f41181335f16cb`.
* Emitted `pooled223/equation.json`:
  `82abe2d0f9da7ae81f0092bf02c040cf4528990fb4fc72e6da63ed0a86bb2bd0`.
* The exact pool certificate:
  `f21ad8fd8b93437c060bcd9fa76d5be32f1e22b75181c779bb54c9f96d06a6e2`.

Receipts are `COMPOSITION_BINDING_CHECK.json` and
`COMPOSITION_BINDING_CHECK_OPTIMIZED.json`. These runs do not rebuild the
inherited Lean closure, prove the unbounded Pell-frame theorem by finite
computation, or independently certify every earlier source and later
projection stage. The semantic proof uses the retained, named inherited
theorems; other finite stages have separate exact certificates.
