# Compact whole-tuple companion: exact degree and binding

This companion uses the entire package-44 compact tuple, with four port bit
lengths 590069, 592884, 590069 and590070. Its formal source and finite code
are identical to the independently reviewed 86-record positive source.
The coefficient ports are beta, K0, MC and the already shifted MF_source;
the actual binding and compressed integer payloads must accompany this
directory. Individual ports from the old tuple must never be substituted.

The source theorem is uniform in these ports. The compact native compiler
and the old-versus-shifted positive transport adapter identify this whole
instance with ZFC refutation search. The native radix is the fixed number
2^590069. It is distinct from the outer source-packing radix B below.

## Exact source parameters

Every weighted source coefficient has absolute value less than
M=2^1182955. Set a=4096M=2^1182967 and B=a*b^2. The finite source code has
W=100, kernel degrees(1545,1920,1847), convolution height Kcode=2047 and
maximum target2016. Its second-degree kernel has leading coefficient1.
All22,451 exact isolation checks pass.

Use the source registers from the accompanying general proof, with

    N0=B^101, Z=B^2048,
    L=b*B^2149, Gcap=32*b*B^100,
    R=L*(Scode+Tcode+1)-Scode-1,
    c=2^9463725, N=c*b*B^1128.

When b=2^k and B=2^v, v=1182967+2k. The low/high mask population and
two-block carry calculation give

    pop(Tcode)=123v-31k-22,
    log2(L)+pop(Tcode)=2272v-30k-22,
    2log2(N)=2*9463725+2k+2256v=2272v-30k-22.

The last equality is exactly2*9463725=16*1182967-22. Thus the compact
coefficient binding retains exactly the same zero-set proof, with all
calibration constants recomputed. No asymptotic approximation is used.

## Exact degree

All fixed coefficients, including a and c, have degree zero. Substitute a
single variable z for all nine inputs solely to compute the diagonal
leading forms. The important source forms are:

| Register | Total degree | Diagonal leading coefficient |
|---|---:|---|
| U_source |200|a^100|
| G_source |4094|a^2047|
| Scode |4296|2a^2148|
| Tcode |4236|a^2118|
| L |4299|a^2149|
| R |8595|2a^4297|
| N |2257|c*a^1128|

The ratio/norm tail is unchanged. Its exact named degrees are:

| Register | Degree |
|---|---:|
| A |17625|
| D |35252|
| k0 |17627|
| F |141010|
| G |176263|
| H |149605|
| a0 |122942|
| a1 |827998|
| m |70703|
| Omega |88328|
| V0 |61471|
| V1 |413999|
| Delta1=V1^2-64a1 |722242|

These bounds resolve the material cancellation using the exact identity

    Theta^2-Omega^2(a0+64a1)
      =E0^2-2E0*Omega*(V0+V1)
       +Omega^2*((Kratio^2-1)+Delta1+2V0V1),

where

    Delta1=((8D+1)k0^2-64D)(GH)^2+64DF(H^2-1).

The term Omega^2 Delta1 uniquely dominates the inner norm polynomial,
with degree898898. Its square has degree1797796, whereas the final
subtracted term256Omega^4a0a1 has degree1304252. The exact final diagonal
leading coefficient is

    2^186 * a^898488 * c^400 > 0.

Thus the full multivariate total degree is exactly1,797,796. The computation
is not naive propagation through the unexpanded square cancellation. The
separate certificate DAG is polynomially identical to the primary circuit
and exposes the cancellation above. Its finite leading-form certificate
records every needed nonzero head.

Equivalently, the generic formula for this family is

    degree=104 deg(R)+400 deg(N)+8W+316
          =816 Kcode+1224W+5044.

## Exact operation counts and domains

The positive circuit has465 live binary operations:159 additions,
22 subtractions and284 multiplications. Every fixed power is evaluated by
charged multiplications, and fixed numerical scalar multiplications are
charged. Reusing a computed value is free. The witness variables are
b,g,h,s,w,C,i,j,n, all strictly positive. Internally j0=j-1 is nonnegative.

The natural-domain translation has472 live binary operations:167 additions,
21 subtractions and284 multiplications. It shifts all positive inputs by1,
with the internal CRT coordinate equal to its unshifted natural input.
Both domains have the same exact total degree. Neither artifact is an
unrestricted-integer nine-variable equation.

The old-tuple companion has identical formal source data and degree/counts,
but a=2^2134939 and c=2^17079501. These two specializations must be kept
as separate complete coefficient bindings.

## Reproduction and proof boundary

From this directory, `python3 build_nine.py` deterministically generates
the two primary circuits, the two cancellation-resolving circuits and the
exact-degree certificates. Only the Python standard library is needed.
`data/parent_source.json` is the literal new weighted source, not a claim
that its byte hash matches the historical source format.

The mathematical source-coordinate proof is in the accompanying
NEW_SOURCE_PROOF.md and independent source audits. The existing native
compiler and Jones numerical ratio theorem remain explicit semantic
dependencies. This contribution does not prove consistency, establish a
global minimum, export an object-language ZFC derivation, or add a complete
new proof-assistant certificate.
