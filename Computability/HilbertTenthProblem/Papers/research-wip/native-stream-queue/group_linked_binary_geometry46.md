# A factored coefficient saves one operation in the complete population kernel

The [source](group_linked_binary_geometry46.py) lowers the shared-B
[geometry47 component](group_linked_binary_geometry47.md) to
**46=25M+21A**, and its standalone computed-B form from49 to
**48=27M+21A**. Each keeps all13 comparisons and19 strictly positive
auxiliary coordinates. This is an exact polynomial refactoring with no
coordinate change: every comparison and the complete sum-of-squares
polynomial are identical to their own parent on all supplied tuples.

| Component | Positive parameters | Positive auxiliaries | Comparisons | Certificate M/A | Complete SOS M/A | SOS total | Exact SOS degree |
|---|---|---:|---:|---|---|---:|---:|
| Shared B |q,B,J|19|13|25/21|38/46|84|28|
| Computed B=8q² |q,J|19|13|27/21|40/46|86|28|

The shared component's population interpretation assumes the external
condition **B>=8q²**, using the already proved extension described below.
The standalone source pays two additional products to compute B=8q².
Neither source includes a power-of-two certificate for P, the repunit
equation (B−1)J+1=P, a controller or a universal-input interpretation.
In particular, its86-operation standalone SOS is a component polynomial,
not a new86-operation universal construction. The separate current
universal bounds74 comparison /86 polynomial are unchanged.

## 1. Identity at the actual supplied-k ports

Both authenticated parent variants compute

    X=wn2=w*q, Y=sn2=s*q, E=UM=X*Y, kY=ksn2=k*Y.

Their first comparison is

    (E²+X)*(kY)² = tau*(tau+1).                    (1)

Here k and tau are independently supplied positive coordinates. The
four coefficient gates are E², E²+X, (kY)², and their product L9,
costing3M+1A. Replace only that coefficient cone by

    first_root_base = E*(kY),
    first_next = first_root_base+k,
    L9 = first_root_base*first_next.                (2)

This costs2M+1A. The elementary identity already used in the
[complete74 transfer](complete74_factored_first_norm.md) is

    (E²+X)*(kY)²
      = X²*k²*Y⁴ + X*k²*Y²
      = L²+L*k = L*(L+k),     L=E*(kY), E=X*Y.      (3)

The equalities E=X*Y and kY=k*Y are literal paid definitions, not
comparisons assumed to hold off-zero. The actual operand is **supplied k**,
not R10b=eta+zeta. With every supplied coordinate1, k=1 while R10b=2:
the correct coefficient is2, but substituting R10b in L+k gives3.
Because the unchanged right side is tau*(tau+1)=2, that mistake changes
the complete SOS by1 on this positive off-zero tuple.

No supplied root is translated or renamed. In particular the right side
of (1) remains the original half-binomial expression tau*(tau+1), not
tau²−1 and not a new unit norm. Its two paid gates remain unchanged.

## 2. Complete source and domain preservation

The emitter authenticates the actual parent Python, receipt and proof,
plus the relevant source and proof dependencies. It verifies the saved
binary43 core hash after reversing exactly the original aliases r=J
and n2=q. It checks all first-coefficient producer rows and that each of
UM2, scaled_norm_coefficient and ratio_product2 has only its declared
private consumer and is not a comparison output. New names are fresh;
the comparison output L9 is retained. Every other parent row and all13
comparison pairs remain unchanged.

The standalone prefix remains literally

    geometry_q2=q*q; B=8*geometry_q2.

The nineteen auxiliaries remain

    a,c,d,f,h,i,j,k,o,s,w,tau,eta,zeta,ga,y_aux,
    odd_half,bound_beta,index_beta.

The actual strong square (ic²)², both auxiliary congruences, positive
ratio slacks, oddness condition and both geometry bounds remain in the
source. Computed intermediate quantities may be signed away from the
zero set; their values are identical to those of the old source.

Identity (3) and the unchanged later definitions prove equality of every
comparison operand and residual over any commutative ring. The complete
SOS polynomials are therefore identical as well. Consequently each
source has precisely the same complete supplied positive zero set as
its own parent; no witness projection or canonical-subfamily restriction
is introduced. The population interpretation continues to use strictly
positive integer parameters and witnesses.

## 3. Exact shared-B hypothesis, including the documented extension

The original geometry47 theorem states its positive projection under
B0=8q²:

    J>B0, J odd, q=2^popcount(J).                   (4)

The already reviewed [dilation132 proof, Section2](native_binary_input_dilation132.md#2-geometry-extension-and-exact-exponent-synchronization)
proves the extension to any positive B>=B0. This transfer pins that proof
and checks the essential source fact: B has exactly one consumer,
`geometry_index_bound=B+index_beta`, compared with J.

Given a positive source zero at B>=B0, replace B by B0 and set

    index_beta0=index_beta+B−B0>0.

Every one of the thirteen comparison residuals is unchanged. The original
theorem at B0 proves the population conclusions, while the original
bound at B gives J>B. Conversely, if J>B, J is odd and
q=2^popcount(J), with B>=B0, the original theorem at B0 provides its
positive extension. Its bound coordinate can be replaced by J−B>0,
leaving all other coordinates unchanged. Hence the exact shared
projection is

    J>B, J odd, q=2^popcount(J),   under B>=8q².     (5)

This is a proof transport, not an additional circuit operation, and the
inequality B>=8q² is still an **external obligation** of a containing
source. The component neither computes nor tests that inequality in
shared mode. No weaker domain is claimed here. Its direct equality of
comparison polynomials holds for arbitrary B, but that algebra alone
does not establish the population theorem outside (5).

For the standalone variant, B=8q² is computed internally, so the original
projection applies directly. If separately paid dyadic typing of P and
(B−1)J+1=P are supplied, the original standalone linking proof yields
q=2^t, B=8q², P=B^t with t>=2. These external relations are not silently
included in the46/48 or84/86 counts.

## 4. Fully charged finalizers and exact degrees

The complete scalar output is the literal sum of all thirteen residual
squares. It costs13 residual subtractions,13 squares and12 binary sum
gates beyond the certificate:13M+25A. Thus shared47/85 becomes46/84,
and standalone49/87 becomes48/86. Every source gate reaches a comparison
operand; every finalizer gate reaches its one output. Every parameter
and auxiliary appears in the complete output.

Give each supplied parameter and auxiliary degree one. Shared B is a
supplied degree-one parameter; standalone B is a computed degree-two
polynomial. In both variants the first residual has exact degree14 and
unique highest monomial

    w²*s⁴*k²*q⁶.

All other residuals have degree at most10. The exact residual degrees,
in the unchanged comparison order, are

    shared:     14,3,1,5,4,2,4,6,10,2,1,2,1;
    standalone: 14,3,1,5,4,2,4,6,10,2,1,2,2.

Consequently the full SOS has exact degree28, with unique highest term

    w⁴*s⁸*k⁴*q¹²

of coefficient1. This is stronger than propagated upper-bound metadata.
The checker expands every source polynomial in all its supplied
coordinates over the exact integer polynomial ring. Each complete SOS
has141 monomials; the receipt includes both expansions, variable orders,
residual degree lists and hashes. It compares every old/new comparison
operand, every residual and the entire expanded SOS. No retained equation
or sign assumption is used in this symbolic identity check.

## 5. Reproducible checks and supported interfaces

The [receipt](group_linked_binary_geometry46.json) contains both complete
comparison sources, both complete finalizers, full current interfaces,
literal operation ledgers, the exact polynomial expansions and parent
pins. The implementation uses only Python's standard library and imports
no historical compiler. From the WIP directory, or with an explicit root,
run

```sh
python3 group_linked_binary_geometry46.py \
  --root /path/to/native-stream-queue \
  --expect group_linked_binary_geometry46.json
```

The default root and receipt are the script's own directory and companion
JSON. `--output PATH` writes a deterministic receipt; normal no-argument
execution compares a fresh receipt. Python `-O` is rejected.

Public `canonical_parent`, `build`, `checked`, `polynomial_source`,
`degree_certificate` and `evaluate` require the selected full canonical
packet, use type-sensitive recursive equality, and recheck all pinned
source/proof bytes on every call. `shared_B` and `signed` are exact
Booleans. Returned packets are fresh copies. `evaluate` accepts complete
exact-integer assignments and defaults to strictly positive supplied
coordinates. In shared mode its arithmetic evaluation does not itself
certify B>=8q²; that separate theorem hypothesis is explicit metadata.
Signed evaluation is available for algebra checks. Low-level execution
and sparse-polynomial utilities are not alternative hostile-packet APIs.

The author audit passes52 complete operand identities,26 residual
identities and two complete symbolic SOS identities. It checks384 full
numeric identities, including192 signed cases and32 rational cases;
4,992 individual numeric residual identities;40,128 unchanged register
values;64 shared/standalone B=8q² graph identities;64 exact shared-B
transport identities; and both supplied-k counterexamples. It also
rejects564 malformed packets, six no-op/incorrect parents, eight invalid
positive coordinates and16 invalid mode flags, checks four independent
copies, and rejects two changed pinned dependencies after prior use.

These tests do not construct a complete positive Pell witness or supply
a new computation substrate theorem. The unbounded population and
positive-converse results are exactly the authenticated parent theorem
and its documented scale extension; this packet changes only their
literal arithmetic implementation.
