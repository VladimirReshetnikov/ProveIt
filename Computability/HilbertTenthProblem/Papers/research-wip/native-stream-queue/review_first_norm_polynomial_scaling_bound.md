# Independent review of arbitrary polynomial scaling of the first norm

**PASS.** Every nonzero polynomial multiple of the first norm needs at
least three multiplications and at least two additions/subtractions at the
six stated dependent paid ports. This is a local arithmetic obstruction;
it neither lowers nor establishes optimality of the complete84 circuit.

## Reviewed artifacts

| File | SHA-256 |
|---|---|
| `first_norm_polynomial_scaling_bound.py` | `489f1e8eb0cb083b83c4d33106519285f3039a5be1f3ddd2415a162bfee5e489` |
| `first_norm_polynomial_scaling_bound.json` | `73ea33544ec5aebda57f50b523e8343f4420f15d7c31c47a5f75ac5d1f3af564` |
| `first_norm_polynomial_scaling_bound.md` | `ade14fbd609acc0b9aff5b559fbe31e1527057afb2265b94a24cb9dffb978ca3` |

Root read the complete new proof and helper, the complete monomial-scaling
predecessor proof, the complete84 companion and its literal84-row array.
The seven predecessor pins in the fresh helper authenticate only inert
bytes; no predecessor program was imported or executed. The receipt was
reproduced by fresh normal and optimized runs from `/`.

## Mathematical challenge

The multiplier quantifier is correct: G is nonzero in Q[T,X,Y,k], after
imposing E=XY and Z=kY. A formally nonzero expression in six independent
letters which becomes zero under those dependencies is not an allowed G.
The multiplier is not furnished as a new paid input.

For the multiplication bound, choose a coefficient at the maximal
(T,X,k)-degree of G. A nonzero rational t outside its finitely many roots
and outside0 makes specialization Y=t preserve that degree. This handles
multipliers that vanish identically at Y=1. All six initial ports then
become affine in T,X,k. A two-product circuit with unrestricted affine
operations has degree at most4, so any surviving nonconstant G is excluded
by degree additivity in the polynomial integral domain.

If G depends only on Y, its surviving specialization is a nonzero scalar.
The proof correctly supplies the missing quartic argument rather than
using degree alone. The most general second-product circuit is

    h(alpha Q+u)(beta Q+v)+bQ+z,

with Q the first affine-by-affine product and u,v,z affine. The quartic
part forces Q's linear factors to have directions X and k, so Q has no T
term and is qXk+rX+sk+z0. At X=0, the quadratic part must be a nonzero
multiple of T². Both second-product linear parts are therefore multiples
of T, forcing their pure-k coefficients to vanish. Their general product
then has no Xk² term. The required coefficient is -t², which is nonzero.
The arbitrary rational scalar and nonzero t do not alter the contradiction.
This proves M>=3 even after granting all affine operations for free.

For the addition bound, with one addition every subsequent value is a
scalar monomial times a power of its one binomial. The six initial ports
really are monomials at the declared boundary. P is irreducible because
the radicand of its monic quadratic in T has odd valuation at X. Since
P is prime and is not a monomial factor, any representation of GP in that
one-addition form would force P to divide the binomial.

The support-width argument excludes that divisor without a restriction on
G's factors or multiplicities. The three support exponents of P span a
two-dimensional affine space. A rational weight orthogonal to the binomial
support difference but not to all P support differences gives zero width
for the binomial and positive width for P. Widths add under polynomial
multiplication: highest and lowest weighted homogeneous parts cannot
vanish on multiplication over a field. This yields the contradiction even
with signed coefficients, cancellation inside G, or P dividing G.
Thus A>=2 independently of the number of multiplications.

## Actual circuit interface and evidence

The literal mapping is T=tau_root, X=wn2, Y=sn2, k=R10b, E=UM, Z=ksn2.
The two retained paid products and all five component rows match the saved
complete84 source. Their expansion is exactly

    P=T²-X²Y⁴k²-XY²k².

The fresh helper checks this source binding, the three-term support and
its nonzero rank-two minor, the odd radicand valuation, and the general
second-product coefficients. Its twelve multiplier examples illustrate
specialization, including G=P, G=P² and examples vanishing at Y=1. They
are corroborating calculations, not an exhaustive search or the proof of
the quantified theorem. No additional independent checker is claimed.
Root's independent evidence is the complete proof challenge above and
fresh normal/optimized execution of the reviewed helper.

## Scope

For a nonvanishing multiplier on the relevant positive domain, replacing
P by GP and the final offset Delta by G*Delta would scale the whole
polynomial. The theorem charges computation of GP at this six-port
interface; it does not make the new offset or other factors free.
Computing the isolated first factor cannot save an operation by any such
polynomial scaling. Extra paid registers, joint factor computations,
rational functions, altered coordinates and identities confined to a zero
set remain outside this theorem. The established universal bound remains
84=47M+37A with18 positive witnesses and exact degree187.
