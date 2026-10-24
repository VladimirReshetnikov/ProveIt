# Expand the transport multiplier and share the direct carrier

This research sibling contains two complete arithmetic graphs: ten strictly
positive integer inputs with 98 operations and exact degree 368 (`zero98.json`),
and ten strictly positive integer inputs with 103 operations and exact degree
340 (`direct103.json`). Both are identically equal to their accepted parent
polynomials at every input, including arbitrary signed integer inputs and
arbitrary four fixed coefficients. This is stronger than an existence-preserving
witness transformation. No previous endpoint, page, emitter or Lean file changes.

## 1. Universal contraction

Use the exact complete accepted definitions in the copied `parents/` proofs.
Write U=mu^2, S=q^3, H=4A-5, L=HI+b, and let g and B denote

    original: g=q-1,    B=Bt, P=S*g, D=0;
    direct:   g=q(q-1), B=B,  P=S*g, D=(q-1)X.

Here `B=B` in the direct row refers to the parent's integer numerator
`(q*K0+X)*C-q*F`, not to the original `Bt`. With W=1+gL, the parent
integer center numerator is exactly

    Zold=P*U*(H*(n+V)+Kpos)
         +H*(U*(gY-S*W*B-D)-P*e).

Replace its private computation of W and W*B by L*B, and replace the
`n+V` operand of H by `n+V-L*B`. The new numerator is

    Znew=P*U*(H*(n+V-L*B)+Kpos)
         +H*(U*(gY-S*B-D)-P*e).

An exact polynomial subtraction gives

    Znew-Zold=H*U*L*B*(S*g-P)=0.

No division, positivity premise, root extraction, selected factor or
modulus cancellation is used. The original graph loses three private
gates `(q-1)*L`, `W=1+(q-1)*L`, `W*Bt` and inserts only the two gates
`LB=L*Bt`, `nVL=(n+V)-LB`. The `q3WBt` name is retained solely to make
the exhaustive row correspondence simple; it now means `q^3*Bt`.
The direct graph has the same saving with `B` and `g=q(q-1)`.

Every other kernel value, Z, M and all four squared arguments of the
weighted octic norm is therefore identical. The entire norm tail is
literally unchanged. By polynomial substitution congruence the output
polynomials agree identically over the integers and over every commutative
ring. In particular both directions of positive completeness use the
identity map on all ten strictly positive inputs.

## 2. An additional direct-base sharing

The accepted direct graph already computes `qbJ=q*(q-1)` for `lowY`.
It computes `P=q^4*(q-1)` in two private gates `q4=q3*q`, `P=q4*(q-1)`.
Delete the former and use

    P=q3*qbJ.

Associativity proves equality at every input, and `q4` has no other
consumer. Thus the direct graph saves two operations altogether.

## 3. Ordinary soundness, chronology and exact degree

The parent ordinary proofs are copied verbatim and bound by SHA-256.
They have been read before this reduction was proposed. Equality of the
complete polynomial means their ordinary unbounded equivalence with a
finite refutation transfers directly in both directions. In particular
the original weighted root noncancellation, sign and transport proof,
strong rank recovery before parity, single-denominator isolation, and
whole-product height projection retain their precise chronological order.
The direct proof still recovers q|X only after projection has removed the
H denominator. Its source reconstruction and positive completeness map
are inherited without modification.

The four fixed payloads are copied together from the accepted original
tuple. Equality is uniform in all four ports, so the ordinary proofs also
retain the separately coherent BFS tuple. No individual substitution of
ports or identification of the original and BFS K0 numerals is involved.

Since each full polynomial is identically equal to its accepted parent,
the exact degree remains 368 or 340, respectively. The parent's symbolic
nonzero leading forms remain the same, not merely a syntactic degree
estimate or a sampled line degree. Syntactic propagation also remains
416 and 384. The degree metadata for the removed W register is omitted;
all other declared register degree bounds are checked directly.

## 4. Scope of literal checks

The independent checker imports no builder, historical emitter or
authentication code. It checks every literal parent row, every retained
and changed operand and every deleted register's complete consumer set;
checks all new rows, topology, liveness, operation counts, domains and
full four-port coefficient bindings; and recursively expands the actual
old and new Z cuts in a free polynomial ring. Its exact cut comparison
licenses the identical complete norm tails and hence the whole-polynomial
equality. The source packets and copied ordinary proofs are fully hashed;
normal and optimized Python runs use explicit exceptions rather than
assertions. Deliberate corruptions must be rejected.

These are universal symbolic checks. No finite input controls are offered
as a proof of the unbounded arithmetic theorem. This packet asserts no
new Lean theorem, internal-ZFC endpoint, consistency result or optimality.
