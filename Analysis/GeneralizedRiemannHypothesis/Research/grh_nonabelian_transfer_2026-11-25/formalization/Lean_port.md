# Lean implementation plan (not compiled)

No new Lean proof is included or claimed compiled. This document separates exact finite arithmetic from algebraic interfaces and the still-missing quantitative hypotheses.

## 1. Exact certificates

Formalize the Gram matrices and column lists from `certificates/frame_certificates.json` over Z or Q. The central finite equalities are:

- `G * C = 229 • I`;
- `C = sum_i m_i • outer(u_i, u_i)`;
- `det G = 229^3` for the S3 field;
- the cubic analogue with `det T = 229`.

A ring-normalization proof or finite integer decision procedure should suffice. Do not use a floating optimizer as a proof oracle.

Then prove the generic matrix implication: if an invertible embedding matrix B obeys `transpose B * B = G`, these identities imply the frame resolution `B * C * transpose B = 229 • I`. Number-field identification of B is a separate theorem.

## 2. Projective Hermitian identity

Use the convention `h` conjugate-linear in its first argument. Define `theta x y z = x * h y z` (scalar multiplication in an abstract module), and `rankOne v = theta v v`.

Given finite dual generators with `sum theta x_i y_i = id`, use adjoints to obtain the reverse identity. For an integral scalar eta with `eta + star eta = 1`, establish:

`rankOne (x + eta • y) - rankOne x - norm(eta) • rankOne y`

`= star(eta) • theta x y + eta • theta y x`.

Summing gives a signed INTEGER identity. Projective duality and self-duality are used to keep every generator inside the lattice. Do not silently assume a free integral basis.

## 3. Positive reserve and arithmetic saturation

Formalize a reserve certificate independently from how it is obtained:

- finite vectors v;
- positive integers c_v and q;
- integers z_v;
- `sum c_v rankOne(v) = q • id`;
- `sum z_v rankOne(v) = id`.

For any lower multiplicity R, use the explicit threshold with equation label `eq:explicit-threshold` in the report. Euclidean division `M=k*q+r` gives coefficients `k*c_v+r*z_v`. This finite lemma can be proved before formalizing Hermitian LDL decomposition.

## 4. Arithmetic tower

Build F as the splitting field of `X^3-4X+1`, its quadratic subfield k=Q(sqrt229), and the CM tower E0=K Q(zeta_q), E=F E0.

Prove inertia at229 has order2, hence F/k is unramified. Use base change and different transitivity to obtain `different(E/E0)=1`. Extend A0 to A and apply Hermitian trace-dual ideal arithmetic.

Reuse the upstream theorem:

`New.nonempty_weilData_of_not_dvd_differentIdeal`

in `grh/src/Lib/ClassField/Grunwald.lean`.

Retain the old finite idele in this unramified special case. Preserve period normalization by choosing compatible roots, or prove equality of all relevant norms up to a root of unity. Do not assert equality of independently chosen principal complex roots.

## 5. Keep the unfinished estimates explicit

The qualitative frame theorem does not discharge `h <= b`, prescribed final level, or vector-size assumptions uniformly in the growing field. The source odd-cocycle theorem assumes cyclotomic containment and cannot be instantiated with E. Its modules are raw cocycles with special local conditions; no replacement by a standard cohomology group is justified without a comparison theorem.

A future end-to-end Lean result must carry those missing statements as hypotheses until they are actually proved. No file in this package presents them as axioms of a purported unconditional nonabelian GRH proof.
