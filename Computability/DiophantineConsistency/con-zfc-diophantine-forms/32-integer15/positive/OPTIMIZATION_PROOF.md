# Three exact circuit simplifications, and a positive transport shift

## Result

At ProveIt commit `8c6eec9d19ef80538c8e61ff6e0180040583446a`, package
`30-quartic31/positive` defines a polynomial in twelve strictly positive
unknowns, of exact degree 1081, with a 111-gate evaluator. The accompanying
three-equation system has 107 gates and residual degrees 7, 2, 1072.

The present evaluator computes **exactly the same polynomial**, with the same
coefficient ports and witness coordinates, in **108 gates**. Its unshifted
system takes **104 gates**. A separate positive-coordinate change gives an
existence-equivalent **103-gate system**. All binary additions, subtractions,
and multiplications, including multiplication by fixed integers, count;
equality comparisons are free, following the upstream convention.

These results improve evaluation costs. They do not lower the variable count
or degree and do not prove any global minimum. The polynomial equivalence is
unconditional over the polynomial ring in the twelve witnesses and four
coefficient ports. Its interpretation as a consistency equation inherits
the upstream whole-tuple compiler and Pell calibration. This is an ordinary
algebraic proof, not a new Lean or Rocq end-to-end certificate.

## Three rewrites

Use all notation in the pinned `POSITIVE12_PROOF.md`. In particular, the
upstream expressions needed here are

    P=Q D v^2, U=Q b^2, HP=H^2 P, HU=H^2 U,
    Knorm=d^2 (W^2-L^2G)^2,
    N=ur^2+Trace ur vr+Knorm vr^2.

1. Share `HQ=H^2 Q` and evaluate `HP=HQ(Dv^2)`, `HU=HQ b^2`.
   The old evaluation of P,U,HP,HU uses six multiplications once Dv^2 and b^2
   are included. The new one uses five. P and U are not needed elsewhere.

2. Evaluate `Knorm=[d(W^2-L^2G)]^2`. This saves one multiplication because
   it needs a product and its square instead of two squares and a product.

3. Evaluate `N=ur(ur+Trace vr)+Knorm vr^2`. This saves one multiplication
   over separately evaluating ur^2 and Trace ur vr.

Each rewrite is a polynomial identity over every commutative ring. Thus the
three output polynomials Nk,Nt,N are unchanged, and so is

    P12=Nk Nt (N+1)-1.

This immediately transfers every zero-set, sign, recovery, and exact-degree
statement in the upstream proof, without redoing any of its estimates.
In particular, any coherent admissible coefficient tuple may be rebound
uniformly: no individual coefficient port is spliced from another tuple.

## Separate 103-gate system

The upstream transport equation is

    (K0+w)C + q-F-z_old(q-1)=1,

where C=q-F-alpha. Substitute `z_old=z+1`. Since q-1 is already evaluated,
the equation becomes

    (K0+w)C=F+z(q-1).

The other two equations are Nk=1 and N=0. Comparing these two transport
sides costs one fewer arithmetic gate than evaluating the old residual Nt
and comparing it with 1. The exact residual degrees remain 7, 2, 1072.

Every positive shifted solution maps to a positive old solution by adding
one to z. Conversely, the upstream soundness argument recovers the ordinary
blank compiler conditions from an old positive solution, including C>0,
q>1, X=wq=2^R, and R>3q. Since alpha and F are positive, C>0 gives F<q.
The bound R>3q gives 2^R>q^2, so w>q>F. Consequently

    (K0+w)C-F>0,

and the old transport equation gives

    (z_old-1)(q-1)=(K0+w)C-F>0.

Therefore z_old>=2, and z=z_old-1 is strictly positive. The shift is a
bijection of the positive zero sets. This is the same transport argument
as the repository's retained59 proof, now applied after the positive12
root-recovery theorem. This shifted system is not silently substituted into
the 108-gate product: that product retains the original witness z.

## Reproduction and proof boundaries

Run `python3 optimize_positive.py`. The program treats the upstream JSON as
inert arithmetic data and emits

- `positive12_system104.json`;
- `positive12_product108.json`;
- `positive12_shifted_system103.json`;
- `OPTIMIZATION_CHECKS.json`.

The checker verifies all four local polynomial identities by exact sparse
coefficient comparison, checks the emitted gate counts, and compares the
old and new circuits at 1000 reproducible signed finite-field assignments.
The finite checks audit implementation; the four algebraic identities prove
the circuit equality. The complete upstream proof is retained as a reference.
No program here tests solvability, consistency, or the unbounded compiler.

## Attribution

The source polynomial, complete reconstruction theorem and separating weight
are package 30's work. The smaller evaluator is a new algebraic refactoring,
prepared with OpenAI assistance. All upstream notices and the repository's
MIT-0 default should be retained in any integrated copy.
