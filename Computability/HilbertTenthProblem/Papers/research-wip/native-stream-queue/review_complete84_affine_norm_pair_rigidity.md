# Independent proof challenge: affine norm-pair rigidity

**PASS in the stated field and polynomial-identity scope.** The entire frozen author note `complete84_affine_norm_pair_rigidity.md` was read, SHA256 `eb67b76ac6a5c3150c37cf17c7e062fe6d19eae374adc8c27e8884fdebd58641`. The actual84 row array was inspected inertly, as were the first110 lines of `complete83_input_quotient_dichotomy.md`, SHA256 `46d6457d10d1847cd4241aa1ed6705bf520216fc32cf97891c1f439f6c2c2505`. No saved helper, supplied program, compiler or predecessor was executed/imported. This is a proof challenge, not a numerical search or a new operation bound.

## The generic source field really has four independent norm coordinates

The declared exterior field has15 independent parameters. Together with `eta,delta,rho,sigma` these account for the19 nonfixed source coordinates. Direct substitution checks the displayed rational inverse: in particular `W=q-F-2Z-alpha-(u-inner_bits)`, so its formula for alpha has the correct second Z and input offset. The inverses for J,w,s,x and zeta also restore their actual producers.

The four affine formulas for c,kappa,mu,D then have nonzero inverse denominators Delta,H. Their inverse is valid in the rational function field before any source equation or positivity requirement is imposed. Delta has valuation1 at each of the distinct Y-linear primes `Y(X+1)+1` and `Y(X+1)+3`; adjoining the other algebraically independent exterior parameters does not make it a square. Thus the actual cut satisfies the theorem's hypotheses. This does not supply an integral or positive witness chart for free.

## Factorization, conjugation and the limits of the conclusion

Over the quadratic extension, the two-norm product has four independent, pairwise nonassociate linear factors. The affine map's invertible linear part keeps its four image factors independent and nonconstant. Unique factorization therefore makes them scalar multiples of a permutation of the old homogeneous factors. Their constants all vanish, so translation vanishes as well.

Galois conjugation forces the two factors arising from one new norm to be the two factors of one old norm. The scalar multiplier is a field norm, and the two norm multipliers are reciprocal. This proves the stated classification, including possible pair exchange and conjugation; it leaves no missing cross-pair affine case. If c and kappa stay fixed, their independence excludes pair exchange and forces each remaining center to change only by its own sign. Positive parent roots then exclude negative signs on that zero set.

The example with coefficients depending on c and kappa is a useful explicit limit: the rational center swap scaled by c/kappa does preserve the product, but falls outside the declared coefficient field. Likewise neither nonlinear norm composition nor equivalence only on positive zero sets is ruled out. The theorem does not obstruct an arithmetic circuit computing the original centers more cheaply without changing them.

## A stronger check on the positive difference and its half

The author's polarization formula is exact. With both original norms equal1, an odd integral simultaneous shear has even norm and cannot replace a unit factor while all other parent factors remain fixed.

One can sharpen its subtraction example using the inherited canonical parent indices. Put `A0=a+2`, `v=R-u>0`, and use the usual Pell identities

    chi_A0(n)+sqrt(Delta)*psi_A0(n)
      =(A0+sqrt(Delta))^n.

Multiplication by the conjugate unit gives

    D*mu-Delta*c*kappa = chi_A0(R-u),
    N(D-mu,c-kappa) = 2-2*chi_A0(v).

Both R and u are odd, by the native index and ordinary-input formula, so v is even and v>=2. Pell recurrences modulo2 show that chi at every odd index has the parity of A0 and psi at every odd index is odd. Thus `(D-mu)/2` and `(c-kappa)/2` are positive integers. Their norm is

    (1-chi_A0(v))/2 <= (1-chi_A0(2))/2
      = 1-A0^2 < -1.

Consequently dividing the positive difference pair by2 does not restore a norm-one pair either. This supplements the parity obstruction; it does not exclude division by a different, separately proved common factor, a changed finalizer or a nonlinear chart. The strict index inequalities and canonical input identification are inherited from the pinned source-domain theorem, not assumed for arbitrary independent-gamma83 zeros.

The root receipt authenticates the six author dependencies and the additional input-domain note. No finite sampling or full-polynomial evaluation is used to establish the field theorem or this Pell consequence. The complete84 polynomial, compiler recipe and arithmetic frontier remain unchanged.
