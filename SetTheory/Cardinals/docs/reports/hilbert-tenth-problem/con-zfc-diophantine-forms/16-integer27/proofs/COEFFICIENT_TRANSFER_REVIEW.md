# Independent review: parity transfer to the pruned T4 compiler

The 27-integer arithmetic needs more than an unqualified existence
equivalence of coefficient tuples: its canonical witness must have odd i,
square w, and odd auxiliary y. The proposed pruned T4 compiler retains
exactly the sufficient native-interface hypotheses.

## Audited finite input

The receipt `../compiler/pruned_t4_receipt.json` records the following:

- 5268 retained four-site tiles, with fixed Start selector 0 and forbidden
  selector 1 in the coefficient construction;
- `MC=2 (mod4)` and `MF_native=4 (mod8)`;
- native mask populations sum to d;
- dummy coordinates at positive bit positions, and `2DC-DR=3 (mod5)`;
- `b=5^7`, `L=5^10`, `d=bL=5^17`.

These finite checks corroborate the coefficient arithmetic. The compiler
proof must additionally establish that arbitrarily padded blank accepting
tableaux survive the pruning, with spatial width and temporal height
independently arbitrarily large powers of five. The proposed pruning
requires at least two permanently blank, head-free cells along each side;
that is achieved by padding beyond the finite head range. It does not
restrict the availability of arbitrarily large powers of five.

## Transfer lemma

Assume the blank native compiler has its established canonical margin,
population, and actual-rank tuning properties, together with:

1. d is an odd power of five;
2. the padded spatial and temporal sizes are powers of five, so N is odd;
3. the distinguished Start is the low selector, giving `C=1 (mod4)`;
4. positive-exponent dummy tuning preserves those low bits;
5. `MC=2 (mod4)` and the usual shifted mask convention hold.

Then the canonical completeness witness required by the 27-integer
polynomial exists whenever the encoded blank machine halts.

### Proof

Set t_bit=dN, q=2^t_bit, J=(q-1)/(B-1). Then t_bit is odd, q=0 modulo4,
and J=1 modulo4. With `G=q(q-F)-C` the packed rank formula gives

`R=G(q^2-1)+(MC+q MFsrc)J=C+MC=3 (mod4)`.

This is the actual final rank after dummy tuning, because the dummy
exponents are positive and the low selectors stay fixed. This calculation
also follows from the shifted population identity in package14's bundled
`pell_lemma_audit.md`, around its lines502-505.

The canonical power scale is

`w=X/q=2^(R-t_bit)`.

The kernel bounds give R>t_bit, and both exponents are odd. Hence w is the
square of the positive integer `2^((R-t_bit)/2)`.

At the canonical kernel witnesses X and Y are even, so `A0=E+Y+2` is even
and Delta=A0^2-1 is odd. For c=psi_A0(R), the recurrence modulo two gives
c odd. Choose the normalized strong index m=cR, as in package14, rather
than the older 2cR. Expanding `(chi_A0(R)+c sqrt(Delta))^c` shows
`c^2 | psi_A0(m)`: the first square-root term has coefficient c*c and
every higher odd term contains c^3. Since m is odd, psi_A0(m) is odd.
Consequently `i=psi_A0(m)/c^2` is a positive odd integer.

The standard auxiliary converse at this same final rank supplies
`y=psi_rho(R)`. Modulo two the Pell recurrence always gives
`psi_rho(n)=n mod2`, independently of rho. Thus y is odd. For the even
weight M in the new equation, `t=M tau+y` is odd, so it is represented by
the affine integer substitution `t=2r_t+1`.

None of these arguments depends on the number of tiles, the particular
clause-band exponents, or the previous value d=5^67. They depend only on
the preserved native interface and the explicitly listed parity data.
Therefore the 27-integer construction transfers to the new whole tuple
once its pruning/completeness theorem is established. No mixture of
coefficient ports from different recipes is permissible.

## Scope of independent review

This review checks the parity and arithmetic transfer, not every
tile-pruning case. The latter is a separate geometric proof obligation
under audit by the compiler and independent-audit agents. The pure
arithmetic root reconstruction does not use powers-of-five padding;
those choices are needed only for completeness of the signed domain.
