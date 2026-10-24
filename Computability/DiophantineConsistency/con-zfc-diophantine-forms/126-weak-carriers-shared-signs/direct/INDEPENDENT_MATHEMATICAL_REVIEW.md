# Independent mathematical review of deferred signs and the Pell frame

Scope: this note reviews the new local reductions against the literal
`source/parent.json` source and the corresponding
478-variable variant's typed-frame and joint-guard certificates.
It does not replace the inherited full C222/arithmetic
calibration proof and does not claim a new formal-kernel derivation.

## 1. Deferred factorial signs

The literal first five rows yield, with
`F=fact0.output`, `D=choose0.output`, `V=pow0.output`,
`r=fact0.remainder`, `s=fact0.slack`,

    D = r+s+1,       DF = V+s,

and hence `V=Fr+(F-1)s+F`. The strengthened guard gives `F>=1`;
the retained time guard gives `t>=16` for the derived profile (the
argument also works for `t>=1`). The first requested base is
`n=Ft^2+1>=2`. After independent indexed-Pell recovery and the signed
power congruence, `V=n^t>F`.

The replacement guard `rs>=0` suffices. If either member of the pair
were negative, product nonnegativity would make both nonpositive, so
`V<=F`, a contradiction. This includes the zero-factor boundaries.
Therefore `r,s>=0` and `D>=1`.

The retained `choose0.oslack=o0>=0` and the literal digit-bound row give
`q=D+o0+1>=2`. For the next binomial output `B` and its slack `o1`, the
other digit-bound row gives `B+o1=q-1>0`. Together with the product guard
`B*o1>=0`, this forces both nonnegative. The literal reciprocal row is

    B*i_q = 2 + crt.encoded_index_minus_one + F^2 > 0,

where the encoded-index guard is retained. Consequently `B>0`.

All index-exponent rows were inspected: their exponents depend on the
retained time, factorial, endpoint and encoded-representative guards,
and on the nonnegative label-constructor circuit. None needs a deleted
remainder/slack sign before power recovery. After the powers have been
interpreted, every remaining fused pair has positive sum `q^k-1`; its
nonnegative product recovers both separate signs.

The boundary `F=t=1` gives `n=2` and `V=2>F`, so there is no hidden
strictness failure in the generic lemma.

## 2. Signed comparison base

The signed-base extension is inherited, not a new theorem here. A full
local copy occurs in the incoming quadratic-frames package at
`direct/source/signed_comparison_base_proof.md`, together with
`signed_comparison_index_proof.md`.

Its proof uses the recurrence identities at negative bases, absolute-value
classification, the index congruence modulo twice the common Pell index,
and the short interval `1<=i,k<=Y`. It permits a signed common ordinate
and independently signed comparison coordinates. No division by a
possibly zero residue is made. The endpoint `Y=1` is covered.

For a claim of equivalence to the old guarded source, a possibly negative
comparison progression coordinate is restored by the stated private
comparison-base lift. A negative frame coordinate can be replaced by
`abs(Z+1)-1`; its norm depends only on `(Z+1)^2`. Alternatively, the
semantic arithmetic argument may be replayed directly with the generalized
signed-base lemma. One must not claim the removed private signs become
pointwise positive.

## 3. Additional coupled frame guard

Let `v=shared_index.Vquotient_minus1`, `P=product_i Y_i`, and retain

    Vaux=P^2(v+1).

The already proposed proof separately guards a positive power modulus
to force `A>=2` and guards `v>=0` to force `Vaux>0`.
Both can be replaced by the single nonnegativity predicate

    (A-1)(v+1)^2 - 1 >= 0.                         (G)

For a quartic presentation introduce one quadratic gate `u=(v+1)^2`
and the quadratic guard

    (A-1)u - 1 = alpha^2+beta^2+gamma(gamma+1).

The right side is nonnegative for all integer witnesses. Thus
`(A-1)u>=1`, forcing `u>=1`, `v+1!=0`, and `A>=2`.
Conversely the canonical old completion has `A>=2`, `v>=0`, and
therefore satisfies (G); Legendre's three-square theorem supplies its
three integer witnesses.

The retained positive seed exponents and their retained slacks give
`Y_i>=k_i>=1`, so `P!=0` and hence `Vaux!=0`, with either sign allowed.
Its Pell norm gives

    |U|^2=1+(A^2-1)Vaux^2 >= A^2,

therefore `|U|>=A`. The comparison base is

    b=1+4Vaux(q4+1),       b=A modulo U.

It is congruent to one modulo four. It cannot equal one, since
`0<A-1<|U|` would then be divisible by `U`. Thus `|b|>=3`, even when
`Vaux<0`. Every hypothesis of the signed-base index lemma is available.
The frame norm and `A>=2` rule out `Z+1=0`, and the existing index
congruence supplies the usual huge bound on `A`. No power meaning or
factorial meaning was used to obtain it.

This replaces six private sign witnesses by three guard witnesses and
one square gate. The algebraic raw saving is two variables. The emitter
reports 478 final integer variables, 305 rows, 5,484 quartic monomials and
coefficient height 511,326; those final projection/expansion metrics are
verified by the separate polynomial checker, not inferred from this
local sign argument.

## 4. Typed-frame certificate review

The independent standard-library program `independent_guard_audit.py`,
importing no producer or elimination program, checked
`budget_certificate.json` against its actual
`fused_source.json`. It also reconstructed all 515 transformed source
rows, including the strengthened factorial guard, fourteen product guards,
the joint square/guard pair, private-witness deletion, and all reindexing.
It checked:

- all 31 initial nonnegative facts have actual retained scalar guards,
  and none is among the deleted scalar guards;
- all 163 ordered deductions match an actual monic row and use only
  previously proved signs on odd-powered factors;
- the frame-definition row and guard rows are not used as sign premises;
- all 41 atoms are affine, with 18 certified nonnegative atoms entered
  linearly and 23 others entered as exact squares;
- the collected final frame polynomial is exactly the sum in the
  certificate.

For every integer `a`, `a^2>=abs(a)`; for proved nonnegative `a`,
`a=abs(a)`. Hence `W=2+sum(contributions)>abs(a)` for every requested
atom. The proof is unbounded; coefficient checks verify its finite
application. The new coupled guard's `v` coordinate is absent from the
scalar sign seed list. The collected source hash is
`25f5aa3ebfb59eb667b8a53f44700d4943ff5b2d9a80fb655d2025461d7e1c43`.
The receipt also records 5,260 qualifying factorial-pair cases, 1,680
qualifying positive-sum pair cases, and 6,561 joint-guard assignments;
these are boundary diagnostics, not substitutes for the proofs above.

## 5. Limitations

These checks support the local sign and frame transformations, not a
claim of global optimality, worldwide priority, proof of consistency,
or a newly completed object-language ZFC derivation. The exact final
projection, collected quartic and all upstream source calibrations remain
separate obligations of the complete package.
