# The numeral cost of the present 106-operation presentation

This note concerns only numeral construction for the current base-four,
shifted-parameter presentation. It is not an optimality claim for other
polynomial systems or algebraically equivalent certificate schedules.

The compact support has

    K=316719071,    3K+2=950157215.

The present core needs the fixed small numerals

    2, 3, 4, 8, 15,

and a fixed exponent L greater than `3K+2`. Literal 5 has already been
removed without changing the core operation count by computing
`a_plus=a_minus+2` instead of `a_plus=a_0+5`.

## Nine operations suffice

Starting with 1, the following nine integer arithmetic operations generate
every required numeral and the admissible exponent `L=2^32`:

    2=1+1,
    4=2*2,
    16=4*4,
    256=16*16,
    65536=256*256,
    L=65536*65536,
    3=2+1,
    8=4+4,
    15=16-1.

Thus this presentation has strict count `106+9=115`.

## Eight operations cannot suffice for this target set

Allow addition, subtraction, and multiplication, starting only with 1;
intermediate integers may have either sign. Each operation produces one
integer. The five distinct required small positive integers each require
an output. In a putative eight-operation construction, at most three
outputs can therefore be outside `{2,3,4,8,15}`; these include the large
target L itself. Duplicates and negative intermediates consume this same
allowance.

Consider the first production of 15. Before that moment the required
small values have absolute value at most 8. Let k be the number of
outputs outside the required small set that have already been produced.

* If k=0, the available values are a subset of `{1,2,3,4,8}`. No sum,
  difference, or product of two members of this set equals 15.
* If k=1, let W be that one other available value. Producing 15 must use
  W, since the previous case excluded the other possibilities. A sum or
  difference with a value of absolute value at most 8 forces `|W|<=23`;
  a product forces `|W|<=15`. Using W twice cannot give 15 by any of the
  three operations. Thus the maximum magnitude when 15 is first produced
  is at most 23. At most two further outputs outside the small target
  set remain. Each can at most square the current maximum, since for
  a maximum at least 2 one has `2M<=M^2`. Hence `L<=23^4=279841`.
* If k=2, the maximum magnitude before producing 15 is at most
  `8^(2^2)=4096`. This is a deliberately generous bound that gives all
  required smaller values for free when maximizing an intermediate.
  At most one other output remains, so `L<=4096^2=16777216`.
* If k=3, all outputs outside the required small set have already been
  produced. Their maximum, including L, is at most
  `8^(2^3)=16777216`. Subsequent small outputs cannot increase it.

Every case contradicts `L>950157215`. This proves that nine operations
are necessary for this precise numeral target set, even when subtraction
and negative intermediates are allowed.

## Consequences for further optimization

Choosing a different admissible exponent L cannot lower the strict
count of this presentation to 113 or 114. Such a result would need a
core rewrite that eliminates one or more required small numerals, a
different encoding with a substantially smaller required exponent, or
another change to the cost convention.

The obvious modulus rewrites do not improve the total: for example,
`8a_0+15=8(a_minus-1)-1` adds a core instruction, while the required
intermediate offset is not otherwise computed. The numeral conclusion
does not exclude a more substantial sharing identity elsewhere in the
core schedule.
