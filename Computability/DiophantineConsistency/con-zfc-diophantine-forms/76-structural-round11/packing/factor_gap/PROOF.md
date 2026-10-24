# A factored positive gap coordinate

This is a source-system simplification, not a better completed nine- or
 ten-variable endpoint. There are31 positive unknowns and22 quadratic rows,
85 weighted coefficient records instead86. In fully expanded port monomials
there are88 terms instead90. No fixed coefficient is changed.

Write q=beta J+1. In the prior positive-gap source, rows1 and2 imply
L=q^2-1 and N_old=q^3-1. Set

N_new=N_old-L-beta J=(q-1)^2(q+1)>0.

Here beta and J are positive, so q>=2. Conversely set
N_old=N_new+L+beta J, which is positive for every positive new tuple.
Substitute this expression in all prior rows, then replace transformed row14
by transformed row14 minus transformed row2. This invertible row operation
and the two inverse coordinate maps establish a bijection of positive zero
sets. All other coordinates and the whole original31 coefficient tuple stay
unchanged. In terms of the original pre-gap source coordinate, the substitution
is N_original=N_new+L+beta J+1.

The two particularly simple transformed rows are

r2=N_new-beta J L,
r14=F N_new-beta J N_new-beta MF J^2-J MC-J MF-L alpha-N_new-V+c j.

The terms in r14 sharing J or J^2 are one coefficient record each. Thus it
would be incorrect to count expanded port monomials as distinct kernel taps.
The old row2 uses4 records and the new2; row4 rises from4 to6; row14 falls
from9 to8. Net improvement is one weighted record.

The supplied exact checker proves the substitution/row-operation identities
as polynomial identities over Z in all31 variables and all four formal ports.
The mathematical positivity argument above is unbounded. A completed packing
layout beating the unchanged-source H1868 layout has not been obtained for
this source, so this is not used to inflate the final equation's improvement.
