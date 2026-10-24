# Independent review of the integer-domain conversion

The conversion is sound for the frozen3,609-natural parent. I checked its
ordinary two-way argument and the independent checker's complete coverage
of the actual semantic/gate partition. No extra native, Pell or positivity
assumption is introduced by this local domain conversion.

For integer c, c(c+1) is nonnegative, including c=-1 and0. Each appended
quadratic row x=a²+b²+c(c+1) therefore makes its one semantic input natural.
Every parent semantic input is covered exactly once; the five outer inputs
are included among the1,670, and all5,010 new auxiliaries are fresh.

The1,939 remaining parent variables are gate outputs. The checker reads
every actual defining row: its output is monic and every other term has
the opposite sign and involves only earlier coordinates, with nonnegative
coefficients after moving to the right side. It covers every gate exactly
once. Thus induction from the guarded inputs makes every gate natural.
This verifies the reason separate guards on those wires are unnecessary;
their naturalness is not assumed from a metadata label alone.

Conversely Legendre's theorem applies to4x+1 for every natural x. This
integer is1 or5 modulo8 and is not divisible by4, so it is not excluded
by the three-square criterion. Its representation has exactly one odd
square, since the total is1 modulo4. Writing that square as(2c+1)² and
the others as(2a)²,(2b)² gives precisely x=a²+b²+c(c+1). Each input's
representation can be chosen independently, with no feedback into the
parent equations.

The original residuals are retained exactly. Appending quadratic guards
keeps the final sum of squares quartic. No quadratic input expression is
substituted into an old product row. A fresh last auxiliary occurs in one
guard only, with fourth-power coefficient1 after squaring; the degree is
therefore exactly four. The checked counts8,619 variables and4,619 rows
follow from3,609+3*1,670 and2,949+1,670. The complete collected expansion
has39,811 terms and coefficient height127,285,349.

The normal/optimized generator and independent-of-builder checker receipts
pass. The checker compares the complete old prefix, exact fresh guard rows,
every nonnegative monic gate definition and every coefficient of the full
quartic. Small representation fixtures supplement the Legendre argument;
they are not its proof.

Composing this existence equivalence with the separately reviewed
prime-lift/C222 construction gives the same ordinary ZFC-formalizable
consistency equivalence over unrestricted integers. Lean and the encoded
internal-ZFC compilation theorem remain separate open work, in accordance
with the owner's pause.
