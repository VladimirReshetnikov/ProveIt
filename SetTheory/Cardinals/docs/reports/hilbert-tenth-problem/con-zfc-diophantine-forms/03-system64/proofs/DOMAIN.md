# Unrestricted integer variables and an explicit quartic

This note proves the domain conversions and quadratic lift emitted by
`source/domain_variants.py` into `artifacts/domain_variants.json`.
All transformed equations retain the exact fixed coefficients specified in
`artifacts/coefficient_recipe.json`. That recipe describes fixed integers;
the coefficient symbols in the JSON are not additional unknowns.

The source system is the final `fixed_marker76_system`: sixteen strictly
positive input variables, 64 shared arithmetic gates and seven comparisons.
The second source is the fifteen-positive-variable degree-295 polynomial
`fixed_marker82`. Their equivalence to the specified machine is inherited
from the main construction. The transformations below are exact and do not
require any further assumption about the coefficients.

## 1. A positive-integer parametrization with three integer coordinates

Define the integer polynomial

    Pos(a,b,c) = 1 + a^2 + b^2 + c(c+1).

For every integer c, the consecutive integers c and c+1 have nonnegative
product. Thus Pos(a,b,c) is strictly positive for all integer a,b,c.

Conversely, let t be any positive integer and put n=t-1>=0. The positive
integer 4n+1 is congruent to 1 or 5 modulo 8, and is not divisible by 4. It is
therefore not of the form 4^r(8s+7). Legendre's three-square theorem gives

    4n+1 = u^2+v^2+w^2.

Squares modulo 4 are 0 or 1, so exactly one of u,v,w is odd. Permute the
three coordinates so that w is odd, then write u=2a,v=2b,w=2c+1.
Division by 4 gives

    n = a^2+b^2+c(c+1),

and therefore t=Pos(a,b,c). Hence Pos maps Z^3 onto exactly Z_{>0}.
This uses the classical three-square theorem, which is a theorem of ordinary
number theory formalizable in ZFC; it does not assume the consistency of ZFC.

## 2. The complete 48-variable and 45-variable substitutions

For each original positive witness x, introduce three new unrestricted
integer variables x_a,x_b,x_c and substitute

    x = Pos(x_a,x_b,x_c).

Every coordinate in the original positive domain has such a preimage, and
every integer tuple maps into that domain. Therefore an original equation
or system has a positive-integer solution if and only if its substituted
version has an unrestricted-integer solution. The equivalence is in both
directions and preserves the same fixed coefficients.

The `integer48` entry lists all 48 unknowns, all 16 substitutions, all 64
renamed arithmetic definitions, all seven residuals, and their literal
sum-of-squares expression. Its maximum equation degree is 56; its single
sum-of-squares polynomial has exact degree 112.

The `integer45` entry lists all 45 unknowns, all 15 substitutions and all 82
renamed arithmetic definitions of the eliminated-root polynomial. Its
single equation has exact degree 590.

Names used for arithmetic definitions are abbreviations for explicit
polynomial expressions, not quantified unknowns. The JSON distinguishes
the finite list of unknowns from the finite list of definitions. Every
definition depends only on previously available values.

To justify exact degrees, let P have exact degree m. Its top homogeneous
part after substitution is obtained from P_m by replacing every original
variable x by x_a^2+x_b^2+x_c^2. This cannot be zero: specializing every
x_b and x_c to 0 yields P_m(x_a^2), and distinct original monomials have
distinct doubled exponent vectors. Thus the substitution doubles the
exact total degree. In particular, 56 becomes 112 and 295 becomes 590.
All coefficients remain integers throughout; no denominator clearing is
required.

## 3. An explicit system of 87 quadratic equations in 128 integer unknowns

Introduce the following independent unrestricted integer unknowns:

* 48 coordinates used in the sixteen Pos substitutions;
* 16 variables `inp__x`, one for each original positive input;
* 64 variables `gate__g`, one for each gate in the original shared circuit.

The total is 48+16+64=128. Fixed coefficients remain constants.

For each original input x add the equation

    inp__x - Pos(x_a,x_b,x_c) = 0.

For each source gate g=operation(a,b), in its original acyclic order, add

    gate__g - operation(rename(a),rename(b)) = 0,

where input operands are replaced by their `inp__` variables, gate operands
by their `gate__` variables, and fixed coefficients by their fixed symbols.
The only source operations are addition, subtraction and multiplication.

Finally add the seven original comparison residuals with their operands
renamed in the same way. These use no extra arithmetic gate variables.

There are 16+64+7=87 equations. Every domain equation has degree 2, every
gate equation has degree at most 2, and every final comparison has degree
at most 1. The generator emits every residual explicitly, validates each
AST and free identifier, checks all degrees, and checks the exact counts.
Prefixing the input variables, gate variables and Pos coordinates prevents
name collisions.

### Projection from a quadratic solution

The sixteen domain equations force every `inp__x` to be strictly positive.
Induction through the acyclic 64-gate list forces every `gate__g` to equal
the actual evaluation of its source polynomial at those inputs. The seven
final comparisons therefore hold for a positive solution of the original
system. Gate variables cannot serve as independent spurious witnesses,
because each is fixed by its defining equation and earlier values.

### Extension of an original solution

Given any positive solution of the original system, choose a Pos preimage
for each input using section 1. Assign every gate variable its actual integer
evaluation. Every domain equation, every gate equation and every output
comparison then holds. These two constructions prove exact equivalence of
solvability. Uniqueness is asserted only for gate values after inputs are
fixed; the Pos preimages need not be unique.

## 4. A single polynomial of exact degree 4

If E_1,...,E_87 are the emitted residuals, define

    Q = E_1^2 + ... + E_87^2.

Every residual has degree at most 2, so Q has degree at most 4. On integer
tuples all summands are nonnegative, hence Q=0 if and only if every
residual is 0. This gives the promised equivalent quartic equation in 128
unrestricted integer variables.

The degree is exactly 4. Take the private coordinate `pos__Jrep__a` in the
first Pos block. It appears only in that domain residual, whose expression
contains the term `-pos__Jrep__a^2`. Squaring contributes
`pos__Jrep__a^4` with coefficient 1. No other residual contains that variable,
so this monomial cannot cancel. The generator checks that the coordinate
is private and records the monomial and coefficient as a degree certificate.
This argument holds for the actual fixed compiler constants as well as
for arbitrary integer values of those constants.

## 5. Reproduction and evidence

Run from the package directory:

    python3 source/domain_variants.py
    python3 source/domain_variants.py --check

The generator uses Python's standard library and reads only the two saved
fixed-marker source JSON files and the coefficient recipe. Its output
records their SHA-256 hashes. It does not import or execute historical
compiler scripts, expand the enormous fixed coefficients, or change any
source construction. The finite AST and count checks support the emitted
artifact; the projection arguments above establish its correctness.

These domain conversions are alternatives for different simplicity criteria.
The 128-variable quartic is a fully emitted arithmetic lift; it is not
claimed to minimize the variable count among all quartic constructions.
