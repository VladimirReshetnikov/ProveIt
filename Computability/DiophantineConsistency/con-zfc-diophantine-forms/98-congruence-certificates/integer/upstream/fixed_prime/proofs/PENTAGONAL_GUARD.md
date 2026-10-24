# A positivity square condition with a fixed 3-adic residue

## Exact equivalence

For any integer N, define

    S(N,u,v)=24N-21-(6u-1)^2-(6v-1)^2.

Then

    N>0  <=>  exists u,v in Z such that S(N,u,v) is a square in Q.

An integer which is a rational square is an integer square, so the phrase
"square in Q" may be replaced by "square in Z". Furthermore S=1 mod3
for every integer assignment of N,u,v, even assignments which do not
satisfy the square condition. The latter uniform property is what permits
using this positivity test as another radicand in fixed 3-adic separation.

## Soundness

If S=z^2 for rational z, integrality of S implies z is integer by reducing
a rational fraction to lowest terms. Since (6u-1)^2 and (6v-1)^2 are each
at least1,

    24N-21=(6u-1)^2+(6v-1)^2+z^2 >=2.

Hence N>=1. Modulo3, S=0-1-1=1.

## Completeness from Legendre's three-square theorem

Let N>=1 and put M=24N-21=24(N-1)+3. It suffices to represent M by
three squares of integers coprime to6. Independent sign choices can then
make all three integers equal to -1 modulo6.

Let e be maximal with 9^e dividing M, and put M0=M/9^e. Then M0 is
positive, M0=3 mod8, and 9 does not divide M0. Legendre's three-square
theorem supplies x^2+y^2+z^2=M0. Modulo8 all three coordinates must be
odd. They are not all divisible by3, since otherwise9 would divide M0.

Use the integral matrix

    L = [[ 1, 2, 2],
         [ 2, 1,-2],
         [-2, 2,-1]].

Direct multiplication gives transpose(L)L=9 I_3. Also modulo3 its rows
are respectively (1,-1,-1),(-1,1,1),(1,-1,-1). For any vector primitive
modulo3, independent sign changes can make x-y-z nonzero modulo3.
Indeed, if that linear form vanished for every sign choice, subtracting
two choices differing only in one sign would force all three coordinates
to vanish modulo3. Thus, after suitable signs, L maps any odd vector
primitive modulo3 to an odd vector all of whose coordinates are nonzero
modulo3, and multiplies the squared norm by9.

Apply this lifting e times, choosing signs at each step. If e>0, the
resulting norm-M vector has all coordinates odd and nonzero modulo3.
If e=0, M is divisible by3 but not9. Its three squares sum to0 mod3;
therefore either all three coordinates are units modulo3 or all three
are divisible by3. The latter case is impossible because9 does not
divide M. Thus the same conclusion holds without a lift.

Choose signs so the final coordinates are 6u-1,6v-1,6w-1. They satisfy

    M=(6u-1)^2+(6v-1)^2+(6w-1)^2,

so S(N,u,v)=(6w-1)^2. This proves completeness.

## Classical attribution

The equivalent statement that every nonnegative integer is a sum of three
generalized pentagonal numbers is classical and must not be claimed as a
new theorem here. The standard identity is

    24*(x(3x-1)/2)+1=(6x-1)^2.

R.K. Guy, *Every number is expressible as the sum of how many polygonal
numbers?*, American Mathematical Monthly101 (1994),169-172, is cited for
this observation. A primary mathematical source confirming the exact
result and giving the square conversion is B.-K. Oh, *Ternary universal
sums of generalized pentagonal numbers*, arXiv:0911.1181, pp1-2:

https://arxiv.org/pdf/0911.1181

Oh points to Z.-W. Sun, *On universal sums of polygonal numbers*,
arXiv:0905.0635, for a complete proof. The elementary matrix-lifting proof
above is included so that the current adapter does not rely on an
unexamined assertion from a secondary source.

The new use under investigation is to merge this uniformly 3-adic-unit
radicand into the same fixed-weight norm that encodes the Pell roots.
That application, rather than the three-pentagonal theorem itself, is
the prospective construction improvement.
