# Independent ordinary review of the affine window-gap lemmas

The frozen ordinary packet is approved within its explicit scope. I found
no mathematical gap in the fixed-gap divisibility restriction, carry-aware
word difference, constant-term-one local mask construction, separate
large-kernel arithmetic family, or conditional rank-controller criterion.
None establishes their required simultaneous compiler intersection, a
nine-positive equation, or an arithmetic-circuit/count improvement.

The reviewed PROPOSAL.md is the complete179-line file, SHA256
`f79720fbd44c4d030b188f39a25429c6ada24709d68b11bb080abb895021310c`.
The frozen packet manifest is
`79d85a07af0368ea5d99327d7170c7aedc73cffb1eb2c5bb1de45490adc80f71`.
Its SOURCE_PINS.json is
`ed05f763c8c285bda2c8cb73982bc06b45e145dc54b68394db78268af659de3f`.
I read the proposal, all251 lines of the closed one-word review, the complete
354-line compact44 native proof and its complete coefficient binding, all215
lines of the indexed-tile proof and its whole four-port binding, the60-line
native/source window note, and all223 lines of the q-cube proof. Every one of
the ten external pins and the proposal core pin matches. All four closed
inventories listed below match, including nested manifest members and any
recorded byte lengths. No frozen author file was edited.

## 1. General fixed-polynomial divisibility

For arbitrary integer P and any fixed A in Z[X], write
A(J)=A(0)+J H(J). If g=gcd(P+1,M) and the proposed linear transport is
solvable, g divides1-A(J). Multiplication by B-1 and M=(B-1)J gives
g dividing (B-1)(1-A(0)). This argument permits negative coefficients,
arbitrary degree and P=-1. The stated size bound when A(0)!=1 follows
from divisibility of a nonzero integer; it is uniform in N at fixed B,A.
When A(0)=1 the right side is0, so the lemma gives no bound and does not
assert solvability. These qualifications are necessary and are present.

For A(J)=DJ-1 and even B, M and g are odd. Therefore g dividing2(B-1)
implies g dividing B-1. Any common divisor of g and J divides2-DJ and J,
hence2; oddness gives gcd(g,J)=1. Since B=1 modulo g, J=N modulo g,
and consequently gcd(g,N)=1. No illicit cancellation by J is used.

## 2. Word differences and the exact bounded-controller obstruction

At the SAME fixed N,h, two solutions differ by an integer multiple of M/g.
As g divides B-1, their difference equals tJ with t a multiple of
(B-1)/g. If both words are strictly between0 and M and the difference is
positive, then0<t<B-1. The numerical integer tJ has the identical digit t
in each base-B position. Addition to the first word can nevertheless carry,
so this does not constrain each corresponding pair of original digits to
differ by t. The proposal explicitly avoids that false stronger assertion.

A consistent linear congruence modulo M has exactly g residue classes;
field bounds, masks and computation constraints can only reduce the number
of candidate words. Thus at most B-1 words at fixed N,h cannot surject onto
every class modulo dN when dN>B-1. This is a particular controller
surjectivity obstruction, not a nonuniversality theorem. Varying dimensions
or asking for only one rank class is outside that obstruction. The earlier
single-bit-toggle obstruction also remains: its power-of-two difference is
a unit modulo odd M and cannot be an independent fixed-gap kernel step at
the licensed nontrivial dimensions.

## 3. Complete coherent masks and the constant-term-one construction

The native recipe uses rho=2^67,L=8807,B=rho^L and the SAME support E of986
micro-positions in both compact44 and indexed BFS tuples. The indexed proof
rebuilds its whole K and controller rather than identifying old packed
words. Its beta,MC and shifted MF_source are byte-identical to compact44;
both binding files give the same complete raw hashes for those three ports.
The high mask used in every intersection here is
MF0=MF_source-(B-1), never MF_source itself.

The complete printed formulas are MC=B-1 minus the support sum excluding
position1 and minus2*rho^1063, while MF0 is4 plus its two clause bands,
copy/anchor bands and high padding. They justify MC=2 modulo4,
MF0=4 modulo8,0<MC,MF0<B-1. In particular both bit0 values vanish,
MC bit1 is set, and MF0 bit1 is clear.

Let D=MC AND MF0 and E=D+2. Since D bit1 is clear, adding2 has no carry:
E is D union bit1, is supported inside MC, and satisfies0<E<=B-2.
Here D<=MF0<=B-4 supplies the strict upper bound. Set H=MF0 AND NOT MC
and U=NOT(MC OR MF0), with complements restricted to d bits. Their repeated
words have no overlap between base-B cells. Any Z supported inside UJ
with global bit0 set exists; that bit is available in U. The construction
C=HJ OR Z is disjoint from EJ and MCJ, and has bit0 set.

Therefore C,F=M-C-EJ,EJ partition the complete dN-bit all-ones word.
Subtracting1 from C clears only bit0. This proves
(C-1) AND (MCJ+1)=0, including the extra low1 in the first mask.
Every MF0J bit belongs to HJ or DJ, so F is disjoint from MF0J.
Decrementing MF0J clears only its lowest set bit2 and sets bits0,1;
F has neither newly introduced bit, because C supplies bit0 and EJ supplies
bit1. Thus F AND (MF0J-1)=0. The identity C+F+(EJ+1)=q follows exactly.

Strict F>0 is established from the COMPLETE recipe, not a generic mask
heuristic. At micro-position1063, MC has digit rho-4: the support removes1
and the explicit correction removes2 from rho-1. MF0 has zero digit there;
its listed copy, anchor, clause and padding positions exclude1063. Hence
binary bit67*1063+2 is in MC but not MF0, not in the extra global bit1 of E,
and not in U. Neither HJ nor ANY allowed Z nor EJ contains this bit in
macro-cell0, so F contains it for every allowed Z. C>=1 and alpha=EJ+1>0
were already proved. No coefficient port is mixed with another tuple.

## 4. The independent arithmetic large-kernel family

For fixed h choose L=B^h+K0+1>1 with gcd(B,L)=1. A positive N divisible
by h and by ord_(L(B-1))(B) exists because B is coprime to that modulus.
Then L(B-1) divides B^N-1 and consequently L divides J, so g=L exactly.
The complete native DC formula has only positive powers of the even rho;
DC and K0=DC+B DR are even, verifying gcd(B,L)=1 in either whole tuple.
Thus these arithmetic kernels genuinely grow with h.

Put a=B-1-E>0. Then C0=aJ/L is a positive integer and
F0=aJ(1-1/L)>0. Their sum is aJ, so the required local sum with alpha=EJ+1
holds. Also L C0=aJ is congruent to -EJ modulo M. This is an explicit
transport solution. It is not asserted to satisfy either mask or valid
computation constraints. Conversely the previous Boolean construction is
not asserted to solve transport. No intersection theorem or old prime-power
padding compatibility is silently imported.

## 5. Conditional packed-rank criterion

At fixed q,J,alpha the actual formula gives
deltaRank=(q-1)(q^2-1)deltaC because deltaF=-deltaC. A kernel step M/g
therefore changes rank by M^2(q^2-1)/g, an integer because g divides M.
If gcd(q^2-1,dN)=1, both M and M/g are units modulo dN, so this entire
integer is a unit. A no-wrap interval of dN consecutive kernel parameters
satisfying ALL masks and local computation constraints would consequently
cover every rank class once. This is sufficient, not constructed.

The large-kernel dimensions need not preserve that unit condition or the
old padding schedule. No guarantee of such an interval, a cofinal
coordinated family, computation soundness/completeness or positive Pell
completion is supplied. The proposal identifies those missing obligations
explicitly. Its q-cube parent retains separate positive J,F,alpha and does
not supply an extra unbounded source register for this redesign.

## 6. Authenticated closed scope

The four complete inventories authenticated in this review are:

- affine-gap packet: `79d85a07af0368ea5d99327d7170c7aedc73cffb1eb2c5bb1de45490adc80f71`,2 payload members;
- one-word review: `01eee2d571407e2fb41ecc4a7726756b2618d2be44d3156ea1110f4306c933dd`,5 payload members;
- indexed tuple: `e077a476c38cb9abd96217887d16b011f6f5e16847036702720d69fcf91b1f84`,38 payload members;
- q-cube normalization: `5e541af44ddbfdf5684f02e64611c7fc84b24f8f25ba48b694702d665a708377`,48 payload members.

No proposal, compiler, source-generator, grouped-quartic or Lean program was
imported, compiled or executed. Only inert file reads and byte/inventory
authentication accompanied the ordinary proof review. This approval covers
the stated lemmas and their limits, with no source, equation, degree,
operation, unknown-count or frontier promotion.
