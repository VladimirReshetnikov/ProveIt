# A conditional Higman-operation compiler for the commutator pattern

From a supplied unary set E_U, the fixed ten-coordinate commutator
pattern is obtained by an explicit finite expression in Higman's
operations. No recognizer for U is constructed. This isolates the
remaining index-recognition problem from the copying, signs and constants
in the word pattern. It is a specialization of the existing H-machine
method, not a new general closure theorem or numerical group compiler.

Root posed this question after the frozen positive7 instantiation-gap
audit. The opposite-pair construction follows the setup in Mikaelian's
Higman-operations paper; root and Pascal independently supplied the
finite-pair-chain proof and corrected projection below. Root also supplied
the adjacent-swap placement in Section 4.

## 1. Exact primitives and finite macros

Let E be the integer-valued functions on Z of finite support. A tuple
starts at index 0 and is zero elsewhere. The two base sets are

    Z={(0)},   S={(n,n+1):n in Z}.

The operations used here have the following meanings:

| Operation on A | Condition on an output f, for some g in A |
|---|---|
| rho | f(i)=g(-i) |
| sigma | f(i)=g(i-1) |
| tau | swap coordinates 0 and 1 |
| zeta | agree with g away from coordinate 0 |
| pi | agree with g on every i<=0 |
| omega_4 | every aligned four-coordinate block belongs to A |

The last row is a block condition at all integer block indices, with
each block read as a four-entry function zero elsewhere. Write
iota(A,B)=A intersect B and upsilon(A,B)=A union B. These are exactly
the used primitives from H, not arbitrary affine transformations.
[Mikaelian, arXiv:2002.09728v6, Sections 2.2--2.4](https://arxiv.org/pdf/2002.09728v6).

Composition acts from right to left. Define the following macros solely
as the displayed finite compositions:

    sigma^-1 = rho sigma rho;
    zeta_i   = sigma^i zeta sigma^-i;
    T_i      = sigma^i tau sigma^-i;
    pi_left  = rho pi rho;
    pi_after1= sigma pi sigma^-1.                         (1)

Every fixed integer power is finite iteration, using the first line for
negative powers. zeta_i frees coordinate i, T_i swaps i and i+1,
pi_left frees indices <0, and pi_after1 frees indices >1. These assertions
follow by substituting the shifted indices into the primitive definitions.
For a finite index set F, zeta_F means the finite product of zeta_i,
i in F; their order is immaterial. It is not a new operation.

## 2. The universal opposite-pair relation

First construct the following fixed sets:

    C0 = T_1 tau S;
    C1 = T_1 sigma^2 S;
    L1 = zeta_{2,3} Z;
    L2 = iota(zeta_{1,3} C0, zeta_{0,2} C1);
    L  = omega_4 upsilon(L1,L2);
    M  = iota(L,sigma^-2 L).                              (2)

C0 consists of (m,0,m-1,0), C1 of (0,n,0,n+1). Their liberations
in (2) and intersection therefore give precisely

    L1={(0,0,m,n):m,n in Z},
    L2={(m,n,m-1,n+1):m,n in Z}.                          (3)

No pointwise sum of sets is assumed. In particular (0,0,0,0) is in
L1, so finite-support words can satisfy the omega_4 condition.

For g in M, put z_i=(g(2i),g(2i+1)). Combining L's aligned blocks
with the shifted condition sigma^-2 L says, for **every** i in Z,

    z_i=(0,0), with z_(i+1) arbitrary,
    or z_(i+1)=z_i+(-1,+1).                              (4)

Suppose z_i is nonzero. Until zero is reached, the second alternative
is forced, hence z_(i+t)=z_i+(-t,t). Finite support forces a first
zero at some positive integer t. Therefore z_i=(t,-t), t>0.
Every pair in M is consequently (n,-n) with n>=0. Conversely, for
any n>=0, place (n,-n),(n-1,-n+1),...,(1,-1) starting at pair index
0 and place zero pairs elsewhere. The initial jump from zero is
permitted by the first alternative; all later transitions obey (4).
This finite-support g lies in M and realizes the specified pair at 0.

Now define

    P = iota(pi_after1 pi_left M, zeta_{0,1} Z);
    D = upsilon(P,tau P).                                (5)

The two pi macros free precisely the coordinates outside {0,1};
their composition preserves a pair occurring in one witness g in M.
Intersecting with zeta_{0,1}Z sets every other coordinate to zero.
Thus P={(n,-n):n>=0}, and

    D={(n,-n):n in Z}.                                   (6)

The starting L1,L2,M mechanism is inherited from Section 4.4; (4)
is a direct complete proof of its needed projection, with explicit
indices. It avoids that section's slips retained in Section 5.
[Mikaelian, Section 4.4](https://arxiv.org/pdf/2002.09728v6).

## 3. The two constants

Only two singleton sets are needed:

    Nplus  = iota(tau S,zeta Z)={(1)},
    Nminus = iota(S,zeta Z)={(-1)}.                       (7)

Indeed zeta Z fixes coordinate 1 to zero. Intersecting it with (n+1,n)
forces n=0; intersecting it with (n,n+1) forces n=-1. This derives the
constants from the allowed bases; no coordinate translation or
pointwise sign operation is inserted.

## 4. The complete conditional pattern expression

Let U be any subset of Z, and supply

    E_U={g:g(0) in U and g(i)=0 for i!=0}.

The actual universal index set is positive, but the following set identity
does not require positivity or recursive enumerability. Put F={1,...,8}.
Define eight sets, using only the fixed macros above:

    B_U  = zeta_{F minus {3}} sigma^3 E_U;
    D13  = T_2 sigma D;
    B13  = zeta_{F minus {1,3}} D13;
    B35  = zeta_{F minus {3,5}} sigma^2 D13;
    B57  = zeta_{F minus {5,7}} sigma^4 D13;
    B2   = zeta_{F minus {2}} sigma^2 Nplus;
    B4   = zeta_{F minus {4}} sigma^4 Nplus;
    B6   = zeta_{F minus {6}} sigma^6 Nminus;
    B8   = zeta_{F minus {8}} sigma^8 Nminus.

    X_U = B_U intersect B13 intersect B35 intersect B57
          intersect B2 intersect B4 intersect B6 intersect B8.    (8)

The last line is seven binary iota operations. D13 first moves D to
coordinates {1,2}, then swaps 2 with 3; its two later shifts give
{3,5} and {5,7}. Thus no unrestricted coordinate permutation is used.
All factors in (8) have support contained in F. In particular coordinates
0,9 and all coordinates outside the ten-entry window remain zero.

To prove the identity, let n=f(3). The first factor enforces n in U.
The three D factors give f(1)=-n, f(5)=-n, f(7)=n. The four remaining
factors give f(2)=f(4)=1 and f(6)=f(8)=-1. Hence (8) is exactly

    {(0,-n,1,n,1,-n,-1,n,-1,0):n in U}.                  (9)

Conversely every displayed tuple meets each factor, using (6),(7).
There are no other restrictions, and if E_U is empty then so is (8).
E_U occurs once. Every other ingredient is a fixed H-expression from
Z,S; expanding (1),(2),(5),(7) and the fixed iterations in (8) removes
all macros. The equality constraints impose repeated values through
intersections; they do not assume a primitive copy or sign gate.

With the explicit even-a/odd-b word convention of the preceding gap
note, (9) encodes [b^-n a b^n,a]. That note's fixed generator swap for
the different displayed parity in the v8 embedding paper still applies;
the current operations paper fixes tuple indices at 0,1,... .

## 5. Retained index boundaries and exact scope

**Remark 1 (the printed pi2 projection loses n=2).** The operations
paper's Section 4.4 Step 4 prints C3=pi_2 pi_left M and then intersects
with pairs supported at {0,1}. By its own definition pi_2 frees only
indices >2. A witness for output (2,-2) must satisfy g(0)=2,g(1)=-2
and g(2)=0, but (4) forces g(2)=1. The claimed positive opposite-pair
set therefore does not follow from that literal expression. In fact its
intersection with support {0,1} gives only (0,0),(1,-1), and the added
strict sign restriction leaves just (1,-1). Replacing
pi_2 by pi_after1 as in (5) is the required local repair.

**Remark 2 (an adjacent printed index is also wrong).** The preceding
paragraph asserts existence of g with g(0)=n and g(2)=-n in M for every
n>0. Formula
(4) implies every even coordinate is nonnegative, so this is impossible
for n>0. The negative partner is coordinate 1. The printed g(2)=-g(2)
in the same paragraph is not used. These are corrections to displayed
indices, not a claim that the opposite-pair theorem is false.

**Remark 3 (left-liberation conjugation must follow its index).** The
printed auxiliary formula sigma^-i pi_left sigma^i frees indices <-i,
although it is described as freeing indices <i. For i=1 and input Z,
it excludes the unit function at index 0, which the latter description
would include. The correct conjugation for freeing indices <i is
sigma^i pi_left sigma^-i. We use only pi_left at 0 and the directly
checked pi_after1, so no incorrect general conjugation enters (8).
[Mikaelian, Sections 2.4 and 4.4](https://arxiv.org/pdf/2002.09728v6).

**Remark 4 (the printed general-swap exponent moves the wrong site).**
Section 2.4 prints, with s=l-k-1,

    tau_{k,l}=sigma^k (tau sigma)^s tau (sigma^-1 tau)^(-s) sigma^-k.

At k=0,l=2,s=1 this is tau sigma^2, because
(sigma^-1 tau)^-1=tau sigma and tau^2 is the identity.
It sends the unit function delta_2 to delta_4; swapping coordinates
0 and 2 would send it to delta_0. Root identified this separate printed
macro error, and Pascal and Riemann independently checked the displayed
exponent and counterexample. Our construction uses only the adjacent
T_i in (1), never the printed general-swap macro. Remarks 1--4 were
checked against the rendered primary pages 5 and 14, so the discrepancies
are not PDF text-extraction artifacts.
[Mikaelian, Section 2.4](https://arxiv.org/pdf/2002.09728v6).

**Question 1 (the remaining task, credited to root).** Construct a finite
H-expression for the actual unary E_U with its explicit program-index
and enumerator contract. The present theorem converts such an expression
to X_U, but supplies no recognizer or expression for E_U. Consequently
the finite benign pair, named finite-presentation embedding words,
universal numerical r and positive7 matrix list remain unmaterialized.
Counting the fixed H macros here is not a bound on any of those outputs
or on Diophantine arithmetic operations.

The proof uses exact source definitions and handwritten set algebra.
No scientific program, supplied helper, stored matrix/source array,
numerical experiment or degree propagation was run. Standard PDF text
extraction/rendering and fresh byte metadata are the only machine work.
Primary pages 3--5 and 12--14 were read as text; pages 5 and 14 were visually
checked. This is a bounded conditional-pattern proof, not a full review
of the H-machine paper or the Higman embedding theorem.

Root read and passed the full original 212-line draft, then independently
checked the fourth retained counterexample against the printed page.
Riemann separately read and passed the full draft, its final changed span,
the exact source definitions, pair-chain projection and word convention.
Both challenges found no correction to the conditional construction.
Their source checks also visually confirm the four retained slips.
Final changes only record this provenance and byte/read-span metadata.
This proof/metadata pair is frozen; no scientific checks were run.
