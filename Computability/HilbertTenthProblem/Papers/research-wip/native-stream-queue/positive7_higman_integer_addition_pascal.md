# An explicit Higman-operation expression for signed integer addition

There is a fixed finite expression in the Higman primitives, starting
from Z and S, whose output is exactly

    ADD={(a,b,a+b):a,b in Z},

with support contained in {0,1,2}. The expression below uses no supplied
addition relation, unrestricted linear map, pointwise sign change, or
recognizer. It is a local building block for the open unary-recognition
task, not a construction of that recognizer or a numerical group compiler.
Root requested this derivation after the conditional commutator-pattern
note. Pascal supplied the finite triple-history construction; Aristotle
supplied the shorter theta-based equality-pair macro in Section 2.

## 1. Primitives and conventions

Let E be the finitely supported integer-valued functions on Z. A tuple
starts at coordinate 0 and is zero at all undisplayed indices. The bases
are Z={(0)} and S={(n,n+1):n in Z}. All intermediate sets are subsets
of E. We use the following exact Higman primitives:

| Operation | Defining condition |
|---|---|
| iota(A,B), upsilon(A,B) | A intersect B, A union B |
| rho(A) | f(i)=g(-i) for some g in A |
| sigma(A) | f(i)=g(i-1) for some g in A |
| tau(A) | swap coordinates 0 and 1 of some g in A |
| theta(A) | f(i)=g(2i) for some g in A |
| zeta(A) | f agrees with some g in A at all i!=0 |
| pi(A) | f agrees with some g in A at all i<=0 |
| omega_6(A) | every block (f(6i),...,f(6i+5)), i in Z, belongs to A |

In the last row the six-entry block is interpreted as a function supported
on {0,...,5}. These definitions are from the primary operations paper,
Sections 2.2--2.4; no printed general-swap or projection macro is imported.
[Mikaelian, arXiv:2002.09728v6](https://arxiv.org/pdf/2002.09728v6).

Composition acts right to left. The following are only abbreviations for
finite compositions of the displayed primitives:

    sigma^-1 = rho sigma rho;
    zeta_i   = sigma^i zeta sigma^-i;
    T_i      = sigma^i tau sigma^-i;
    pi_left  = rho pi rho;
    pi_after2= sigma^2 pi sigma^-2.                       (1)

Thus sigma shifts one site to the right, zeta_i frees site i, and T_i
swaps sites i,i+1. pi_left frees sites <0, whereas pi_after2 frees sites
>2. Fixed powers are finite iteration; negative powers use the first
line of (1). For a fixed finite set F, zeta_F denotes a finite product
of its zeta_i. Liberation order is immaterial. A union or intersection
of three or five sets below means a fixed parenthesized series of binary
upsilon or iota operations, respectively.

## 2. The equality pair and three exact cylinders

Define

    Q=theta iota(zeta_2 S, zeta_0 sigma tau S).            (2)

Indeed the first liberated set has tuples (n,n+1,t); the second has
(t,m+1,m). Their intersection is exactly {(n,n+1,n):n in Z}.
The theta primitive selects coordinates 0 and 2, so

    Q={(n,n):n in Z}.                                    (3)

For any A supported on {0,1}, define the following three finite macros:

    C03(A)=zeta_{1,2,4,5} T_2 T_1 A;
    C14(A)=zeta_{0,2,3,5} T_3 T_2 sigma A;
    C25(A)=zeta_{0,1,3,4} T_4 T_3 sigma^2 A.              (4)

Their outputs are supported on {0,...,5}. They constrain, respectively,
the ordered pair at (0,3), (1,4), or (2,5) to lie in A and leave the
other four coordinates arbitrary. For example T_1 moves the second
coordinate of A from 1 to 2, then T_2 moves it to 3 while site 0 stays
fixed. The other two lines first shift this placement by 1 or 2 and
use the corresponding adjacent swaps. Every liberated coordinate is
listed in (4); no free copying or generic coordinate map is assumed.

Write Splus=S and Sminus=tau S. The ordered pairs in these sets satisfy
second=first+1 and second=first-1, respectively.

## 3. Four step blocks and the finite expression

Construct the following five sets of six-coordinate blocks:

    B0 = zeta_{3,4,5} Z;
    B1plus  = C03(Splus) intersect C14(Q) intersect C25(Splus);
    B1minus = C03(Sminus) intersect C14(Q) intersect C25(Sminus);
    B2plus  = C03(Q) intersect C14(Splus) intersect C25(Splus);
    B2minus = C03(Q) intersect C14(Sminus) intersect C25(Sminus).

    B = B0 union B1plus union B1minus union B2plus union B2minus;
    L = omega_6 B;
    M = iota(L,sigma^-3 L);
    ADD = iota(pi_after2 pi_left M, zeta_{0,1,2} Z).      (5)

This is the promised finite expression. Substituting (1),(2),(4), the
two S abbreviations and finite binary unions/intersections expands it
entirely into H applied to Z,S. There is no variable-length composition
hidden in (5): the unbounded sequence quantifier belongs to the one
permitted primitive omega_6.

## 4. Exact denotation of the expression

For g in E put z_i=(g(3i),g(3i+1),g(3i+2)). The block set B describes
exactly these alternatives for consecutive triples:

    z_i=(0,0,0), with z_(i+1) arbitrary; or
    z_(i+1)=z_i+(1,0,1); or
    z_(i+1)=z_i+(-1,0,-1); or
    z_(i+1)=z_i+(0,1,1); or
    z_(i+1)=z_i+(0,-1,-1).                              (6)

The scalar additions in (6) describe the proved denotation of the block
cylinders; they are not extra set operations used to form (5).
The condition g in L checks (6) at all even i. The condition
sigma^3 g in L, equivalent to g in sigma^-3 L, checks all odd i.
Thus g in M if and only if every adjacent pair obeys (6).

Define the integer invariant I(a,b,c)=c-a-b. Every one of the four
non-reset steps in (6) preserves I. If z_i is nonzero, finite support
ensures a first zero triple z_(i+t) for some t>0. At each preceding
nonzero triple the reset alternative is unavailable, so I is preserved
up to that zero. Consequently I(z_i)=I(0,0,0)=0. Zero triples already
have invariant zero. Every triple in every g in M therefore satisfies
c=a+b; cycles in the allowed step graph do not affect this argument.

Conversely, start with any z_0=(a,b,a+b). Move the first coordinate
toward zero one unit at a time using the appropriate B1plus or B1minus
step, updating the third coordinate by that same unit. After |a| steps
the triple is (0,b,b). Move the second coordinate toward zero using
B2plus or B2minus. After |b| more steps the triple is zero. Put these
successive triples at indices 0,...,|a|+|b| and zero triples elsewhere.
The transition from the preceding zero to z_0 is allowed by B0. All
other transitions obey (6), so this defines a finitely supported g in
M. The case a=b=0 uses the all-zero function.

The two liberations in the last line of (5) preserve the triple at
0,1,2 of a single underlying g in M and free every other coordinate.
Intersecting with zeta_{0,1,2}Z sets every other coordinate to zero.
The preceding two paragraphs therefore prove both inclusions in

    ADD={(a,b,c):a,b,c in Z and c=a+b}.                   (7)

This includes all sign combinations and all zero cases.

## 5. Retained boundaries and remaining scope

**Remark 1 (rho cannot supply pointwise negation).** The tempting
identification of rho with arithmetic sign reversal is false under the
exact primitive definition: rho fixes the singleton tuple (1), while
pointwise negation sends it to (-1). It reflects the support index of
delta_2 to -2 while preserving its value +1. Here rho is used only for
inverse shifts and left liberation in (1). Both signs of the step
relations come instead from S and tau S.

**Remark 2 (a valid longer equality construction).** Before Aristotle's
simplification, the equality pair was obtained from
A=iota(zeta_2 S,zeta_0 sigma tau S) by

    iota(zeta_2 T_1 A,zeta_{0,1}Z).

Since T_1 sends (n,n+1,n) to (n,n,n+1), this also gives (n,n).
Equation (2) replaces those swaps/liberations by the already permitted
theta operation; the earlier expression was valid, not a failed proof.

**Question 1 (the outstanding recognizer, credited to root).** How should
an explicit machine/program-index contract be converted into a finite
H-expression for the unary universal E_U? The addition relation (7)
and the preceding conditional commutator-pattern compiler provide
local set operations, but neither supplies that history/acceptance
construction. No literal benign pair, finite universal presentation,
numerical relator count, arithmetic circuit, or operation bound follows
just by counting the macros in (5).

All mathematical work here is handwritten set and integer reasoning.
Primary definitions were read as inert text. No scientific program,
stored source array, helper, symbolic computation, numerical experiment
or degree propagation was executed. Fresh byte metadata binds the final
proof and exact source reading.

Root and Aristotle each read and independently hand-challenged the full
184-line mathematical draft. Both passed the equality pair, ordered
cylinders, two alignments, first-zero invariant, all signed completeness
cases and same-witness projection, with no correction requested.
Question 1 records this note's dependency boundary: root's separate
`positive7_higman_unary_recognizer_root.md` draft now addresses it without
using ADD. That draft is not a premise of (7), and this arithmetic note
claims no recognizer construction of its own. The final changes record
only these scope and review details. This proof/metadata pair is frozen.
