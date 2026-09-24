# A seven-operation marker selector recovers its own radix alignment

A fixed nonzero Boolean radix16 marker can certify the alignment of its
own position. Given a Boolean radix16 word F and an independently proved
power of two A, its positive selector costs **7=4M+3A**, one multiplication
less than constructing the marker offset as a fourth power.

This is a conditional interface lemma. Its count does not include the
typing of F, the power-of-two proof for A, a machine history, or the
universal input compiler. The [checker](../verification/explore_typed_marker_alignment.py)
and adjacent receipt cover the exact three-equation source and the
alignment and cone inequalities.

## 1. Source and recovered position

Fix length ell>=1, K=16^ell and a nonzero Boolean radix16 word P<K.
It may have leading or trailing zero digits. Supply positive p,z,R,T,alpha
and impose

    pz=A,
    F=R+p^2(P+KT),
    R+alpha=p^2.                                          (1)

Compute E=p*p once. The source has four products pz,E,KT,E(P+KT)
and three additions P+KT,R+E(P+KT),R+alpha: seven operations, three
comparisons and five positive supplied coordinates.

Since A is a power of two, p=2^e for some e>=0. The prefix equation
gives0<R<E and therefore e>=1. The interval0<P<K means that the binary
bits of the three summands

    R, E P, E K T

occupy disjoint ranges: below2e, from2e through2e+4ell-1, and at least
2e+4ell, respectively. There is no carry into the marker. Choose any
set bit of P, at position4j. Then F has a set bit at2e+4j. Boolean
radix16 typing of F forces4|(2e+4j), so e is even. Write e=2k. We obtain

    p=4^k, E=16^k, k>=1.                                  (2)

The equation therefore selects exactly the ell digits of F beginning
at position k. The prefix R is the part below that position, and T is
the part above the marker. Both are Boolean words automatically, since
F is Boolean and the cuts are now aligned. Their strict positivity
requires a live digit before and after the marker.

Conversely, suppose a marker occurrence in F begins at k>=1, with
positive prefix R and positive tail T, and4^k divides A. Set
p=4^k,z=A/p,alpha=16^k-R. These witnesses are positive and satisfy (1).
This is the exact completeness domain, including its divisor condition;
the selector does not assert that every position is available in an
arbitrarily chosen ambient A.

The nonzero-marker assumption is essential to this proof. An all-zero
marker does not provide the aligned set bit that forces e to be even.

## 2. Sharing the square root with the boundary cone

For moving Rule110 histories, let the highest occupied power of the
initial word be M0=16^b. After t steps the highest occupied power of the
endpoint F is M0*16^t. This follows from the raw rule preserving the
rightmost1 and the moving shift advancing it by one position each step.

With p as in (2), the inequality

    F<M0*p                                                (3)

implies M0*16^t<M0*16^(k/2), hence2t<k. Conversely, if2t<k, then
k>=2t+1 and M0*p>=4 M0*16^t. Every nonzero Boolean radix16 word is
strictly less than16/15 times its highest occupied power, so (3) holds.
Thus (3) is exactly the required left-cone inequality under these
front-position hypotheses. A positive slack F+beta=M0*p enforces it
with the same product and addition as the older formulation.

The older selector supplied p_old=2^k, computed p_old^2 and then
E=p_old^4, and reused p_old^2 in (3). The new p is that square root of E
directly. The typed marker forces the missing alignment, so one square
is redundant without moving its cost into the cone.

## 3. Consequence for the provisional Cook interface ledger

For a self-contained arithmetic ledger, suppose the compiled initial
configuration has prescribed nonzero Boolean period words L0,R0 of common
length d, with phases fixed next to a Boolean center B0 of length c.
Assume c>=max(d,ell). Write a=16^d, b=16^c and use the fixed constants

    Q0=bR0, G=(a-1)B0+L0-bR0.

Positive S,zS,Z and the initial word I satisfy

    A=S*zS, (a-1)Z+1=S,
    (a-1)I+L0=S(Q0*S+G).                                  (4)

These equations cost8=5M+3A. They make S=a^j for j>=1, since S divides
the power of two A and a-1 divides S-1. The assembly equation is exactly
the word with j whole left periods, the center, and j whole right periods.
Put h=dj, so S=16^h. A negative fixed G uses subtraction at the same cost.

If e is the highest occupied digit of R0, define the free positive
integer constants K0=16^(c-d+e), KR=16^(c-ell). The initial highest
occupied power is M0=K0*S^2. Compute S^2 once and impose

    F+beta=(K0*S^2)*p,
    E+gamma=KR*S^2.                                       (5)

These cost6=4M+2A. The first inequality gives2t<k by Section2; the
second gives k+ell<2h+c. Thus the marker's entire backward dependency
interval [k-2t,k+ell-1] lies inside the initialized finite word. In this
conditional setting the artificial zero boundaries cannot create the
selected event. For any genuine finite-time event in the infinite
configuration, increasing both tail paddings eventually satisfies these
inequalities and leaves live digits before and after the marker.

Using the seven-operation selector (1), the resulting interface ledger is

    input8 + marker7 + cone6 = 21 = 13M+8A.

The width quotient A=W/16 of the
[complete76 source](EXPLORATION_LINEAR_WIDTH_RULE110_HISTORY.md) is an
available power of two. It can replace the older divisor host v in both
input and marker equations. For completeness the chosen row width can
be increased so that the two required divisors fit. Its input margin
I<A and the zero-exterior history proof remain valid.

For Cook's nonzero fourteen-digit halting marker, this replaces the older
eight-operation selector while keeping the input and cone costs. The
resulting provisional arithmetic sum is76+21=97=56M+41A. This
improves the older provisional99 ledger by two multiplications, one
from the history and one from this selector. It is **not a complete
97-operation certificate**: a combined source and full Cook compiler
audit have not been supplied, and the fixed-system raw-query loader
remains separate. The complete universal bound remains90.

## 4. Verification

The checker compares all three source residuals symbolically. It
exhausts positive prefixes through p=32, all nonzero Boolean marker
words of lengths1..4, and seven positive Boolean tails. Misaligned
powers of p never give a Boolean F. In aligned cases the test accepts
exactly the Boolean prefixes. Separate checks cover the shared square
root's exact cone inequality for several front positions and times.

These are finite checks supporting the general disjoint-bit and size
proofs, not a substitute for the external typing and power hypotheses.
Review status: author and independent complete scoped proof/source review
pass. The independent review also checks the eight-operation input identity,
the six-operation cone ledger, and its stated incomplete-compiler boundary.
