# Two positive stacks with an affine ordinary-input loader

A fixed binary two-stack machine can recognize every recursively enumerable
set of positive integers using an initial configuration

    (n_0,r_0)=(s_start, kappa*x+lambda),                  (1)

where kappa>0 and lambda>=0 are fixed program numerals. The varying input
is the ordinary integer x. The loader costs **two operations, 1M+1A**;
there is no separate variable prime-power or block-encoding equation.
Input conversion takes ordinary machine steps inside the run.

For a machine with B listed transition branches, its exact scalar step
has **four positive witnesses, five equations**, and a literal cost of
**16B-3=8B M+(8B-3)A**. For each fixed duration t>=1, fully unrolling
those steps gives **6t-2 positive witnesses**, **5t equations**, and cost
**2+t(16B-3)**, including the input loader and the fixed accepting endpoint.
One sum-of-squares polynomial costs **(16B+12)t+1**.

The [factored read-selector successor](two_stack_factored_selector_step.md)
reduces the scalar graph to **8B+18** for a full B=9K table, using eight
witnesses and seven equations. It retains the machine and input contract
proved here. The [typed-history audit](two_stack_polycyclic_history_obstruction.md)
explains the stack guards and the cost of a bounded-depth linear encoding.

This improves the ordinary-input contract of the
[prime-counter substrate](residue_affine_factored_counter_step.md).
It does not yet give a fixed-size certificate for an existentially chosen
run length. Neither the scalar bound nor the fixed-duration family is a
complete universal improvement below75.

## 1. Every positive integer is a valid binary stack

Write a finite binary word in top-first order, w=(w_0,...,w_(ell-1)). Set

    enc(w)=2^ell+sum_(j=0)^(ell-1) w_j*2^j.              (2)

The empty stack has code1. A leading symbol b satisfies

    enc(bw)=2*enc(w)+b.

Every positive integer is exactly one stack code: its highest binary1 is
the bottom sentinel, and its lower bits, read least significant first,
are the stack word. There is no promise restricting the input x to a
sparse set of codes. Let dec(x) denote this word.

For any *fixed* binary prefix p of length ell, define fixed numerals

    kappa=2^ell, lambda=sum_j p_j*2^j.

The concatenation identity is

    enc(p dec(x))=kappa*x+lambda.                       (3)

Thus prefixing a fixed program costs one multiplication and one addition.
The exponent ell depends on the fixed program, not on the queried input.
The stack's bottom sentinel is preserved by this identity, including x=1
and prefixes ending or beginning in zero.

The omitted leading1 of x can be restored by a finite controller. Begin
with an empty left stack and the stack code x on the right. While the
right stack is nonempty, pop its top bit and push that bit on the left.
When the right stack becomes empty, push1 on the left. The left stack now
contains the usual most-significant-first binary word for x, and the right
stack is empty. This takes exactly bit_length(x) steps when the paired
pop/push is one transition. It is an executed preprocessing routine, not
an uncharged arithmetic transformation of x.

## 2. Exact fixed-universal-machine contract

For related constructive context,
[Timothy Murphy, *A Universal Machine* (2003), Sections1-4](https://www.maths.tcd.ie/pub/Maths/Courseware/AlgorithmicEntropy/UniversalMachine.pdf)
constructs a universal stack interpreter and discusses two-stack/Turing
equivalence. Its displayed interpreter has four stacks. Its Chaitin input
convention makes reading past the end or halting before consuming the
whole input undefined; that convention does not establish the arbitrary
finite-word contract needed here. We use the following direct construction
with an ordinary finite input tape and a detectable blank endpoint instead.

Encode a finite Turing transition table by a binary word e of length k>=1,
and prefix it by the self-delimiting header1^k0. One fixed interpreter first
counts those1s, reads exactly the next k description bits, and stores the
decoded table on its work tape. It then copies the remaining binary input
word w, stopping at the first blank, and simulates the stored table on w.
Each simulated step searches the stored finite table for the matching
state/symbol record and updates the simulated tape. These operations are
ordinary Turing procedures, so their composition is one fixed finite-word
Turing machine U. Invalid descriptions and rejecting halts enter a
nonaccepting loop. For the fixed prefix p_T=1^k0e, this construction gives
U(p_T w) accepting exactly when the described machine T accepts w, including
empty w. The proof uses the explicit endpoint test, not the different
input convention in the cited stack interpreter.

Fix a recursively enumerable set S of positive integers. Effectively form
a binary-word recognizer T_S which, on w, accepts exactly when enc(w) is
in S. This is an ordinary computable change of word interpretation; for
example the routine in Section1 reconstructs the binary numeral before
simulating a recognizer of S. The constructed finite-word interpreter gives
a finite program word p_S for its fixed universal Turing machine U:

    U(p_S w) accepts if and only if enc(w) belongs to S.  (4)

Here and below acceptance means finite arrival at the intended accepting
state; a rejecting halt is directed to a nonaccepting loop. The interpreter
detects and copies the whole finite remainder before its simulation starts.

To implement this one fixed U with two stacks, retain its current tape
symbol and finite control state in the controller. The left stack holds
the tape to the left of the head, nearest symbol first, and the right
stack holds the tape to the right. Moving right writes a symbol onto the
left stack and pops the next current symbol from the right; moving left
is symmetric. An empty stack supplies a blank. Finite tape alphabets are
encoded by fixed-width binary words, and the controller performs the
finitely many bit pushes/pops needed for each simulated move.

The raw binary input needs no externally supplied block code. A fixed
initial phase pops its bits from the right, pushes the reverse of each
symbol's fixed binary code onto the left, and then transfers all those
bits back to the right. This produces the correctly ordered coded tape;
it handles an empty input too. The phase, the first tape-symbol read,
code validation, and every later simulated move are part of the same
finite binary two-stack controller.

On an accepting simulated halt, add cleanup states which pop both stacks
until empty and then enter a fresh state h. No other state enters this
cleanup. Let h keep both stacks unchanged. Rejecting or otherwise
undefined transitions are completed by a nonaccepting loop. This gives
one fixed total deterministic two-stack machine and a fixed point target
with both stacks empty. All these normalizations enlarge its fixed table;
they are included in B when the scalar theorem is applied.

Consequently, after folding the finite control into the left coordinate
as in Section3, the fixed numerical map F satisfies

    x belongs to S
    iff F^t(s_start, kappa_S*x+lambda_S)=(h,1)
        for some finite t>=1.                          (5)

Choose s_start different from h to exclude a zero-step exception.
The fixed constants in(5) are exactly those in(3) for p_S. This establishes
an ordinary affine input contract for a fixed universal substrate. It does
not assume a free prime-power loader or free numeral-to-block conversion.

The executable fixture is the explicit input-decoding routine, not a
transcription of a complete universal interpreter table. Thus no numerical
value of B for a small universal interpreter is asserted. The theorem
applies to any such fixed table, with every branch counted.

## 3. Binary transition normal form and folded control

Let the finite states be1,...,K. At each step a branch reads one symbol
from each stack, where the symbol is one of E,0,1 and E denotes the empty
stack. A nonempty read is popped. The branch then pushes a fixed binary
word onto each remaining stack and changes state. Push words are written
in top-first order. A machine that merely inspects or preserves a symbol
can pop and push it back in one such branch. Ordinary serial push/pop
programs therefore fit this finite normal form.

For a selected read symbol s and pushed word v, define fixed integers
(d,c,a,b) by

| Read symbol | d | c | a | b |
|---|---:|---:|---:|---:|
| s in{0,1} | 2 | s | 2^len(v) | val(v) |
| E | 0 | 1 | 0 | 2^len(v)+val(v) |

Here val(v)=sum_j v_j*2^j is a fixed numeral. For a strictly positive
quotient P, the exact input/output stack equations are

    X=dP+c, X'=aP+b.                                  (6)

On a nonempty read, P is the remaining stack code and is positive. Thus
X=1 cannot masquerade as a popped1: it would require P=0. On an empty
read, X=1 is forced, and X' is the fixed encoded pushed word. P is then
irrelevant and may be any positive integer. The output coefficient a=0
is essential in that case; a free empty-stack quotient cannot create
unrepresented contents.

Let X,Y be the two positive stack codes and j the state. Fold the state
into one positive coordinate:

    n=K(X-1)+j, r=Y.                                  (7)

Every positive n has a unique such pair(X,j), with X>=1 and1<=j<=K.
No variable length, exponent or divisibility witness is needed to define
this representation in the proof.

List all B branches. For branch z, let I_z,O_z be its source and target
states. Take(d,c,a,b) for its left stack and(e,f,g,h0) for its right.
Precompute these eight fixed coefficient columns:

    ns=K*d, nc=K*(c-1)+I_z,
    rs=e, rc=f,
    ts=K*a, tc=K*(b-1)+O_z,
    us=g, uc=h0.                                      (8)

The exact branch equations are

    n=ns*P+nc, r=rs*Q+rc,
    n'=ts*P+tc, r'=us*Q+uc.                            (9)

Some fixed offsets in(8) are negative. Their role is to encode positive
stack/state configurations; they are signed constants, not positive
existential coordinates.

## 4. A complete positive scalar certificate

Interpolate the eight coefficient columns at z=1,...,B, and clear all
coefficient denominators with one fixed positive integer D. Write
NS(z),NC(z),...,UC(z) for the resulting integer polynomials, of degree at
most B-1, so that they evaluate to D times the corresponding entries.

For positive arguments n,r,n',r', supply only four positive witnesses
z,v,P,Q and impose

    z+v=B+1,
    D*n =NS(z)*P+NC(z),
    D*r =RS(z)*Q+RC(z),
    D*n'=TS(z)*P+TC(z),
    D*r'=US(z)*Q+UC(z).                                (10)

The first equation forces z into the listed branch range. Dividing the
other equations by the fixed D in the proof recovers(9). Equation(7)
and the source-state column ensure the branch's source state is the actual
state. Equation(6) forces each read symbol exactly: the empty case has
stack1; a nonempty case has the stated parity and a positive remaining
stack. The output equations then give exactly the chosen pushed words
and target state. Hence every positive solution of(10) is a genuine step.
For a deterministic complete table exactly one branch is possible.

Conversely a genuine step supplies its branch z, v=B+1-z, and the two
remaining stack codes after popping. On an empty stack choose the unused
quotient to be1. All four witnesses are strictly positive and satisfy(10).
This proves the full scalar graph, including both stacks empty, only one
empty, empty pushed words, zero bits, and arbitrary stack depth. There is
no hidden nonzero-stack promise.

Eight padded Horner evaluations cost8(B-1)M+8(B-1)A. The four remaining
affine equations each cost two multiplications and one addition, including
the multiplication of their positive argument by D. The selector slack
costs one addition. Therefore the literal total is

    16B-3=8B M+(8B-3)A.                                (11)

The five squared residuals add5M+9A, giving **16B+11 operations** for a
single polynomial, with the same four positive witnesses. All numeral
multiplications are charged. These padded schedules allow
coefficient-specific reductions; they do not assert arithmetic optimality.

The two-state decoder fixture has B=18 and therefore costs285 operations
as this generic scalar graph, or299 as one polynomial. It is an input
routine used to validate the compiler, not a claimed small universal
machine or a competitor to complete75.

## 5. Fully paid bounded histories

Fix an integer t>=1 externally when constructing the certificate. Compute
r_0=kappa*x+lambda with one multiplication and one addition; take n_0 to
be the fixed starting state. Fix(n_t,r_t)=(h,1). Supply the2(t-1) positive
intermediate configuration coordinates and four fresh positive witnesses
for each of the t copies of(10). The exact totals are

    positive witnesses = 2(t-1)+4t = 6t-2,
    equations = 5t,
    graph operations = 2+t(16B-3),
    multiplications = 8Bt+1,
    additions = (8B-3)t+1.                             (12)

Every configuration coordinate is shared between its preceding and
following step. Thus induction using the scalar theorem proves that the
certificate has positive witnesses exactly when the loaded computation
reaches(h,1) at step t. All honest finite histories supply positive
witnesses by the converse. Since(h,1) is absorbing, reaching it earlier
also permits padding to step t using genuine transitions and positive
empty-stack witnesses.

A single polynomial can sum the t scalar sum-of-squares polynomials.
The t-1 extra additions, together with the loader, give

    total = (16B+12)t+1,
    M=(8B+5)t+1, A=(8B+7)t.                            (13)

These are literal counts including the fixed endpoints, without any
arithmetic for equality comparisons. Constant-specific simplifications
may reduce an endpoint copy, but are not taken in this generic schedule.

This is a *family* indexed by fixed t. Its number of witnesses and its
arithmetic size grow with t. Declaring t to be existential does not turn
the family into one fixed Diophantine polynomial. A uniform packed-history
construction remains required for the universal equation problem.

## 6. Remaining history problem and evidence

The loader now has the required ordinary numerical interface and a paid
constant cost. Empty-stack behavior and control synchronization are paid
locally in(10). An arbitrary-duration history still needs a common finite
geometry, bounded digit fields, and simultaneous enforcement of the local
equations at every time. In particular NS evaluated at a packed branch
word is not coefficientwise lookup, and its product with a packed quotient
word has cross terms between times. The scalar schedule cannot be applied
to packed histories unchanged.

This substrate also differs from one-dimensional interval-affine dynamics
and from the prior pure-division, coprime-slope ancestor-pumping subclass.
It has two independent positive integer coordinates, residue guards, and
point guards for empty stacks. The nonempty ordinary-input language of
this fixed machine therefore is not subject to those one-coordinate
obstructions.

The [checker](two_stack_affine_input_step.py) compiles the eight exact
coefficient columns, proves the five source identities and sum-of-squares
identity symbolically, and compares the arithmetic graph against independent
word-based stack execution. It tests wrong branch/output choices and the
irrelevance of arbitrary positive empty-stack quotients. It checks the
fixed-prefix identity across all prefixes of length at most6 and verifies
the leading1 decoder on the first1024 ordinary positive inputs, including
actual scalar witnesses along selected decoder runs.

A separate two-state cleanup fixture checks the complete bounded-history
schedule at durations1,...,8, including histories that have not yet reached
the forced endpoint, correct zero-stack padding, and wrong initial inputs.
The [receipt](two_stack_affine_input_step.json) is regenerated and compared
by default. Neither executable fixture is universal, and the complete
universal interpreter table has not been transcribed or assigned a numerical
branch count here. The parametric proof and the directly constructed
finite-word interpreter establish the universal substrate; the finite checks
audit its arithmetic compiler and input interface.

Independent proof/source/default review passed after correcting the
reference's input-convention scope. That review checked3,000 additional
cases from a separately generated three-state,27-branch table with arbitrary
replacement words of lengths0,...,4, including265 empty-stack cases with
arbitrary positive unused quotients. It also checked the direct finite-word
interpreter contract and the complete fixed-duration ledger. No
proof-assistant formalization or new complete universal arithmetic bound
is claimed.

    /tmp/diophantine-research-venv/bin/python two_stack_affine_input_step.py
