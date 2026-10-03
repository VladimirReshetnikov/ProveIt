# A single-AND tape interface for Wang B machines

A power-of-two head, its read bit and a non-erasing mark can share one
complete native AND. The literal mark graph costs **74=35M+39A**
certificate operations,17 comparisons and24 positive witnesses; its
single polynomial costs **124=52M+72A**, with total degree **at most40**.
Omitting the mark equation gives the head/read interface in72 certificate
or119 polynomial operations, with16 comparisons and the same24 witnesses.

This is a complete scalar graph, not a complete Wang-program history.
It does not improve the [303-operation explicit U9 construction](neary_woods_universal_joint_and_units.md),
its [301-operation arithmetic successor](neary_woods_universal_joint_and_arithmetic.md),
or the separate [87-operation universal polynomial](complete75_normalized_strong87.md).
The useful feature is that no external power-of-two test for the head
is needed. Section5 gives an exact obstruction to replacing current-tape
reads by final-tape reads, despite the machine's monotonic tape.

## 1. Primary-source model and scope

Neary, Woods, Murphy and Glaschick,
[*Wang's B machines are efficiently universal* (2014)](https://mural.maynoothuniversity.ie/id/eprint/12409/1/Woods_Wang_2014.pdf),
Theorem1, proves effective simulation of binary Turing machines by Wang
B machines. Definition6 uses a finite list of four instruction types:
move left, move right, mark the scanned cell with1, and jump to a fixed
instruction when that cell is1. The tape is binary, bi-infinite and
otherwise blank. Falling past the final instruction halts. This is a
finite-input universal model, rather than a gate array requiring an
unspecified infinite background.

The source's Section3 constructs13 instructions per nonhalting state
of a simulated non-erasing binary machine, plus a final mark. Its tape
codes are0→10 and1→11. Section2 first simulates an ordinary binary
machine using a three-bit cell code and copying. Thus the source does
not license identifying an ordinary query integer with the eventual
Wang tape at zero arithmetic cost. It also does not supply a numerical
universal program table for the scalar circuit below.

This repository already has paid two-stack steps, residue-affine
counter steps, tag histories, matrix mortality and reversible-gate
components. The present construction isolates a different interface:
one unbounded non-erasing binary tape and one one-hot head.

## 2. Exact scalar graph, including head typing

Let T>=0 be a finite tape word with cell j stored at bit j. Let H>0 be
the candidate head mask. Supply positive parameters

    tape_hat=T+1, head=H, marked_hat=T'+1,

and positive witnesses read_hat=C+1 and beta. Compute the radix

    P=tape_hat+H+read_hat+beta.                         (1)

Hence T,H,C<P and C>=0 on every positive supplied tuple. Also P>=4.
Use one complete [prescribed-scale AND64](native_binary_masked_selection63.md)
with scale P², input words

    A=T+P*H,       B=H+P*(H-1),

and output word C. Add the mark equality

    marked_hat+read_hat=tape_hat+H+1.                  (2)

All conceptual native hats A+1,B+1,C+1 and the scale P² are positive
before any native equation. The complete AND theorem first gives P²
dyadic, hence P dyadic, and A AND B=C. Since all low words are canonical
base-P digits,

    A AND B=(T AND H)+P*(H AND (H-1)).                 (3)

But0<=C<P. Uniqueness of the low and high blocks gives

    H AND (H-1)=0,       C=T AND H.

Since H>0, the first equality is equivalent to H=2^j for an integer
j>=0. Equation(2) says T'+C=T+H, and consequently

    T'=T OR H.                                       (4)

Conversely, fix T>=0 and H=2^j, and set C=T AND H and T'=T OR H.
Choose any dyadic P>tape_hat+H+read_hat and set beta equal to their
positive difference. The two words A,B lie below P², satisfy(3),
and have AND equal to C. The full positive converse of AND64 supplies
all22 native witnesses. Equation(2) holds. This proves the exact
positive projection onto (tape_hat,H,marked_hat): it is precisely(4)
with a power-of-two head. The read_hat witness is uniquely C+1,
although the radix and native extensions need not be unique.

Deleting(2) gives the same exact head/read relation, with C still
available as the decoded witness read_hat-1. No outside promise that
H is one-hot, that P is dyadic, or that a tape bit is Boolean is used.
The tape may be initially empty and a mark may leave it unchanged.

## 3. Literal folding and arithmetic costs

The [source](wang_b_single_and_tape.py) folds the native padding into
the following gates. The first sum is reused by(2):

    tape_head=tape_hat+H;
    radix_partial=tape_head+read_hat;
    P=radix_partial+beta;
    P16=16P;               head_region=P16*H;
    native_q=P16*P;
    tape16=16*tape_hat;
    A_sum=tape16+head_region;
    native_A=A_sum-4;
    head16=16H;
    B_sum=head_region+head16;
    B_difference=B_sum-P16;
    native_B=B_difference+10;
    native_Z_scaled=16*read_hat;
    native_F3=native_Z_scaled-8.

These are exactly the native ports16P²,16A+12,16B+10,16C+8.
The fifteen displayed gates replace the seven original port gates;
the other57 AND64 gates are unchanged. The two additions for(2) then
give74 gates. In particular, sharing16P and16PH is counted; P² is not
silently precomputed. Every fixed-numeral multiplication is paid.

| Relation | Certificate | Comparisons | Positive witnesses | SOS polynomial | Degree bound |
|---|---:|---:|---:|---:|---:|
| Head and read |72=35M+37A|16|24|119=51M+68A|40|
| Head, read and mark |74=35M+39A|17|24|124=52M+72A|40|

The degree bound propagates through the actual DAG, with every supplied
parameter and witness degree one. It is not an exact-degree claim.
There are no gigantic program numerals in this component. The native
Pell witnesses remain part of its counted positive existential domain.

For an already selected instruction, moving right uses H'=2H and moving
left uses H=2H', each one additional doubling gate. Positive H' excludes
a left move from H=1 in this finite-window coordinate system. A fixed
jump has C either0 or H, so its next instruction can be expressed by
an affine equality after multiplication by H. These observations do
not select an instruction or assemble an unbounded run.

## 4. A finite-run translation with two initialization gates

Fix a literal Wang input integer x>0: initially, cell j>=0 contains
bit j of x, all negative cells are blank, and the head is at cell0.
Fix a finite execution, including its initial and final configurations.
Let L>=0 be at least the negative of every head position visited by
that execution. Translate every cell coordinate by L and put

    H0=2^L,       T0=x*H0,       initial_tape_hat=T0+1. (5)

The shifted tape has only nonnegative coordinates: initial marked cells
were nonnegative, and every later mark lies at a visited head position.
Translation preserves each current read, mark, jump and control label.
A right move becomes H'=H+H; a left move becomes H=H'+H'. The choice
of L ensures H'>0 for every left move in this finite execution.

The input initialization in(5) uses exactly one multiplication and one
addition **after H0 is typed by a separately paid initial head/read
instance of Section2**, or by that same already-paid first instance
in a proposed history relation. The two gates do not type H0 by
themselves. They also do not include that scalar instance's native
witnesses or its polynomial finalization cost. Its read output may
be discarded when the first selected instruction does not read.

Conversely, suppose a finite list of configurations, represented by
positive tape hats and head masks, has an explicitly paid initial
head/read instance, initialization(5),
and the exact selected-instruction constraints at every step: current
reads and marks are those of Section2, moves satisfy the indicated
doubling equalities, the tape and head are unchanged where required,
and control labels follow the selected instruction and current read.
The initial instance gives H0=2^L with L>=0. Starting from H0,
doubling, positive halving and head preservation keep all heads powers
of two. Subtracting L from every tape/head coordinate then recovers
an exact bi-infinite Wang execution on the original literal input x.
In particular, initialization forces every originally negative cell
to be blank. A left move from H=1 has no positive integer half and is
correctly excluded; completeness chose enough translation to avoid it.

Thus the finite-window translation has a paid two-gate initialization
once the initial head is typed. This is a conditional finite-history
lemma, with all chronological and selected-instruction constraints
explicitly retained. It does not encode a variable-length run or the
primary source's ordinary-TM-to-Wang cell codes. It changes neither
scalar ledger in Section3, and gives no whole-run arithmetic bound.

## 5. Why final-tape monotonicity does not certify past reads

Consider the legal four-instruction Wang program, with zero-based labels,

    0: J(3)
    1: M
    2: J(2)
    3: M

Start on an empty tape with the head at cell0. The exact execution is
0→1→2; instruction1 sets the scanned cell to1, and instruction2 then
self-loops forever. The repeated full configuration is an exact finite
certificate of nonhalting, not a timeout observation.

If every jump is instead evaluated against the proposed final tape,
the sequence0→3→HALT appears consistent with final tape{0}. Its first
jump sees the1 written only by the future instruction3. The tape is
monotone, its initial and final values are correct, and all listed
instructions are legal, yet this is not an actual run. Thus a verifier
that merely checks the union of initial and marked cells cannot replace
the tape at the time of each read by the final tape.

The single-AND graph in Section2 uses the current T and does not admit
this shortcut. A uniform Wang history still must bind successive tape
values, head positions and control states in chronological order.

## 6. Comparison with the current complete constructions

The arithmetic advantage is local: the one native AND simultaneously
certifies arbitrary-head typing and the read, and the mark adds two
additions by reusing a paid sum. It avoids a second independent native
head-power predicate. It is not directly comparable to the complete
303/301 polynomials or the75-certificate/87-polynomial frontier.

To get a complete ordinary-input bound from this model still requires
a fixed universal instruction list and its paid input encoding; an
unbounded common history of tape, head and instruction; and paid
instruction selection and jumps. Section4 accounts for translating a
finite literal Wang input/run into nonnegative bit coordinates, given
the stated initial head predicate and exact per-step relations. It does
not pay the primary source's input-cell encoding. Those codes suggest
a fixed-block recoder, not an already proved free loader. No whole-run
operation count, numerical universal table or reduction below301 follows
from the present scalar result.

The [receipt](wang_b_single_and_tape.json) records256 complete canonical
native residual/SOS identities,128 signed;31,744 low-block cases;
and512 positive outer extensions including zero tapes and idempotent
marks. The complete AND theorem supplies the positive native extension;
the fixtures do not materialize giant Pell tuples. The four-instruction
obstruction is checked by its exact lasso and the separate relaxed path.
The finite-run audit additionally compares physical set-of-cells
executions with independent integer-mask transitions:128 physical runs,
256 translated traces and6,530 translated steps. These include86
halting runs and61 runs visiting negative physical cells, as well as
two translation offsets per run. The checks include complete halting
traces and finite prefixes of nonhalting traces. They check the
two initialization gates and each state's scalar AND identity; it does
not materialize native Pell witnesses or a complete history polynomial.

```sh
python3 wang_b_single_and_tape.py
```

Review status: author writer and fresh default pass. Root's independent
proof/source review, primary PDF check and refreshed default pass,
including the finite-run addition.
Franklin's full proof/source review and refreshed default pass with no
findings. His additional independent checks cover192 complete
residual/SOS identities,96 signed;512 low-block cases on128-bit values;
and256 finite physical prefixes with7,010 steps, including800 left
moves. These are scalar and finite-trace checks, not a uniform history
certificate. All six local links resolve.
