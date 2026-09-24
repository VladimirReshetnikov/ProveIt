# An internal blank loader saves one raw-input operation

The constant-length queue of
[the preceding14-operation component](EXPLORATION_CONSTANT_LENGTH_RAW_QUEUE.md)
has a separate **13-operation successor, 6M+7A**. Its initial queue is just
the padded ordinary ternary digits of x followed by `#`. A finite delayed
loader turns the last raw zero into a genuine blank, preserving length and
numerical input. It rejects a nonzero final raw digit. Existentially choosing
more zero padding supplies both that zero and enough eventual work space.

This preserves the complete ordinary-input machine theorem and removes one
initialization multiplication. All append products remain ordinary scalar
products with a constant W, and both final contents remain exactly zero.
The result is a machine contract and a counted conditional component, not a
complete Diophantine certificate: the arithmetic controller, field typing,
power geometry and Pell realization are still unpaid. The preceding files
are unchanged and are imported as frozen dependencies by the new checker.

## 1. Three paid initialization instructions

Retain the preceding nine-symbol alphabet: ordinary trits are `(a,0)`,
ordinary blank is `(0,2)`, delimiter is `(0,1)`, and the four marked cells
are `(1,1),(2,1),(1,2),(2,2)`. All nine pairs occur exactly once.

Choose a padding power `L=3^ell>x` and use

    I0=x,       I1=L,       W=3L,       R=3W,
    x+alpha=L, alpha>0.                                    (1)

The symbolic initial word is

    d0 d1 ... d_(ell-1) #,

where the di are the ordinary little-endian ternary digits of x padded
to ell places. Its two values are precisely x and L, and its constant
length marker is W. There is no initial blank supplied arithmetically.

The only instructions are `W=3*L`, `R=3*W`, and `input_bound=x+alpha`,
compared with L. Thus the initial interface costs **3=2M+1A**. The old
product I1=5L is gone because the second input coordinate is now L itself.
The inequality x<L is retained and paid; no carry-based input alias is
being allowed in its place. The stronger condition x<3^(ell-1), when
needed for a successful loader, is checked by the loader's actual final
raw digit, not by an uncounted arithmetic bound.

The powers L=3^ell and q=R^t for the same finite run are external geometry
obligations. If surrounding geometry proves R divides a power of three,
R=9L proves L is a power of three. Neither that divisibility condition nor
the common history power has been compiled by (1).

## 2. Delayed loading creates exactly one blank

On its first queue transition the loader requires a raw ordinary trit.
It holds the marked version of that cell in finite control and appends
a provisional delimiter. On each subsequent raw trit, it appends the
held cell and holds the newly read trit unmarked. Thus it delays emission
by one cell, without deleting or inserting any physical queue symbol.

At the original delimiter it checks the held raw digit:

* If that digit is nonzero, enter the rejecting rotation loop, re-appending
  the delimiter. Its nonzero input contribution is never silently erased.
* If that digit is zero, append a genuine blank instead of the held zero.
  If the held cell also carries the initial mark, preserve that mark on
  the blank; this is exactly the one-raw-cell case.

The queue is then the provisional delimiter followed by the processed
tape. One extra transition rotates that delimiter to the end and enters
the fixed normalizer of the preceding construction. For ell>=2 and a
zero high raw digit, the exact tape is

    marked d0, d1, ..., d_(ell-2), blank.                     (2)

Removing the high zero leaves the numerical value x unchanged. The loader
has used ell+2 transitions and preserved queue length ell+1 throughout.
It stores only one cell and a finite phase flag, independently of x and ell.
Any malformed input event enters the rejecting loop. All transitions,
including rejection, remove and append exactly one of the nine symbols.

The small cases are explicit. For ell=0 the initial queue is just `#`,
which the first-step rule rejects. For ell=1 a nonzero raw digit is rejected
at the original delimiter. A sole raw zero becomes a marked blank; the
mandatory normalizer sees a blank at its initial leftmost cell and rejects.
Thus no ell=0 or ell=1 input can accidentally accept. These rejections do
not prevent any nonnegative integer from using a larger padding.

## 3. Exact ordinary-input universality is retained

For a valid loading, the inherited normalizer starts with the trits in (2),
a true blank, and the head at zero. It scans to that blank, then erases
high raw zeros until the highest nonzero trit; for x=0 it keeps one zero.
It returns to the left endpoint. Its tape then consists of canonical(x)
followed by blanks, on a physical tape of exactly ell cells. Its steps all
fit within that interval.

For any recursively enumerable set, fix a four-symbol one-sided machine M
recognizing the canonical ternary input, preceded by this normalizer. If M
accepts x and its accepting run visits only positions through S(x), choose
ell>=2 so large that x<3^(ell-1) and ell>S(x). The loader succeeds, the
normalizer establishes precisely the fixed canonical configuration, and
the entire accepting computation fits. If a smaller padding exhausts the
tape, the inherited queue scan detects the left or right overflow and
rejects before committing the next machine state. Such a finite bounded
accepting computation is also an accepting computation of M on its
unbounded right-blank tape. Therefore some padded run accepts exactly
when x is in the chosen set.

This is a statement about existential padding and a fixed normalization
procedure. It assumes no space bound for M on varying padded input words;
M always starts from the same canonical infinite-tape configuration.
The compiler, loader, normalizer and machine remain fixed as x varies.

The inherited work scan emits a provisional delimiter at its first data
cell, then held predecessors, then the last held cell at the old delimiter,
and finally rotates the provisional delimiter. The inherited erasure pass
after a genuine accepting state replaces every tape cell and the final
delimiter by ordinary zero. These rules still preserve physical length
at every step. Their direct Turing-step proof, including both boundary
rejections, applies unchanged to the new tape length ell.

## 4. Zero endpoints and strictly positive history coordinates

During loading the old delimiter remains present until its provisional
replacement has been emitted. Loading rejection preserves a delimiter.
After loading, every valid work scan and every rejecting loop preserves
at least one delimiter until the final accepting erasure. During that
erasure the delimiter is ahead of the newly appended zeros until its own
last step. Consequently the two coordinates can both become zero only
when the complete accepting erasure has finished. Conversely that pass
ends in the all-zero word. No separately imposed final controller state
is needed once the initial control and all table transitions are verified.

All six packed histories X0,X1,D0,D1,A0,A1 remain strictly positive on
every true accepting run. A successful loader has ell>=2. It appends its
initial marked cell before the last raw zero becomes blank, and the
mandatory normalizer later reads that marked cell. Every marked cell has
positive first coordinate. Thus A0 and D0 have a nonzero digit, including
when x=0, and X0 records a queue containing that marked cell. The loader
both reads a delimiter and appends its provisional replacement, so D1 and
A1 have nonzero digits, while the initial value L makes X1 positive.
If x>0, a nonzero raw input trit already supplies the corresponding first
coordinate witnesses during the initial pass.

L,W,R and alpha are positive. Individual source rows may have zero content
or zero head/append coordinates; those are packed digits and do not need
separate positive existential variables. Both final coordinate values are
the literal zero, not extra positive witnesses.

## 5. The complete13-operation initialization/transport source

Let a true run take t transitions and put q=R^t. For each coordinate i,
pack source contents nij, removed trits dij and appended trits aij at the
same time positions:

    Xi=sum nij R^j, Di=sum dij R^j, Ai=sum aij R^j.

The scalar W has the same value on EVERY source row, including loader,
normalization, work scans and erasure. Therefore

    3*n_i,j+1=nij-dij+W*aij,
    R*(Xi-Di+W*Ai)=3*(Xi-Ii).

Since R=3W and I0=x,I1=L, the two complete transports are

    W*(X0-D0+W*A0)=X0-x,
    W*(X1-D1+W*A1)=X1-L.                                 (3)

Each costs five operations: `weighted=W*Ai`, `cut=Xi-Di`,
`appended=cut+weighted`, `left=W*appended`, `right=Xi-Ii`.
The two products `W*Ai` are genuine scalar products. There is no weighted
selector field, packed length field or length transport. Zero endpoints
justify omitting both possible q*Fi products and their additions.

Together with (1), this is **13=6M+7A**, with five independent source
equalities. The checker expands every paid instruction against those
sources and verifies the exact off-shell identity

    old_i-3*new_i=(R-3W)*(Xi-Di+W*Ai).

Every true row satisfies nij<W, dij,aij<=2, and

    nij+W*aij<R, dij+3*n_i,j+1<R.

These strict bounds follow from the constant physical queue and R=3W.
They are not automatically recovered from arbitrary integer solutions of
(1),(3). That recovery, finite-control selection and the common row masks
are precisely part of the still-unpaid arithmetic compiler. The short
component alone neither proves a complete count below75 nor supplies a
lower bound against a future improved compiler.

## 6. Evidence and unchanged predecessor

`../verification/explore_delayed_blank_raw_queue.py` imports the frozen
preceding implementation, replacing only its loader and arithmetic
initialization. Its receipt stores SHA256 hashes of all three predecessor
artifacts after canonical LF normalization. The predecessor is not edited
or assigned a smaller operation count.

The author check expands all13 instructions and five source residuals.
An exhaustive loader/normalizer/erasure test covers all1,093 initial raw
words with ell=0,...,6: 363 valid accepting words and 730 rejections.
It checks37,724 queue transitions and all363 positive packed transports.
The rejected cases include the sole ell=0 input, all three ell=1 inputs,
and726 higher inputs with a nonzero final raw digit. This accepting-client
fixture accepts exactly ell>=2 with x<3^(ell-1).

Seven fixed clients compile to687 reachable controls and all6,183 table
entries. Across420 padded inputs the checker records287 successful loads,
280 exact canonical normalizations,6,575 direct Turing steps and54,228
queue steps, including1,400 rejecting-loop steps. Its100 accepting runs
check the exact zero endpoint, both complete packed transports, and the
positivity of all six history words. There are280 rejections and40 bounded
observations of the explicitly stationary nonhalting client; no arbitrary
cutoff is classified as divergence. Twenty inputs in a workspace fixture
reject with insufficient padding and accept with larger padding.

The unchanged complete single-scan enumeration checks all15,024 choices of
tape length one through four, tape contents, head, written symbol and move:
12,304 valid passes and1,360 rejections at each boundary, with79,200 queue
steps. During every exercised whole-run step, the checker independently
tests constant length, both scalar coordinate equations, strict radix
bounds and the equivalence of a zero word with completed erasure.

These finite results corroborate the generic proof; they are not an
arithmetic encoding of an arbitrary controller or a full Pell witness.
Default execution requires and compares the saved receipt; `--write`
regenerates it. Author and two independent complete scoped proof/source
reviews pass, as do fresh exact receipt replays. Publication is a separate
gate from these mathematical and executable checks.
