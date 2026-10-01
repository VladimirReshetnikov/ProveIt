# Fixed binary input blocks with a synchronized initial counter

Every fixed binary clockwise machine can be preceded by a finite padding
normalizer whose binary input has exactly **four cells per input bit and
eight fixed frame cells**. On a positive integer's padded binary spelling,
it simulates the original machine on the spelling with leading zeros
removed. The new initial state is distinct from halt, all its nonhalting
instructions are defined, and its binary transition table is effectively
constructed here.

If the padded bit length `n>=2` is a power of two, its initial tape has
`4n+8` cells. The exact least-power-of-two counter required by the
[fixed halt bridge](binary_tag_fixed_halt_bridge.md) is therefore `8n`.
After the fixed word encodings, that counter and the ordinary input data
have **identical binary lengths**. A recoder scale can consequently serve
both; no assertion that an arbitrary oversized counter is valid is needed.

This is a machine normalization and word identity. Its source does not
pay for dyadic input length, recoding, or a complete tag-history polynomial.
Those are separate arithmetic interfaces. No new numerical universal
bound or explicit universal machine table is claimed here.

## 1. Machine convention and the finite binary compiler

A logical rule has the form

\[
          (q,A)\longmapsto (v,q'),\qquad |v|\in\{1,2\}.
\]

With the circular tape cut immediately before its head, a step takes
`A w` to `w v`: the head advances beyond the whole replacement to the
next old cell. This also specifies the order of a two-symbol write.
Halting is entry to one designated state with no instructions. All
nonhalting state/symbol pairs of the source machine are defined.

For an ordered alphabet of size `r`, choose a power of two

\[
 a\ge\max(2,1+\lceil\log_2 r\rceil),
 \qquad c(A_i)=0\,\operatorname{bin}_{a-1}(i),\quad 0\le i<r.
                                                        \tag{1}
\]

All codes have length `a` and begin with zero. Reserve `10^(a-1)` as a
temporary marker. The binary machine uses the following finite phases.

1. **Read and mark.** Starting at a block head, read its `a` old bits
   into finite control while replacing them by the marker. The stored
   code determines the logical instruction and its fixed output of
   length `a` or `2a`.
2. **Return to the marker.** Copy bits clockwise, counting positions
   modulo `a`. Test for the marker's leading one **only at block heads**.
   All other block heads are zero; ones inside their data cannot be
   mistaken for the marker. The first marker encountered is the one just
   written, after precisely all the other logical cells.
3. **Emit the replacement.** Consume the marker's `a` old cells. Write
   one output bit per old cell for a one-symbol logical write, or two
   output bits per old cell for a two-symbol write. Counting old marker
   cells, rather than new output bits, preserves the prescribed order.
   After the last old cell, enter the next logical checkpoint or halt.

The first emission consumes the marker's leading one; the remaining
old marker cells are zero. At completion the marker has disappeared,
the output is exactly one or two complete code blocks, and the head is
at the next old logical block. If the old tape has `N` logical cells,
the macro uses exactly

\[
                a+a(N-1)+a=a(N+1)                       \tag{2}
\]

binary transitions. This includes `N=1` and a transition to halt.
Thus the macro realizes the required tape cut `w c(v)` exactly, including
tape growth, and restores block alignment at every checkpoint.

All phases store only finite strings of bounded length and a residue
modulo `a`. Invalid codewords or malformed phase data enter a defined
nonhalting trap. The [checker](clockwise_dyadic_input_normalization.py)
constructs the literal finite binary table with both instructions for
every nonhalting emitted state. Its simulation checks execute those
instructions individually; they do not treat a macro as a free step.

## 2. Leading-zero normalization with `a=4,b=8`

Let `R` be any fixed binary clockwise machine with a distinct initial and
halting state. Introduce four logical symbols `L,R,P,F` in addition to
its data symbols `0,1`; here the frame symbol `R` is unrelated to the
machine's name. Start in a fresh state, with head at the left of

\[
                            L\,w\,R.                    \tag{3}
\]

After copying `L`, replace each leading zero by `P`. At the first one,
write `F` and scan clockwise, copying every symbol, until that unique
`F` returns. On reading it, execute the source machine's actual initial
instruction for data symbol one and enter its next state. This avoids
an unimplemented stationary move. In simulation states, execute source
instructions on `0,1`; on `L,R,P`, copy the symbol and retain the source
state. An unexpected `F` enters the rejecting loop.

If `w` denotes a positive integer, a first one exists. Erasing the
ignored `L,R,P` symbols from each source checkpoint gives exactly the
source machine's circular tape and head cut on `w` without leading zeros.
The initial return scan preserves all other bits, and all subsequent
source insertions contain only `0,1`. Between any two source steps the
finite ignored set is crossed in finitely many steps. Halting therefore
agrees in both directions. All-zero inputs enter a defined nonhalting
loop when the initial scan reaches the right frame.

Applying (1) to the ordered six-symbol alphabet gives the concrete codes

| Symbol | Code |
|---|---|
|`0`|`0000`|
|`1`|`0001`|
|`L`|`0010`|
|`R`|`0011`|
|`P`|`0100`|
|`F`|`0101`|

The initial binary tape is `c(L)c(w_1)...c(w_n)c(R)`, with its head
before `c(L)`, and has `4n+8` cells. The compiler's initial state is
fresh and nonhalting. The argument proves equivalence for **every**
leading-zero padding of every positive input, including padding to any
permitted dyadic length.

This result preserves the language of a given binary clockwise machine
on raw canonical binary input. It does not assume, without an input
encoding proof, that an arbitrary published universal binary machine
already has this convention.

For the existential semidecision application there is also a direct
finite-alphabet route. Choose an ordinary Turing machine that decodes
leading-zero-padded positive binary integers and halts exactly on the
desired set; rejected or malformed inputs loop. The primary
[Neary–Woods clockwise construction, Lemma2.1](https://mural.maynoothuniversity.ie/id/eprint/12416/1/Woods_FourSmall_2009.pdf)
represents its finite input by the individual input symbols and two
end markers. A fresh initial instruction on the left marker moves to
the original first input cell. Apply (1), ordering input zero and one
first, and the two frame symbols next. This yields the same shape (3)
with some fixed dyadic `a`, and two frame blocks of total length `b=2a`.
This use of a larger alphabet need not have `a=4`. It supplies an
effective fixed-machine input convention, not an arithmetic cost for
that machine or an explicit universal table.

## 3. The exact counter is linear in a dyadic duration

More generally, suppose the initial tape has `s0=an+b` cells, where
`a,n` are powers of two, `b>0`, and `an>=b`. Then

\[
                    an<s_0\le2an.
\]

Since `an` is a power of two, the **least** power of two at least `s0` is

\[
                  c_0=2^{\lceil\log_2 s_0\rceil}=2an.    \tag{4}
\]

For our shape `b=2a`, the condition is simply `n>=2`. In particular,
`a=4,b=8` gives `c0=8n`, including the boundary case `n=2` where
`s0=c0=16`. Every positive ordinary input admits arbitrarily long
dyadic padded spellings. No instruction of the normalized machine
needs to test whether that chosen spelling length is dyadic.

The imported [clockwise-to-cyclic-tag simulation, Lemma2 and its stage
tables](https://dna.hamilton.ie/assets/dw/NearyWoodsBCRI-04-06.pdf)
uses the exact counter (4). For its fixed number of states write
`z=30Q_machine+61`. With binary tape symbols identified with zero and
one, its initial word has the form

\[
 S_{\rm start}\,\tau(c(L))\,
 \tau(c(w_1))\cdots\tau(c(w_n))\,
 \tau(c(R))\,\mu^{2an},                                \tag{5}
\]

where `tau` acts on each physical tape bit and

\[
 \tau(0)=01\,0^{2z-2},\quad
 \tau(1)=001\,0^{2z-3},\quad \mu=10^{z-1}.
\]

The state and both frames in (5) are fixed. The initial head convention
agrees with Section2, and the initial state differs from halt, as required
by the fixed halt bridge. The machine table and all constants remain
fixed while `x,n` vary.

## 4. The complete word shares one scale

Use the fixed halt bridge's words `u,B_0,B_1` and its binary code
`e(b)=10^beta1,e(c)=1`. Put

\[
 G_i=e(B_i),\quad |G_0|=|G_1|=K,
 \quad \mathcal G(v)=G_{v_1}\cdots G_{v_{|v|}}.
\]

The complete binary endpoint is precisely

    PREFIX DATA_w1 ... DATA_wn MIDDLE MU^(2a*n) TAIL,

with all words most-significant-bit first and

\[
\begin{aligned}
 \mathrm{PREFIX}&=e(u^{[1]})\,\mathcal G(S_{\rm start}\tau(c(L))),\\
 \mathrm{DATA}_i&=\mathcal G(\tau(c(i))),\\
 \mathrm{MIDDLE}&=\mathcal G(\tau(c(R))),\\
 \mathrm{MU}&=\mathcal G(\mu),\qquad
 \mathrm{TAIL}=E(u).
\end{aligned}
\]

Here `E(u)=e(u without its final b)10^beta`. In particular,

\[
 D=|\mathrm{DATA}_i|=2azK,
 \qquad t=|\mathrm{MU}|=zK,
 \qquad |\mathrm{MU}^{2an}|=Dn.                         \tag{6}
\]

Consequently one recoder output `Q=2^(Dn)` supplies both lengths.
With `L_D=2^D-1`, the two repunits satisfy the exact identity

\[
 r=\frac{Q-1}{L_D},\qquad
 \frac{Q-1}{2^t-1}=\frac{L_D}{2^t-1}\,r.              \tag{7}
\]

The multiplier is a fixed integer because `D=2at`. If `v_i` is the
value of `DATA_i`, the data value is

\[
 v_0r+(v_1-v_0)\operatorname{spread}_D(x),\qquad
 \operatorname{spread}_D(x)=\sum_j\operatorname{bit}_j(x)2^{Dj}.
                                                               \tag{8}
\]

Sentinel-concatenating the fixed prefix, middle and tail with (7)–(8)
gives the complete initial word. The checker compares this nested
integer expression against the explicitly concatenated binary word.
This is the precise word-format contract for a separate paid loader;
division and exponentiation in (6)–(8) are mathematical identities, not
free arithmetic gates in a claimed certificate.

## 5. The ordinary-data coefficient is strictly positive

The fixed halt bridge's literal tracks give `u` the prefix `bcb`:
track zero consists of `b`, track one of `c`, and track two of `b`.
Thus `phi_0=b^6 u b^4` begins `b^7 cb`, while
`phi_1=b^8 u b^2` begins `b^9 c`. Appending the same `u^k` does not
change these prefixes. After the common binary prefix `e(b)^7`,
`G_0` starts with `11` and `G_1` starts with `10`. Their equal lengths
therefore give

\[
                              G_0>G_1                   \tag{9}
\]

in lexicographic and integer order. Notice the reversed bit labels.
At the first difference between `tau(0)` and `tau(1)`, their bits are
one and zero respectively. Equation (9) reverses that comparison, so
the two equal-length transported physical-cell codes satisfy
`G(tau(0))<G(tau(1))`. The input codes
`c(0)=0^a,c(1)=0^(a-1)1` then give

\[
                              0<v_0<v_1.               \tag{10}
\]

Both codes contain ones after transport, which supplies the first
strict positivity in (10). In particular, the coefficient `v1-v0`
in (8) is a fixed **positive** integer, independently of arithmetic
typing or equations. The folded counter loader can therefore use
positive input expressions directly for this particular interface;
an arbitrary pair of blocks would not justify that conclusion.

## 6. Executable evidence and remaining interface

The [source](clockwise_dyadic_input_normalization.py) and
[receipt](clockwise_dyadic_input_normalization.json) check 512 exact
binary macro simulations on eight logical alphabet sizes, including
two-symbol writes, single-cell circles and halting transitions. They
also execute 72 complete normalized traces of three actual binary
machines, comparing every source checkpoint and every compiled binary
microstep. These cover immediate halting, two-state insertion and an
unbounded nonhalting insertion example, each with several positive
inputs and leading-zero paddings. Eight all-zero cases enter the
defined rejecting loop.

Further checks compare 96 complete framed word values and both repunits
at dyadic durations, and inspect 16 actual fixed-halt track constructions
for the exact first unequal bit in (9). These are finite checks of the
proved constructions, not numerical full native-kernel zeros or a
materialized universal machine.

The remaining arithmetic composition must enforce dyadic `n>=2`,
provide the recoder's matching `Q` and spread value, pay the relation
defining `r`, and connect the computed sentinel to a complete tag-history
predicate. This packet removes ambiguity about the machine's initial
format, padding invariance, exact counter and coefficient sign. It
does not silently discharge those arithmetic obligations.

Independent review: native_controller checked the complete proof, actual
source and fresh default replay, and reopened both primary simulation
sources; no findings. A separate circular-array simulator verified 288
local macros and 96 whole normalized traces, comprising 870 original
source steps and 213,430 actual binary microsteps. This simulator uses
array replacement and an explicit moving head rather than the checker's
queue representation.

Root independently reviewed the full proof and source, passed a fresh
default replay, and reopened primary Lemma2.1. The head-after-whole-write
convention was checked against both right-boundary examples and the
literal bi-tag rule `e_x a_i -> a_j a_k e_y`; no findings.
