# A fixed binary-tag production with external simulation input

The input-bearing bootstrap in the binary-tag construction can be removed
on the **valid clockwise-Turing-machine simulation slice**. For each fixed
binary clockwise machine, the construction below gives one fixed deletion
number and one fixed production `u`. Its external input is a fixed block
morphism of the cyclic-tag initial configuration. It halts exactly when
the machine halts, and every such halt reaches the singleton `b`.

The delicate point is a unique pending halt activation. We prove it from
the actual machine encoding, rather than assert it for arbitrary cyclic-tag
data. The external initial configuration still contains a power-of-two
tape-length counter. **That counter has not been loaded by a paid ordinary
integer certificate.** This packet therefore supplies no new universal
arithmetic bound. The complete encoded-input predicates in
[the four-tile packet](binary_tag_four_tile_history.md) and
[its normalized successor](pcp_normalized_strong_history_units.md) retain
their existing scopes.

## 1. The imported simulation contract

The primary [Neary–Woods construction, Lemma2 and Tables1.1–3.2](https://dna.hamilton.ie/assets/dw/NearyWoodsBCRI-04-06.pdf)
simulates a binary clockwise machine with `Q` states using `p=2z`
appendants, where `z=30Q+61`. The initial tape has `s0` cells and its
counter has `c0=2^ceil(log2(s0))` copies of `mu=10^(z-1)`.
Its halt convention is the distinguished self-copying state appendant.
[Neary's published STACS2015 Lemma9](https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf)
adds parity-based tag cleanup and an input-bearing bootstrap. We retain
the simulation and cleanup idea, supply the input externally, and prove
the necessary first-halt invariant below.

Use `Q>=2`, initial state distinct from halt, and at least two initial
tape cells. Clockwise transitions preserve or increase that number.
Nonaccepting undefined instructions may be replaced by a nonhalting
loop. Thus “halts” denotes the intended semidecision event. These are
fixed-machine conventions, not existential input conditions.

The printed STACS Table2 contains `u` in positions purported to be
literal binary tracks, and the following halt paragraph retains older
`6h` indices. We do not use those expressions as literal rules. Section3
defines complete `b,c` tracks and proves their outputs directly.

## 2. Exactly one pending halt activation

Put

\[
 h=30Q+20,\qquad S_h=0^h1\,0^{2z-h-1}.
\]

The halt appendant is `alpha_h=S_h`. In the valid simulation, its first
activation occurs when this unique state object is read with initial
marker zero. Before the halt state is reached, the other state rows in
Tables1.1–3.2 cannot activate index `h`. This can also be checked directly
from their indices: the only unshifted state offset congruent to20 modulo30
is `30i+20`; here `i<Q` until halting. The shifted state offsets, transition
indices, passive indices and counter-reset indices have different residues,
or lie strictly below `h`. The checker lists all these table-index families.

Immediately after the `1` in `S_h` is read, its unprocessed suffix consists
of zeros. All other queued encoded objects are passive tape or counter
objects: their lengths are `z` or `2z`, their unique `1` lies at an offset
in `{0,...,6}`, and their initial marker is zero or `z`. This includes
partially marked counters if the dataword is viewed at a cyclic cut.
Their activation indices belong to

\[
                  \{0,\ldots,6,z,\ldots,z+6\},
\]

which does not contain `h`. At a standard configuration the counter has
an even number of `z`-blocks, because `s0>=2`; the whole word has length
divisible by `2z`. The state is entered at marker zero, including after
the one or two write-symbol blocks preceding it in a completed transition.
No other state object is present. This is the concrete simulation
invariant supplied by the stage tables, not a restriction on all binary
datawords.

Consequently, **no further `h` activation occurs while the portion already
queued after that first state bit is consumed once**. Appended outputs go
behind the new halt output and cannot invalidate this statement. This
FIFO observation is essential: a later copy of `S_h` would activate `h`
again in the unmodified cyclic-tag system, but it is not reached before
the first appended halt output.

## 3. Fixed literal binary-tag rules

More generally, take fixed appendants `alpha_0,...,alpha_(p-1)`, with
`p>=2` and a distinguished `0<h<p`. Put `beta=10p`, `M=beta-1`, and choose

\[
 s\ge 11\max(p,\max_m|\alpha_m|)+3,\qquad s\equiv1\pmod M.
\]

Define the short words

\[
 \theta_e=b^4cb^6,\quad\theta_0=b^6cb^4,
 \quad\theta_1=b^8cb^2,
 \qquad z_m=(\beta-10m+1)\bmod\beta.
\]

For a binary word `a`, `theta(a)` is the concatenation of its short words.
For a word starting with `b`, a superscript minus below deletes that first
letter. Define `u` by interleaving the following `beta` tracks, each of
length `s`; all track indices are modulo `beta`.

| Track | Literal word |
|---|---|
|Every even index; every index9 modulo10|`b^s`|
|`z_m`|`c^s`|
|`z_m-4`, `z_m-6`, with `m>0`|`theta_e^p c^(s-11p)`|
|`z_0-4`, `z_0-6`|`(theta_e^p)^- c^(s-11p+1)`|
|`z_m-8`, `m>0`, `m!=h`|`theta(alpha_m)c^(s-11|alpha_m|)`|
|`z_0-8`, `alpha_0` nonempty|`theta(alpha_0)^- c^(s-11|alpha_0|+1)`|
|`z_0-8`, `alpha_0` empty|`(theta_e^p)^- c^(s-11p+1)`|
|`z_h-8`|`b c^(s-1)`|

These are disjoint track classes. In particular, the old input bootstrap
track `beta-1` is now simply `b^s`. Thus `u` depends on the appendants and
`h`, not the input data. It has length `beta*s` and begins and ends in `b`.
The two tag rules are `b -> b`, `c -> u`, with deletion number `beta`.

Let `phi_a` be `theta_a` with its `c` replaced by `u`. The objects `phi_a`
have length `beta*s+10`, so processing one changes entry shift from `z_m`
to `z_(m+1)`. A `u` object preserves the shift. Directly reading every
`beta`th letter gives the following exact local behavior.

For `m>0`, `phi_1` appends `phi(alpha_m)u^(s-11|alpha_m|)` unless `m=h`.
The `phi_0` and `phi_e` objects append `phi_e^p u^(s-11p)`. At `m=0`, an
extra initial `b` is read; the deleted first `b` in the table restores the
same output, with one extra `u`. Empty `alpha_0` uses the garbage row.
A `u` object appends `u^s`. A block `phi_e^p` has net shift zero and is
garbage, just as `u` is. Finally, at the distinguished event `phi_1`
appends

\[
                         H=b\,u^{s-1}.                 \tag{1}
\]

These statements follow by substituting `b -> b,c -> u` into the literal
read tracks; they do not depend on the defective printed entries.
Every normal read track has at least three final `c` letters. Its first
such letter is read while at least a full deletion block still remains,
then appends an entire `u`. Thus normal object processing cannot cause
premature tag halting, even when only garbage remains. FIFO ensures that
finitely many queued garbage objects do not prevent a later data object
from eventually being read. The usual cyclic-tag simulation therefore
holds up to the first distinguished event; ordinary cyclic-tag emptiness
alone is not treated as a halting event here.

At that event, Section2 implies that no second `H` is appended before the
first reaches the front, on the valid machine slice. Garbage may pass
through marker `h`, but `phi_e` uses its own track and never triggers (1).
The first `H` is entered at an odd shift. Its one leading `b` makes every
`u` within it be entered at an even shift. Its total length is odd, so
the following normal blocks are also entered at even shifts. Every such
block has even length, even `b` prefixes, and only `b` letters on its
even `u` tracks. The finite remainder of the queue therefore produces
only `b` letters. After it is consumed, the queue is entirely `b`, and
each step shortens it by `beta-1` until it halts.

Conversely, before an `H` event only the nonhalting normal simulation
occurs. Thus on valid initial configurations of the fixed clockwise
machine, this fixed binary-tag system halts **if and only if** that
machine halts. No arbitrary-CTS multiple-hit theorem is asserted.

## 4. A fixed block morphism enforces the singleton endpoint

Let `k=(-11) mod M`, with `0<=k<M`, and put

\[
 B_i=\phi_i u^k,\qquad
 W(w)=u^{[1]} B_{w_1}\cdots B_{w_n}u,\qquad n\ge1.    \tag{2}
\]

Here `u^[1]` means `u` with its first letter removed. It is read on
track1 and leaves the next object at shift1, initializing marker zero.
The inserted `u` objects do not change the simulation. Since

\[
 |u|\equiv1\pmod M,\qquad
 |B_i|=(k+1)|u|+10\equiv k+11\equiv0\pmod M,
\]

every `W(w)` ends in `b` and has length1 modulo `M`, for every input
length. The same residue is preserved by both tag rules. Any halted
nonempty word has length at most `M`; therefore it is exactly the
singleton `b`.

The two blocks have equal `b,c` contents. Under the four-tile code
`e(b)=10^beta1,e(c)=1`, they consequently have equal encoded length.
Writing `E(v)=e(v without its final b)10^beta`, the complete boundary is

\[
 E(W(w))=e(u^{[1]})\,e(B_{w_1})\cdots e(B_{w_n})\,E(u). \tag{3}
\]

This is a fixed prefix, two equal-length bit blocks, and a fixed suffix.
It has no input-dependent production or input-length-dependent padding.
The four-tile word equation therefore characterizes machine halting at
the encoded input sentinel `[E(W(w))]` on this slice.

## 5. The remaining ordinary-input counter contract

The word `w` in (2) is the whole cyclic-tag initial configuration, not
the ordinary input integer's binary spelling. It contains the state,
the encoded tape, and `mu^c0`, where

\[
                       c_0=2^{\lceil\log_2 s_0\rceil}.
\]

No additional freedom to use an arbitrary larger dyadic counter is
needed or proved here. The source keeps this exact initial relation.
If `K=|e(B_0)|`, loading the counter block requires the binary scale
`2^(K*z*c0)`. A recoder for an `n`-bit ordinary input supplies `2^n`
and `2^(K*n)`, not this scale. Even a future proof permitting
`c0=2^n>=s0` would instead require `2^(K*z*2^n)`. Independent power
witnesses do not identify these exponents. This remaining interface must
be paid or eliminated before claiming an ordinary-input universal bound.

## 6. Executable evidence

The [checker](binary_tag_fixed_halt_bridge.py) and
[receipt](binary_tag_fixed_halt_bridge.json) independently materialize
small fixed track tables, extract every relevant read track, verify every
even cleanup track, check fixed padding and complete binary endpoint
frames, list the primary activation-index families, and inspect rotated
standard halt configurations with the exact counter. The all-`b`
cleanup recurrence is also checked. These finite checks support the
parametric proofs; they do not instantiate a universal production, solve
the missing counter interface, or replace the primary simulation theorem.

```sh
/tmp/diophantine-research-venv/bin/python binary_tag_fixed_halt_bridge.py
```

Author replay and two independent full proof/source/default reviews passed.
Both reviewers checked the primary stage tables, the first-halt FIFO cut,
and the retained counter limitation. Additional independent checks covered
342 literal object tracks at `p=7,...,12` and512 mixed passive-cut component
fixtures. The latter test the local index exclusion; they are not claimed
to be additional reached machine configurations. No review findings remain.
