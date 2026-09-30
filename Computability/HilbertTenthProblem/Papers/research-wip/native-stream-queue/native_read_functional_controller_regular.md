# A finite controller cannot rescue read-functional equal-length rewriting

Suppose that a fixed queue machine appends the same symbol `f(a)` whenever
it reads a physical symbol `a`. An arbitrary synchronized finite controller
may permit or forbid that step and choose its next control state. It may be
nondeterministic, and its transition table may be nonlinear. Nevertheless,
the language of finite initial queue words from which the machine can reach
an all-zero queue and an accepting control state is **regular**.

The theorem includes existential queue width and duration, a prescribed
first transition, any finite collection of positive-stream requirements,
and fixed congruences on width and duration. The zero symbol need not be
absorbing. Consequently ordinary numerical input followed by existential
zero padding and a fixed delimiter still gives a regular numeral language.
A fixed computable input substitution preserves decidability, although it
need not preserve regularity.

This strengthens the [stateless FIFO theorem](native_stateless_fifo_regular.md)
in a different direction: it allows genuine synchronized control but requires
that the physical rewrite be a function of the read symbol. In particular it
closes the variable-width gap explicitly left in Section 5 of
[the NAND composition note](native_controller_nand_composition.md). It does
not classify controllers with two possible appended symbols for the same
physical read symbol. No new arithmetic schedule is proposed, and the
established complete universal certificate remains **75=41M+34A**.

## 1. Machine, control, positivity, and arithmetic interface

Fix a finite alphabet `Sigma` with a distinguished zero symbol `z`, a
function `f: Sigma -> Sigma`, and a finite control-state set `Q`. For each
read symbol `a`, let `E_a` be an arbitrary relation on `Q`. A step is

    (a v, s) -> (v f(a), s') whenever (s,s') is in E_a.       (1)

The queue has a positive constant physical length. There are fixed initial
and accepting control-state sets. A partial rewrite function is covered by
adding a sink symbol with no permitted controller transitions; any transition
actually present still has the prescribed unique output. Duplicate labels
with the same read and append symbols are permitted.

All extra restrictions in the theorem can be included in finite state:

- A flag for each required positive native stream records whether a nonzero
  digit has occurred. A native nonnegative digit word is positive exactly
  when its flag is set. Requiring every selector label to occur is handled
  by the same construction, even with duplicate physical rows.
- A one-time entry state can enforce a specified first labeled edge.
- A finite clock can impose any fixed duration congruence. Width congruences
  are checked by the finite recognizer of initial words.

Thus it suffices to prove the theorem for the finite relations `E_a`; the
state space may already include all these flags. No uniform bound on its
size is assumed. It is fixed independently of the varying ordinary input.

In a paid native queue component, `q=b^t` and `W=b^m` and the actual bounded
read and append words satisfy

    D_i=I_i+W*A_i, 0<=I_i<W, 0<=D_i,A_i<q.                 (2)

The standard FIFO identity makes (2) equivalent to the actual `t`-step
zero-reaching run in each lane. Applying the theorem assumes that the
containing certificate has proved this geometry and typing; powers,
divisibility, digit extraction and bounds are not free new primitives.
When the original source has an exact positive-witness converse, its
strictly positive streams are represented by the flags above. The positive
Pell coordinates are supplied by that existing converse, not by a new or
numerically materialized witness construction here. A source with additional
non-finite-state equations is outside this exact projection theorem; one
cannot infer regularity of an arbitrary subset of a regular language.

## 2. Powers of the physical rewrite have a finite phase

The sequence of functions `id,f,f^2,...` is eventually periodic. This needs
only finiteness: there are at most `|Sigma|^|Sigma|` functions on `Sigma`,
and equal powers have equal successors. Compute integers `alpha>=0` and
`beta>=1` with

    f^(alpha+beta)=f^alpha.

Let `J={0,...,alpha+beta-1}`. Write `nu(r)` for `r` before `alpha` and for
`alpha+(r-alpha mod beta)` thereafter. For `j` in `J`, define
`g_j=f^j`, and let `next(j)` be its successor phase. Then

    f^r=g_nu(r), g_next(j)=f composed with g_j.             (3)

Only this fixed finite phase set is used below. In particular no claim
that every queue reaches zero, or that zero remains zero, is needed.

Let `R` be the finite monoid of binary relations on `Q`, with relational
composition in temporal order. It has at most `2^(|Q|^2)` members. For a
word `v=a_0...a_(k-1)` define

    M_j(v)=E_g_j(a_0) ... E_g_j(a_(k-1)),                  (4)
    M_j(empty)=identity.

For every phase, `M_j(uv)=M_j(u)M_j(v)`. The vector `(M_j(v):j in J)`
is consequently a finite-monoid summary that a finite automaton can
compute as it reads `v`. Let `C(v)` also record the finite set of symbols
occurring in `v`.

## 3. Exact full sweeps and an arbitrary final partial sweep

For a nonempty initial word `w` of length `m`, write a duration uniquely as
`t=hm+p`, where `h>=0` and `0<=p<m`. During full sweep `r`, the controller
reads exactly `f^r(w)` in the original order. Thus the full-sweep controller
relation is

    P_h=M_nu(0)(w) ... M_nu(h-1)(w), P_0=identity.          (5)

Nondeterministic control does not change the symbols: every permitted step
still rewrites `a` to the same `f(a)`. Relation multiplication in (5)
retains exactly all compatible choices of controller states.

Write `w=uv`, with `|u|=p` and `v` nonempty. After the final partial sweep,
the physical queue and the total control relation are exactly

    f^h(v) f^(h+1)(u),
    P_h M_nu(h)(u).                                      (6)

Therefore this run accepts exactly when the relation in (6) connects an
initial control state to an accepting one, and

    g_nu(h)(a)=z       for every a in C(v),
    g_next(nu(h))(a)=z for every a in C(u).                (7)

Equations (5)--(7) retain correlations created by the synchronized
controller. This is why the earlier independent-token argument alone did
not settle this case.

For a fixed vector `(M_j(w))`, iterate the finite deterministic map

    (P,j) -> (P M_j(w), next(j)), starting at (identity,0). (8)

It has at most `|J|*2^(|Q|^2)` states. Stop at the first repeated pair.
Every pair `(P_h,nu(h))` has then appeared; subsequent pairs only repeat.
For each visited pair, (6)--(7) are a complete acceptance test for any
chosen cut. This is an effective decision procedure over all durations,
without any numerical time cutoff.

## 4. A finite recognizer works uniformly over all queue widths

Construct a finite automaton that guesses a cut `w=uv`, requires `v` to
be nonempty, and accumulates

    ( (M_j(u))_j, (M_j(v))_j, C(u), C(v) ).                (9)

There are finitely many possible values of (9). From them one recovers
`M_j(w)=M_j(u)M_j(v)` for every phase. Acceptance is the finite test obtained
by iterating (8) and applying (6)--(7). Thus the accepting values of (9)
form a finite effectively computable set. This is a finite automaton for
exactly the initial words that admit an accepting run.

This establishes **regularity uniformly in the existential width**. It is
stronger than separately deciding each fixed queue graph. It also explains
why no bound on a user's input or on the number of sweeps was silently
introduced. A restriction to any fixed congruence class of `m=|w|` is a
finite additional clock. A duration clock was already incorporated in
`Q`, so restrictions such as even `m` and even `t` remain regular.

## 5. Ordinary input, padding, and the three-row consequence

Let `i` embed radix-`b` digits into `Sigma`, with `i(0)=z`. Let `#` be a
fixed delimiter, if the intended input interface uses one. Write `digits_b(x)`
for the canonical low-to-high digit word of a positive ordinary integer.
For the usual input interface the initial words are

    i(digits_b(x)) z^k #, k>=0.                          (10)

The no-delimiter version omits `#`. If `K` is the regular language proved
above, mark a state of its finite automaton accepting exactly when some
suffix `z^k #` leads to an old accepting state. The requisite states are
computable by finite graph reachability. Pull back along the fixed digit
map `i` and restrict to nonempty canonical positive numeral words. This
recognizes exactly the accepted ordinary inputs. Width positivity and the
strict bound `b^m>I` are realized by the actual input format. An additional
fixed amount of padding is another fixed regular suffix condition.

For a fixed positive computable input substitution `P`, evaluating `P(x)`
and running this numeral-language decider proves decidability of the
resulting `x`-language. This includes every fixed positive integer
polynomial and fixed affine marker. It does **not** assert that such
polynomial preimages are regular, or that computing `P` is arithmetically
free. A paid input bridge with additional history constraints requires its
own exact projection and is not replaced by this observation.

In particular, three fixed physical selector rows that cover all three
ordinary ternary read symbols necessarily assign exactly one append symbol
to each read symbol. Any synchronized finite controller leaves this rewrite
read-functional, so the theorem applies. This supplies the missing
variable-width conclusion in the earlier three-label discussion.

For the direct scalar initial integer `x`, any controller accepting every
positive even input must process every read trit: input `2` forces trit `2`,
input `4=(11)_3` forces trit `1`, and input `6=(20)_3` forces its low `0`
before the higher nonzero trit can disappear. With initial integer `2x`,
the corresponding even inputs `x=2,4,6` give `(11)_3,(22)_3,(110)_3`.
Thus an exact three-row direct-input representation of a set containing
all positive evens must use all three read trits and is decidable by this
theorem. It cannot represent the union of all positive evens with a
nonrecursive computably enumerable subset of the odds. The same conclusion
for another initializer requires proving its read-coverage property; no
unpaid change of encoding is assumed.

## 6. Fixed affine carry controllers are included

Suppose a proposed synchronized controller is specified by fixed integers
and the integral recurrence

    b*c_(j+1)=c_j+kappa(label_j), c_0=c_start, b>=2,        (11)

where the finitely many labels have fixed increments. Put

    B=max_label |kappa(label)|,
    C=max(|c_start|,ceil(B/(b-1))).                       (12)

Every carry stays in `[-C,C]`: if `|c_j|<=C`, then
`|c_j+kappa|/b <= (C+B)/b <= C`. Hence integral transitions in (11) form
an actual finite controller, without assuming an unproved state-range
filter. A specified terminal carry is a finite accepting-state condition.
Several such recurrences give the finite product of their carry ranges.
Any further fixed finite-state or regular guards are also included.

Consequently neither extra finite-state control nor any finite number of
these bounded affine carry equations repairs a read-functional physical
rewrite. This does not extend to unbounded nonlinear carry updates,
state-dependent physical rewriting, variable-length tag deletion/production,
or additional equations coupling the word to arbitrary arithmetic data.
Those are substantive directions outside the obstruction. In particular,
the complementary-lane queue has two physical outputs for every read pair,
so the theorem does not collapse its still-open controller family.

## 7. Independent evidence

The [checker](native_read_functional_controller_regular.py) implements two
independent algorithms: full physical queue/controller graph reachability,
and the full-sweep monoid procedure (5)--(8). Neither uses a duration cutoff.
It exhausts every binary rewrite function and every pair of binary relations
on a two-state controller, on all binary queue words of lengths 1 through 4.
Further ternary fixtures exercise all 27 rewrite functions, partial and
nondeterministic controllers, a prescribed first edge, even width/time,
nonzero-read and nonzero-append flags, and a nonabsorbing zero symbol.
The [receipt](native_read_functional_controller_regular.json) records counts.

These finite comparisons validate the algorithms on those domains. The
regular-language conclusion for arbitrary alphabets, controllers and widths
is the mathematical proof above. No existing source or receipt is modified,
and no complete universal improvement below 75 is claimed.
