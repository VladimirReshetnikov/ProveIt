# Permuting the complete AX output family

Research note, 18 October 2026. This is an ordinary mathematical proof about
the abstract enumerator and a symbolic checker of its stack contracts. It is
not a new binary-machine certificate. The new search dimension is arbitrary
ordering of the **eight complete logical rows**, keeping GEN first and the
gated bundle last in the actual emitter. Previously located complete-grammar
experiments preserved the logical-row order. Older four-row permutations
belong to the retired equality-free experiment.

## 1. Scope and source audit

The prior-art enumerator is in
`lib/jeff-busy-beaver-zfc254/ZF/m254/tools/logic/spec.py`; its existing proof
compiler is `tools/logic/compiler.py`. The mathematical statements below use
their exact command effects. The original emission order is

    GEN, rho8, rho7, rho6, rho5, rho4, rho3, rho2, rho1, bundle.

`full_grammar_experiment.py` preserves the complete primitive AX word.
`layout_grammar_experiment.py` preserves the first 88 primitive calls,
including all eight rows in their original order, and changes only the
conjunction layout and grammar sharing. `theory_backend_experiment.py`
searched all 24 orders of the reduced four-row system; that system's logical
incompleteness is separately documented by `typed_countermodel.md`.

These findings establish that the located complete searches did not cover
all 8! orders. They do not establish historical novelty outside the inspected
sources or prove any state-count improvement.

## 2. Exact command interface

Write a command-boundary state as `(t,S,d,h)`, where `t` is the current
formula, `S` is the theorem stack (top first), `d` is the additive datum and
`h` is the cache. `0` is truth and `1` is the designated refutation formula.
The stack is a stream eventually padded by zeros. `X::S` means an actual
Cantor-pair push, not an uncharged extra register.

All displayed DROP and NIP commands have encoded input argument x=0; this
argument does not increment the state register d. Their effects are

    DROP: (t,S,d,h) -> (h,t::S,d,h).
    NIP:  (t,X::S,d,h) -> (t,S,d,X), unless h=1, when it halts.

The MP command with datum `x` sets `b=d+x` and behaves as follows:

    if h=Imp(t,b): (t,S,d,h) -> (b,0::S,b,0);
    otherwise:    (t,S,d,h) -> (0,S,b,0).

In particular `MP(1)` on `(T,S,0,0)` always fails, because
`Imp(T,1)=4 P(T,1)` is positive, and yields `(0,S,1,0)`.

An AX command `AX(c;x,y,u)` first obtains `a=d+x`, remembers the old cache
`h`, and obtains `b=h+y`; it forms the same ten outputs from these parameters
as the original enumerator. Assume an implementation emits these outputs
in a fixed order `R_1,...,R_m`, where `m=10`, preserving the old current `T`.
Its boundary result is exactly

    (R_m, R_(m-1)::...::R_1::T::S, 0, 0).                (AX)

The bundle output is zero whenever `c=a` or `c=b`. The GEN output is
`All(a,h)` using the old cache, before adding `y`. No formula family, numeric
encoding, freshness condition, or parameter cleanup is changed.

## 3. The selection lemma

For an emission position `j`, with `1 <= j <= m`, define

    E_m = NIP^m;
    E_j = NIP^(m-j); DROP; NIP^(j+1)       (j<m).

**Lemma.** Starting at (AX), execution of `E_j` either halts upon testing a
cache equal to 1, or ends at

    (R_j,S,0,T).                                        (Select)

No cell of the suffix `S` is inspected or changed. The conclusion is valid
for every natural value of `T`, every output value, and every suffix `S`.

**Proof.** For `j=m`, the `m` pops traverse `R_(m-1),...,R_1,T`, leaving the
last value `T` in the cache and the current `R_m` unchanged. For `j<m`, the
first `m-j` pops leave cache `R_j` and stack
`R_(j-1)::...::R_1::T::S`. DROP changes the current to `R_j` and pushes
the old current `R_m`. The final `j+1` pops traverse
`R_m,R_(j-1),...,R_1,T`. The remaining stack is exactly `S` and the final
cache is `T`. Any interrupted sequence has just encountered a literal
refutation value under the original NIP rule. This is an induction on the
finite displayed prefix; it makes no assumption about the infinite tail.

There are `m` NIPs if the selected output is current and `m+1` NIPs plus one
DROP otherwise. The positions of the other outputs have no effect on the
argument.

For the actual ten outputs, the early-halting alternative is unnecessary:
the eight static rows and the bundle are implication codes (residue zero
modulo four, including the failed-gate truth zero), and GEN is a universal
code (residue two). None is 1. The saved current T is loaded only by the
last NIP, after that NIP has already performed its halt test. Thus actual
selection terminates with exactly (Select), even when the saved T is 1.

## 4. Complete replacement proof compiler

Let `bpos` and `gpos` be the emission positions of the bundle and GEN.
For each static logical row `rho_k`, let `pos(k)` be its emission position.
The invariant for a derivation compiler is

    Build(D): (T,S,0,0) ->* (conclusion(D),S,0,0),        (Build)

or an earlier halt. `T` and `S` are arbitrary. All intermediate NIP tests
that can halt before completion concern valid derived outputs; discarded
arbitrary residual data are shielded by the construction.

### Discard

    D = MP(1); AX(1;0,0,0); E_bpos.

MP gives `(0,S,1,0)`. AX has `a=c=1`, so its bundle is zero and its saved
current is zero. Select gives `(0,S,0,0)`. This replaces the original fixed
ten-pop cleanup if the bundle is moved.

### Axiom leaves

For a desired bundle instance at `(a,b,c)`, use

    D; AX(c;a,b,0); E_bpos.

For a desired row instance `rho_k(a,b,c,u)`, use

    D; AX(c;a,b,u); E_pos(k).

After D, both additive datum and cache are zero, so the selected parameters
are precisely the requested naturals. The saved current is zero, making
the final cache zero by Select. A failed bundle gate returns the original
truth placeholder. The retained row family is the complete original family.

### Generalization

For a derivation of `H`, the compiler for `All(i,H)` is

    Build(H); DROP; NIP; AX(i;i,0,0); E_gpos.

After the first two commands following Build, the state is `(0,S,0,H)`.
AX therefore emits `All(i,H)` at position `gpos`, with saved current zero.
Select yields `(All(i,H),S,0,0)`. In the AX parameter acquisition, `a=i`
and `b=H`; there is no need to subtract H from another desired parameter.

### Modus ponens

For derivations of `A` and `Imp(A,B)`, use

    Build(A); DROP; Build(Imp(A,B)); NIP; DROP; NIP;
    MP(B); AX(B;0,0,0); E_bpos; DROP; NIP; NIP.

The prefix before MP yields `(A,S,0,Imp(A,B))`. Successful MP yields
`(B,0::S,B,0)`. The next AX has `a=c=B`, so its bundle is zero. Select gives
`(0,0::S,0,B)`. DROP and the two NIPs then give `(B,S,0,0)`: the first pop
removes the zero pushed by DROP, the second removes MP's dummy zero.
If `B=1`, a NIP may halt early, which already fulfills the objective.

### Arbitrary retained data and final halt

The prefix `START = AX(0;1,1,0)` resets `d=h=0` without NIP. Whatever
values it leaves in current or stack can be supplied as the arbitrary `T,S`
of Build. For a refutation derivation, append

    DROP; NIP; NIP.

This halts from `(1,S,0,0)`: DROP saves 1, the first NIP loads it into cache,
and the second NIP tests it. This argument uses the same halting convention
as the original enumerator.

## 5. Enumerator soundness and completeness

**Theorem.** An abstract enumerator with the original command decoding,
original formula constructors, and AX satisfying (AX) for any fixed
permutation of all ten original outputs halts from a sound seed iff the
original calculus derives formula code 1. The theorem also applies to
the intended arbitrary counter and finite retained program-list seeds,
provided the same soundness condition as in the original enumerator holds.

**Soundness.** Preserve the invariant that current, cache and every stack
entry are derivable. Zero is derivable. MP and GEN preserve derivability;
each static row is an original axiom; the gated bundle is either an
original bundle axiom or zero. Reordering preserves this multiset of
derivable outputs and preserves the saved derivable current. NIP can halt
only when its cache is derivable code 1.

**Completeness.** Induction on the original calculus derivation, using the
four blocks above, gives a finite command word that derives 1 from every
retained current and stack after START and then halts. The original
Cantor-pair command encoding realizes every finite command word. The
remaining program-list value strictly decreases at every noninitial
command, so every finite candidate drains. The candidate counter increases
and eventually reaches the encoded word unless an earlier halt occurs.
For an arbitrarily advanced initial counter, prefix enough START commands
to make a successful word's numeric code exceed that counter: a command
word of length l has code at least l-1, since each continuation is encoded
with the original positive delimiter. START does not affect the Build
contract. Thus no reset to a special proof-search seed is needed.

This proof is finitary and translates into the same arithmetic formalism
as the original abstract-enumerator proof. It does not, by itself, supply
the separate internal interpretation of the calculus in ZFC or a binary
compiler proof.

## 6. Safe schema symmetries and emitter constraints

Every static row can independently permute its formal parameters
`a,b,c`, since those range over all naturals in a clean AX call. This
preserves the complete instance family, including when a parameter is used
as a formula code in one position and a variable label in another. If a
given row does not use some parameters, it suffices that the map on its
used parameter tuple be surjective; a permutation is a simple certificate.
The inverse permutation tells the leaf compiler which AX parameters to
choose. Different rows may use different permutations because a separate
AX call can extract each desired axiom.

This freedom does **not** authorize changing the bundle's matrix/fresh
variable correlation, its gate, or the old-cache GEN dependency. The
bundle permits swapping a and b with the same symmetric gate, but moving
c into another role requires the corresponding gate transformation and a
separate emitter proof. Permuting u into a repeated position requires
storing/reusing u: the present `read_u` macro consumes a new command-list
entry whenever invoked.

There is a strictly larger safe symmetry family for rho8. Its template is

    ((c -> u) -> a) -> ((a -> c) -> (b -> c)),

so the formal-role occurrence counts are a:2, b:1, c:3, u:1. A permutation
of the four formal parameters can therefore send the new input role u into
either original b or original u: each occurs once. There are
`2 * 3! = 12` such permutations. All preserve the entire axiom-instance
family and execute `read_u` exactly once. The three remaining roles use
the existing reusable a/b/c leaf macros. For example, the map
`old(a,b,c,u) -> new(b,u,a,c)` emits `rho8(b,u,a,c)`. To obtain the
desired original instance `rho8(a0,b0,c0,u0)`, a clean AX call supplies
`new(a,b,c,u)=(c0,a0,u0,b0)` and selects that row. The different outputs
from the same AX call remain valid original instances.

Combining these twelve rho8 variants with independent six-way a/b/c role
permutations on each other row and all eight-row orders yields the nominal
configuration count

    8! * 12 * 6^7 = 135,444,234,240.

This counts syntactic choices, not necessarily distinct emitted programs,
and supplies neither a search-exhaustion claim nor a state-count benefit.
The ordinary compiler theorem applies compositionally to every choice.

The actual zero-cost edit used by the proposed search keeps GEN first,
then executes `read_b`, then permutes the eight complete logical rows, and
keeps the bundle and five existing gate/cleanup macros last. Only rho8
consumes `read_u`, so its position among those eight rows is unrestricted:
the others do not inspect or consume the remaining proof list. The same
fourth parameter is eventually read exactly once before AX ends.

If GEN moves after `read_b` without storing the old cache, it produces
`All(a,h+y)`, which need not be derivable. If the ungated bundle moves into
the saved stack while the existing gates still clear only the final
current, malformed bundle instances survive. These are concrete forbidden
shortcuts; they are not limitations of the abstract permutation theorem.

## 7. Executable evidence

`check_axiom_row_permutation.py` independently interprets DROP and NIP on
formal stack values, with a completely arbitrary marked suffix. It checks
all 40320 actual eight-row permutations, all ten selection positions, both
ordinary and early-halting cases, and the Discard/GEN/MP contracts. Values
are free exact symbolic objects, not fingerprints or truncated huge
integers. This checks the displayed algebraic command interface, not the
source macro implementation, all numeric formula codes, or a literal TM.

The general selection proof covers all 10! output permutations; the
exhaustive actual-emitter lane fixes GEN first and bundle last.

`check_full_row_emission.py` additionally checks all 40320 actual row orders
with the existing recovered primitive emitter and its separate symbolic
formula evaluator. It checks the twelve rho8 role maps, their occurrence
counts, their exact single read_u, and inverse-renaming identity. The
corresponding JSON records make the source-spec SHA-256 explicit.
