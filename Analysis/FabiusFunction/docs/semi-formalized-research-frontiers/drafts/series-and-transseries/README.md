# Series and transseries

Draft packages whose subject is the formal-series calculus itself — the
algebra, division, composition, and reversion of asymptotic expansions —
rather than any one special function.

- [`polynomial-logarithmic-transseries/`](polynomial-logarithmic-transseries/)
  holds the operational treatment of one specific scale: the six
  independently written articles on polynomial-logarithmic transseries, now
  consolidated into a single canonical volume.
- [`lambert-inverse-transseries/`](lambert-inverse-transseries/) holds three
  articles received on 2026-09-02 that invert `x + W(x)` at infinity and build
  a logarithmic-transseries calculus around that example (quick intake only;
  not yet compared or reviewed):
  - `lambert_inverse_transseries/` — *Asymptotic Reversion of x + W(x) and a Calculus for Logarithmic Transseries*
  - `lambert_inverse_transseries_bundle/` — *Reversing x + W(x): Exact Reduction and Logarithmic Transseries*
  - `reversing_x_plus_lambert_w_transseries/` — *Reversing x+W(x): Exact Reduction, All-Orders Asymptotics, and Logarithmic Transseries*
- [`transseries-tutorials/`](transseries-tutorials/) holds four expository
  introductions to transseries in general, filed on 2026-09-02.
- [`special-function-inversion/`](special-function-inversion/) holds twelve
  articles received on 2026-09-03 that invert a rapidly growing special
  function at infinity to all orders (quick intake only; not yet compared or
  reviewed).  They fall into four subjects, three independently written
  articles each:
  - the Gamma and Barnes `G`-functions;
  - the hyperfactorial `K`-function;
  - the subfactorial (these three normalize a power-logarithmic phase with the
    Lambert `W`-function); and
  - a real-argument continuation of the Fibonacci function, whose inverse
    transseries is log-periodic in the golden-ratio phase.
- [`sequence-transseries/`](sequence-transseries/)
  holds five articles received on 2026-09-03, in the evening batch, on the
  complete asymptotic transseries of two classical integer sequences (quick
  intake only; not yet compared or reviewed): two on the Bell numbers, whose
  expansion is a saddle-point series at `r = W_0(n)` with a finite rule for
  every coefficient, and three on the Fubini (ordered Bell) numbers, whose
  exponential generating function `1/(2 - e^z)` has a vertical lattice of
  simple poles, so that the pole-sector transseries is exact and convergent
  rather than asymptotic.

The first four subgroups overlap in subject but not in purpose: the first develops
one scale in operational depth, the second inverts one specific map and builds
its calculus, the third introduces the field, and the fourth applies the
Lambert-core technique across several different special functions, with three
independent treatments of each.  The first
and second are close enough that a later consolidation may merge them; that
comparison has not been made.  The second and fourth share the Lambert-core
step but differ in scope — one map treated deeply against one technique applied
broadly — and each of the fourth's nine articles additionally extracts a
general reversion calculus, so whether those calculi coincide with each other
or with the second subgroup's is an open comparison, deliberately not made at
intake.  The fifth subgroup applies the method to number sequences rather than
to functions; its Bell-number articles meet the Lambert `W` saddle `r = W_0(n)`
that [`../lambert-w/`](../lambert-w/) treats and the Touchard and Stirling
apparatus of [`../combinatorial-coefficient-calculus/`](../combinatorial-coefficient-calculus/),
and those crosswalks are likewise open.

The group was created on 2026-09-02 by splitting the polynomial-logarithmic
packages out of [`../lambert-w/`](../lambert-w/), where they had been filed on
2026-09-01 because Lambert W is their guiding example.  That move was verbatim:
no source, checksum ledger, or PDF changed, and no PDF was rebuilt for it.  The
tutorials and the Lambert-inverse articles arrived directly later the same day.

See [`../MANIFEST.md`](../MANIFEST.md) for the group record.
