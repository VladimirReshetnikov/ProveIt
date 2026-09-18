# fastunknot (Rust)

A Rust implementation of the `fastunknot` 0.2 pipeline from `../fast`,
designed for Rust rather than transliterated from Python. No dependencies;
builds offline with a stock toolchain.

**Status: exact and complete, exponential in the worst case. This is not the
quasi-polynomial algorithm of Lackenby's talk**; see `../synthesis/report.pdf`.

## Build, run, test

```sh
cargo build --release
target/release/fastunknot recognize ../fast/examples/conway.json
target/release/fastunknot khovanov  ../fast/examples/stress_braid5_36.json
target/release/fastunknot khovanov  ../fast/examples/conway_sum_8.json --factor
target/release/fastunknot jones     ../fast/examples/kinoshita_terasaka.json
cargo test --release
python cross_check.py 150        # Rust against the Python package on random braid closures
python profile.py                # timing and phase breakdown; writes results/profile.json
```

Input formats are those of the Python package (`pd`, `braid`, `rows`, `x`/`o`).
Output is one JSON object; `seconds` is measured inside the process after the
input has been parsed and validated (`--repeat K` reports the median of K runs
and the minimum as `seconds_min`). Exit codes: 0 for an exact verdict, 2 for
invalid input, 3 for `UNKNOWN`.

Options of `recognize`: `--no-reduction`, `--no-descending`, `--no-factor`,
`--no-modular`, `--no-jones`, `--jones-max-states N`, `--lifo`, `--tail N`,
`--max-objects N`, `--seconds S`, `--no-r3`, `--race N`, `--race-after MS`.
Options of `khovanov`: `--factor`, `--lifo`, `--tail N`, `--max-objects N`,
`--seconds S`, `--race N`, `--race-after MS`.

## Pipeline

Validation; incremental Reidemeister I/II reduction; linear descending test;
visible connected-sum factorization; Alexander minor at t = −1 and at a generic
point of F_p (p = 2^61 − 1); Kauffman bracket at a generic point of F_p by a
frontier scan; exact F2 Khovanov rank by scanning with delooping and
Gaussian elimination. The exact Alexander polynomial over Z[t] of the Python
pipeline is omitted: it needs big integers, and exactness never depended on
it, since the Khovanov scan decides whatever the filters leave open.

## Reidemeister III help (ported from the Python package, September 2026)

When every filter has failed and the exponential scan is next, `recognize` looks
for sequences of up to four Reidemeister III moves (inversions of a triangular
face, the later moves next to the first) after which a Reidemeister I or II
move exists, keeps such a sequence and reduces further; sequences that lead
nowhere are undone. The search deepens only while fewer than 10 trial moves per
crossing have been made. `prep::simplify_r3` is a port of `simplify` in
`../fast/fastunknot/simplify.py`, where the move and the search were verified
(see `../fast/README.md`); here the tests check that it never leaves more
crossings than I/II alone, leaves no I/II move, preserves the reduced Khovanov
rank and the Alexander test on 150 random closures, and agrees with Python on
the named examples (the 8-crossing "hard unknot" falls to one III move, one
unknot needs two in a row, one survives depth 4 with 9 crossings). `--no-r3`
turns it off.

## Racing scan orders on threads (`--race N`)

The scan is sequential, but its cost depends wildly on the order of the
crossings, and the greedy rule's ways of breaking ties are incomparable: on 81
diagrams each rule is better on about as many inputs as it is worse, with work
ratios from 0.01 to 28 (`../fast/README.md`). No cheap predictor was found, and
restarting or trying candidates costs more than it saves. Racing does not need
a predictor: `--race N` scans up to three orders (ties broken by crossing
index, by longest wait, by most recent touch) on separate threads; the first to
finish sets a flag that the others see at their next check and stop. Rank and
ranks by degree do not depend on the order, so the result is the same whoever
wins; a competitor that hits `--max-objects` does not end the race. The race
lives here and not in the Python package because a Python competitor must be a
process, which costs 76 to 111 ms to start, against scans of mostly under
300 ms.

Measured (`python race_eval.py`, results in `results/race_eval.json`): 40 random
closures of 34 to 55 crossings on 4 to 7 strands whose single scan takes 30 ms
to 8 s, five rounds with the three settings interleaved, medians.

| | total time | per-input ratio: median, min, max | faster / slower |
|---|---|---|---|
| `--race 2` | 0.650 of single | 1.06, 0.05, 1.43 | 19 / 21 |
| `--race 3` | 0.689 of single | 0.98, 0.05, 1.68 | 20 / 18 |

So it is insurance against the heavy tail, not a uniform gain: 6.8 s becomes
0.34 s, 6.3 s becomes 1.4 s, 890 ms becomes 140 ms, but when the default order
was the best one anyway the race costs 10 to 60%. That premium is not the
allocator: two or three *separate processes* running the same single scan at
once slow each other down exactly as much as the racing threads do (1.15
against 1.18, 1.27 against 1.28, 2.11 against 2.06, 1.71 against 1.70), so it
is contention in the hardware of this machine (12 logical cores, 1.7 GHz
nominal), and will differ elsewhere. The default is therefore `--race 1`; use
`--race 2` when scans are long or a bad order would hurt.

**A head start for the default order (`--race-after MS`, default 0).** The idea:
let the competitors start only after the default order has run for a while, so
that scans finishing within the head start pay nothing. It works as designed
but is not a better default. On the 17 inputs whose single scan is under 100 ms
(nine interleaved rounds): no head start 1.10 of single (median 1.15), 50 ms
1.10 (median 1.07, since most of these scans last 50 to 100 ms), 200 ms 1.01
(median 1.006). On all 40 inputs (five rounds) the totals were 0.514 without,
0.572 with 50 ms and 0.604 with 200 ms, because a head start gives away wins on
scans of 100 ms to 1 s (0.78 of single without, 0.87 and 0.98 with) to protect
scans where at most 15 ms are at stake. Those totals carry a run-to-run noise
of about 0.1: the same setting on the same inputs gave 0.650 in the first
experiment and 0.514 in the second, a few multi-second inputs dominating.
(`results/race_head_start.json` predates the fix described next;
`results/race_head_start_short.json` is after it.) A first implementation let
the late starters poll with `sleep(1 ms)`, which on Windows lasts up to a timer
tick of about 15 ms and held up the return of the scope: scans that never
started a competitor cost 1.04 (worst 1.13) instead of 1.00. They now wait on a
channel that the first order closes when it is done.

Cancellation needed the clock and the flag to be looked at while a crossing is
being added, not only between cancellations, so the transfer loop now checks
every 1024 objects. With a budget of 1 s on closures of 71 to 83 crossings the
overshoot is at most 0.08 s, process start included, with and without a race.
The overshoots of 40 to 70 s recorded below were on 300 s budgets with far
larger complexes; those runs were not repeated, so whether this check removes
them is not known.

## What is Rust-specific

* **Interned matchings.** A boundary matching is a sorted `Vec<(u32,u32)>`
  stored once; objects, plans and caches refer to it by a `u32` id.
* **Morphisms as bitsets.** An element of Hom(a, b) is a set of monomials
  (dot masks over the circles of a ∪ b̄). With at most six circles, which
  covers every scan boundary up to twelve edges, it is one inline `u64`;
  larger Hom spaces use boxed words. Addition is XOR, the unit test is bit 0.
* **Compiled plans.** The dot-independent topology of a composition or of a
  crossing transfer (components, Euler characteristics, boundary circles) is
  computed once per matching triple or pair and reduced to a few integer masks;
  evaluating a monomial is popcounts and ORs.
* **Memoization with a fast hasher.** Composition results and crossing
  transfers are cached per stage in hash maps using an Fx-style multiplicative
  hasher (measured: the standard SipHash is 18 to 32% slower on the scanner).
* **Flat object storage and a binary heap** for the lazy min-fill (Markowitz)
  pivot queue; units over F2 are involutions, so a pivot needs no inversion.
* **Arithmetic modulo 2^61 − 1** with `u128` products for both filters.
* A small base-10^9 big integer for factored ranks such as 33^16.

## Verification

`cargo test --release` runs known ranks in every configuration (min-fill and
LIFO pivots, tails 0 to 2, mirrors), input validation, one-sidedness of the
filters on unknot diagrams, and the recognition pipeline. `cross_check.py`
compares ranks by cube degree and verdicts with the Python package on random
braid closures. Measured results are in `results/` and in the synthesis report.

## Test and profile status (last observed 18 September 2026, rustc 1.96.1, Windows 11)

* `cargo test --release`: 6 tests, OK (18 September 2026, after the III search and the race were added;
  the profile numbers below predate both and were not re-measured).
* `python cross_check.py 200`: 200 random braid closures, 0 problems (about a minute).
* `python profile.py`: completed in about 13 minutes. Almost all of that is two
  scaling inputs (a 160-crossing 3-strand closure and an 81-crossing 4-strand
  closure) that exhaust their 300 s budgets, and overshoot them by 40 to 70 s
  because the deadline is only checked between cancellations. Everything else
  finishes in seconds. Remove those two rows from `profile.py` for a quick run.
* Headline numbers (`results/profile.json`): the 36-crossing stress closure scans
  in 68 ms (Python 0.2: 0.69 s; Python 0.1: more than 600 s); recognition of the
  Conway knot takes 55 microseconds; the scanner is 10 to 17 times faster than
  Python 0.2 on identical inputs.
