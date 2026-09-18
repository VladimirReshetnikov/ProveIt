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
`--max-objects N`, `--seconds S`. Options of `khovanov`: `--factor`, `--lifo`,
`--tail N`, `--max-objects N`, `--seconds S`.

## Pipeline

Validation; incremental Reidemeister I/II reduction; linear descending test;
visible connected-sum factorization; Alexander minor at t = −1 and at a generic
point of F_p (p = 2^61 − 1); Kauffman bracket at a generic point of F_p by a
frontier scan; exact F2 Khovanov rank by scanning with delooping and
Gaussian elimination. The exact Alexander polynomial over Z[t] of the Python
pipeline is omitted: it needs big integers, and exactness never depended on
it, since the Khovanov scan decides whatever the filters leave open.

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

* `cargo test --release`: 4 tests, OK.
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
