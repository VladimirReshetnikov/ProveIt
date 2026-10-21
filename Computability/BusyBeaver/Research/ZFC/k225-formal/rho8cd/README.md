# rho8 by condensed detachment

`rho8 a b c u = ((c → u) → a) → ((a → c) → (b → c))` is Łukasiewicz's single axiom of the
implicational calculus. The dominated calculus of the K215/K217 endpoints grants it only when
`u ≤ a`; `DomRho8.rho8_all` derives every instance from truth (the code 0, with `0 → 0 = 0`),
modus ponens and the dominated rows. This directory holds one condensed-detachment derivation
of that fact, short enough to be read as a list of lemmas, and renders it for both lanes:

* [`derivation.txt`](derivation.txt): the derivation, one line per formula,
  `i major minor F [side conditions]`. Leaf `-1` is truth `Z`, leaf `-2` the dominated row
  `(((a>b)>c)>((c>a)>(d>a))) [b<=c]`; every other line follows from its major and minor premise
  by modus ponens after the most general unifier. The last line is the row with no side condition.
* [`generate_domrho8_cd.py`](generate_domrho8_cd.py): renders `Lean/BusyBeaver/ZFC/DomRho8.lean`
  (`--lean`) and the Rocq lane's `DomRho8.v` (`--rocq`, called by
  `rocq/rocq-extension/regenerate215.py`). It recomputes each unifier, so every lemma states its
  formula and applies its premises at explicit instances; each side condition `u ≤ a` is proved
  because `u` is a literal subterm of `a` (`le_l`/`le_r`), is `0`, or is a hypothesis of the lemma.
* [`search/`](search): the untrusted search that found the derivation: a given-clause prover
  (`cdr`, Rust) and Veroff's hint-deletion loop (`shrink.py`). Hints from the statements of the
  previous derivation (Source 149's certificate, 118 lemmas) gave an 86-step proof in six seconds;
  rerunning with the proof's own formulas as hints, each time without one of them, shortened it.

Regenerate and check:

```sh
python generate_domrho8_cd.py --lean ../../../Lean/BusyBeaver/ZFC/DomRho8.lean
python ../rocq/rocq-extension/regenerate215.py   # writes coq/215/DomRho8.v among the rest
```

Search again (needs a Rust toolchain):

```sh
cd search && cargo build --release
./target/release/cdr 40 1 3000000 3 HINTS.txt 1 > proof.txt   # one hinted run
python shrink.py proof.txt best.txt 30                         # hint deletion
```
