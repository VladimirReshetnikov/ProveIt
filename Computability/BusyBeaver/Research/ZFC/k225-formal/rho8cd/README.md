# rho8 by condensed detachment

`rho8 a b c u = ((c → u) → a) → ((a → c) → (b → c))` is Łukasiewicz's single axiom of the
implicational calculus. The dominated calculus of the K215/K217 endpoints grants it only when
`u ≤ a`; `rho8_all` derives every instance from modus ponens and the dominated rows. This
directory holds condensed-detachment derivations of that fact, short enough to be read as
lists of lemmas, and renders them for both lanes:

* [`derivation_core.txt`](derivation_core.txt) (58 steps, no truth constant): the unrestricted
  row, composition `(a → b) → ((b → c) → (a → c))` and prefixing `(a → b) → ((c → a) → (c → b))`
  from modus ponens and the restricted rows alone. `--core` renders it as
  [`Lean/BusyBeaver/ZFC/DominatedImplication.lean`](../../../../Lean/BusyBeaver/ZFC/DominatedImplication.lean):
  any binary connective with a reflexive `below` relation closed under insertion into either
  operand, the interface of the representation-independent core (phase eight). Its three public
  theorems depend on no axioms; `DomRho8.lean` is the unchanged Nat adapter.
* [`derivation.txt`](derivation.txt) (52 steps, uses truth `Z` = the code 0): the row alone.
  `--rocq` renders a Rocq `DomRho8.v` (11,190 bytes; compiled with `ThmDom`, closed under the global
  context; adopted in `4fdc59197a`, while the maintained Rocq tree keeps its checked certificate replay,
  see [the status note](PROVEIT_STATUS.md)); `--lean` renders the same derivation as a drop-in Nat
  `DomRho8.lean` (built with `KCodeDom` in `4fdc59197a`).

* [`derivation_luk.txt`](derivation_luk.txt) (56 steps, unrestricted row, no truth): K, Peirce,
  composition and S. `--luk` rewrites the `Lukasiewicz` namespace of
  [`Lean/BusyBeaver/ZFC/Lukasiewicz.lean`](../../../../Lean/BusyBeaver/ZFC/Lukasiewicz.lean) (it ported the
  107-step CD254 DAG; the Tarski bridge after the namespace is kept verbatim); `--rocq-cd` renders the
  Rocq `CD222.v` with `thm_K`, `thm_P`, `thm_B`, `thm_S`.

[`rocq-proposal/`](rocq-proposal/README.md) holds the two Rocq renderings, compiled with their users,
as proposals for the peer's Rocq checkpoint.

Format: one line per formula, `i major minor F [side conditions]`. Leaf `-1` is truth `Z`, leaf
`-2` the dominated row `(((a>b)>c)>((c>a)>(d>a))) [b<=c]`; every other line follows from its major
and minor premise by modus ponens after the most general unifier; `#GOAL i F` names the line
proving each public statement.

[`generate_domrho8_cd.py`](generate_domrho8_cd.py) recomputes each unifier, so every lemma states
its formula and applies its premises at explicit instances. Each side condition `u ≤ a` is proved
because `u` is a literal subterm of `a` (`le_l`/`le_r`, from reflexivity), is `0` (Nat and Rocq
only), or is a hypothesis of the lemma. Nothing it does is trusted; the kernels check every step.

[`search/`](search) is the untrusted search: a given-clause prover (`cdr`, Rust) with side-condition
tracking and Veroff's hints, and the hint-deletion loop `shrink.py`. Hints from the 111 statements
of the earlier derivation ([`hints_source149.txt`](search/hints_source149.txt), Source 149's
certificate as compressed to 118 lemmas) gave an 86-step proof in six seconds; rerunning with the
proof's own formulas as hints, each time without one of them, shortened it to 52 steps (with
truth) and, with `NOZ=1` and the two extra `GOALS`, to the 58-step core.

```sh
python generate_domrho8_cd.py --derivation derivation_core.txt --core ../../../../Lean/BusyBeaver/ZFC/DominatedImplication.lean
python generate_domrho8_cd.py --derivation derivation_luk.txt --luk ../../../../Lean/BusyBeaver/ZFC/Lukasiewicz.lean
python generate_domrho8_cd.py --rocq DomRho8.v       # the Rocq renderings (not in regenerate215.py)
python generate_domrho8_cd.py --derivation derivation_luk.txt --rocq-cd CD222.v
python generate_domrho8_cd.py --lean DomRho8.lean    # the drop-in Nat rendering

cd search && cargo build --release
./target/release/cdr 40 1 3000000 3 HINTS.txt 1 > proof.txt     # one hinted run
NOZ=1 GOALS="((a>b)>((b>c)>(a>c)));((a>b)>((c>a)>(c>b)))" \
  python shrink.py proof.txt best.txt 30                          # hint deletion, core goals
```
