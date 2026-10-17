# Eliminating GEN by prefix-closed axioms: sound, but larger here

2026-10-16. An ordinary admissibility argument removes the generalization
rule while retaining the original numerical calculus's refutations. A concrete
complete-control emitter for this presentation costs **286 states**, or
**285 states** after conjunction grouping, in a bounded32-layout comparison.
The unchanged original control costs281. This is a negative compiler result,
not a new smaller consistency machine or a Lean theorem.

The source program, arithmetic and Wade compiler are attributed to Mira-Cult,
Jeff and Wade, pinned at `297ab8df7e5de329605c3875b4934643b371a5e3`.
The driver [gen_free_experiment.py](gen_free_experiment.py) reads the immutable
219-node DAG, uses the existing checked symbolic AX comparison, and copies the
pinned compiler into external scratch. It preserves native equality, all eight
logical schemas, the gated CP/GIC/vacuity bundle and the existing scheduler.
It does not reuse the incomplete equality-free row deletion experiments.
Complete replay data are in
[results/gen-free-experiment.json](results/gen-free-experiment.json).

## The precise admissibility argument

Let `A` be the original primitive axiom family, including truth0 and every
permitted gated bundle. Let `A*` contain `All(i1,...All(ik,a)...)` for each
`a∈A` and each finite prefix, including the empty prefix. Define `P*` by
axioms `A*` and modus ponens alone.

Generalization is admissible in `P*`. Induct on a finite `P*` proof of `b`:

* An axiom can receive one more leading universal because `A*` is prefix
  closed.
* For MP from `p` and `p→b`, the induction hypotheses give `All(i,p)` and
  `All(i,p→b)`. The original QI/rho2 instance
  `All(i,p→b) → (All(i,p)→All(i,b))` and two MPs give `All(i,b)`.

Conversely, every `A*` axiom has an original proof by finitely many GEN steps.
Induction therefore gives exactly the same numerical theorem set, in
particular the same refutations. Truth0 must be included in this argument;
closing only the nonlogical axioms is insufficient. This is an explicit
effective proof transformation by finite proof induction, but no arithmetic
representation or PA-internal theorem is supplied here. Consistency comparison
with ZFC can compose with the original calculus's calibration; it is not
inferred from the emitted table or its finite tests.

## A small concrete prefix generator

The new macro reads a Cantor-coded entry into `X` with original `read108`.
Entry0 terminates the prefix; entry `a+1` decrements to `a`, applies original
`pair162; times4_117; add2_159`, and repeats. It maps the current formula `t`
to `All(a,t)` while preserving the formula stack and `N,A,D,H`; both scratch
registers finish0. A finite prefix is followed by a zero terminator, after
which the remaining command word is preserved. All nine registers remain.

The first presentation replaces the old GEN output by truth0 and inserts this
same macro after each of the ten completed AX rows. All subsequent logical
rows and the bundle are unchanged. The bundle gate stays after its prefix:
on a gate collision it returns0, whose universal prefixes are already supplied
by the truth row. Thus the union of emitted primitive families is still
prefix closed. Exact row boundaries and every rebracketed macro expansion are
checked against the published symbolic spec. Prefix entries are ordinary
independent input fields; their byte/variable payload is not omitted.

The grouped presentation keeps rho8 and rho6 as separate prefix-closed rows,
then forms one conjunction of rho7, rho5, rho4, rho3, rho2, rho1 and the gated
bundle. The literal gates run **before** this final conjunction. All three
rows receive arbitrary prefixes.

This grouping has no circular projection argument. Rho8 supplies K/S/Peirce
by MP alone; rho6 supplies ex falso using K/S and MP, without GEN. The exact
derivations already occur in `Lukasiewicz.lean:497` and
`Code254.lean:383`. They allow projection from the relative-falsity conjunction,
so QI and every original axiom are available before invoking the admissibility
lemma. Numeric `rho8(0,0,0,0)=0`, so all truth0 prefixes are also directly
available from the first family. Every new primitive row is conversely an
original theorem by conjunction introduction and GEN.

The extra prefix input does not require an oracle or a new register. Each
finite augmented command word has an ordinary Cantor encoding. The unchanged
candidate counter still enumerates all such numbers. An ordinary proof-search
coverage argument must also update the existing fixed row-selection and
cleanup blocks to the new row counts; no unchanged `Enum254` compiler theorem
is asserted. In the grouped case the master conjunction is positive and
different from1. A cleanup can pop all newly emitted rows to cache the known
old0, then use `DROP; NIP; MP0` to discard the positive master and restore
top/cache0. This gives an explicit route rather than assuming the old
ten-row normalization still applies.

## Measurements and boundary

| Complete control | Unshared | Best32 | Best decision + framework |
|---|---:|---:|---:|
| original | 281 | not rerun | 219 +62 |
| delete GEN output only, incomplete | 280 | not searched | 218 +62 |
| prefix each primitive row | 308 | 286 | 224 +62 |
| three grouped prefix families | 307 | 285 | 223 +62 |

Only seeds0–31, Re-Pair exponent2 were tested. Every actual table is charged
for the full original arithmetic runtime, all retained axiom templates,
prefix generator, gates, MP/DROP/NIP, scheduler and generic Wade bootstrap.
Every decision edge is re-extracted. The standard missing framework row is
totalized to halt; its unreachability in a changed blank-start run is not proved.
The new startup invariant is unverified. There is no compiler/runtime proof,
new state bound for Con(ZFC), or exhaustive-layout claim.

Forty exact structured-register tests check empty, one-label and two-label
prefixes, including preservation of a nonzero remaining command word. A wider
initial unary grid exhausted10,000,000 structured steps and was not counted.
The ordinary admissibility proof is stronger than these finite checks, while
the concrete macro and compiler correctness remain separate formal work.

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/gen_free_experiment.py \
  --scratch /tmp/zfc-gen-free-replay --output /tmp/zfc-gen-free-replay/results.json
```
