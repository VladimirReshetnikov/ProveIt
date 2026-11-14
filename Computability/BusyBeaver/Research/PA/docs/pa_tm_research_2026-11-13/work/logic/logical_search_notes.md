# Logical encoding searches and bootstrap audit

## Scope and result

The source is `jamesyc/BusyBeaver@407cdc356f6b586635e71ac92be394255f4bfea4`.
The current AX body has 201 macro tokens and 68 internal binary grammar nodes.
The published physical layout shares six of these nodes, using 62 body states.
No smaller verified TM was found by the logical-word searches reported here.

The portable script `logical_variant_search.py` takes the source repository as
its first argument. It reconstructs the exact current AX word from the
mathematical heads and gate, checks that it equals the source's word, and
reproduces the finite searches. All its costs are grammar-rule counts; they
are not machine-state counts or proofs of a global lower bound.

## Completed search families

| Family | Number checked | Best observed grammar-rule count | Meaning |
|---|---:|---:|---|
| Independent label-role permutations in the six heads, fixed original primitive tree | 46,656 | 159 whole-program internal nodes | Original assignment uniquely minimizes this finite family |
| Six-head order, three antecedent swaps, gate Δ/V order, global equality orientation; fixed 201-leaf association | 23,040 | 68 AX-body nodes | Original word uniquely minimizes this finite family |
| Same word family, deterministic RePair grammar, original membership orientation | 23,040 | 71 AX-body nodes | Heuristic upper bounds; not a minimum-grammar proof |
| Same word family, reversed membership orientation | 23,040 | 72 AX-body nodes | Heuristic upper bounds |
| Fuse h5 into the gate, permute retained heads/gate factors, vary both atomic orientations and antecedent swaps | 23,040 | 73 AX-body nodes | 202-token words; heuristic upper bounds |
| Fuse h1 with a separate explosion head | 138,240 | 75 AX-body nodes | 206-token words; heuristic upper bounds |
| Fuse h1 and h5 with a separate explosion head | 92,160 | 75 AX-body nodes | 207-token words; heuristic upper bounds |
| Negated-atom or contraposed vacuity variants, selected head orders, both atomic orientations, antecedent swaps | 4,032 | 72 AX-body nodes | Heuristic upper bounds |

An independent transport of the original grammar, performed by the machine
optimization subtask, found additional word variants attaining 68 nodes, but
no verified saving in the number of physical states. The original 68-node
grammar is already better than all the RePair scores in the table.

## A bootstrap obstruction, with a countermodel

The designated contradiction is formula code 1. A classical implicational
basis with an arbitrary designated formula does not automatically prove
`1 -> H`. In PA196 that explosion principle is obtained from head h1:

    (exists x_D forall x_D H) -> H,

where the existential is defined by `not forall not`, and `not A` means
`A -> 1`. Consequently two tempting simplifications are circular:

1. Replace h1 by its familiar classical dual `H -> forall x_D exists x_D H`,
   then invoke double-negation elimination to recover the old h1.
2. Place h1 inside a negative encoding of a conjunction, remove its separate
   head, then use conjunction projection to recover it.

There is an explicit Boolean countervaluation showing that neither recovery
follows from the remaining numeric calculus. Interpret numeric code 0 as
true, implication as Boolean implication, every universally quantified
formula as true, and both atomic codes `M(a,b)` and `E(a,b)` as the truth value
of equality of the *numerical labels* `a=b`. Thus code 1 is true, while
`M(0,1)`, whose code is 9, is false. The exceptional code `I(0,0)=0` respects
this valuation, since true implies true.

All instances of h2, h5 and h6 are true because their quantifier expressions
are true. The h3 and h4 instances follow from equality of labels. The
restricted propositional head is a Boolean tautology. Every negative gate
`N(X)=X -> 1` is true. Modus ponens preserves truth and generalization does
also, since its conclusion is always true. The proposed dual h1 is always
true. But old `h1(0,9)` is false: its antecedent is true and its consequent is
false. Therefore old h1 is not derivable in either proposed weakened system.

`bootstrap_countermodel.py` implements this valuation and supplementary
finite checks. The preceding all-instance argument is the proof; the finite
checks are not being substituted for it.

## Safe gate fusions that were actually searched

Let the original gate be `N(Delta -> (V -> Q))`.

* **h5 fusion:** replace it by `N(h5(D,H) -> (Delta -> (V -> Q)))`, and remove
  the separate h5 push. Head h1 remains available, so explosion and
  conjunction projections remain derivable. Head h5 is independent of A;
  any foreign A gives its required instance. This adds one constructor token,
  producing a 202-token word and eight pushed items instead of nine.
* **h1 fusion with bootstrap:** replace the separate h1 by `1 -> H`, and put
  old h1 inside the gate. The explicit explosion head and the retained
  propositional basis justify the projections needed to recover h1. This
  gives 206 tokens and retains nine pushed items.
* **Both:** use an explicit explosion head and put both h1 and h5 inside the
  gate. This gives 207 tokens and eight pushed items.

The guarded calls do not restrict h1/h5 instances: these heads depend only
on D and H, and one may choose A different from both. The old gate is a
propositional consequence of each strengthened gate. A compiler for these
variants would update the fixed stack-selection ranks and push counts.
None of the measured layouts improved the current machine.

## The push macro clears its accumulator

The exact macro contract in `M6/Source/AXMacro.lean` is

    push(t, stack) = (0, t :: stack).

The macro called `P` in the token word, `node49`, therefore cannot replace a
second computation of the current expression while preserving that
expression in the accumulator. In particular, replacing the consecutive
computations `E,E` in equality vacuity by `E,P` is unsound. The emitter uses
`P,i` to construct the constant one precisely because P clears its input.
A genuine duplicate-preserving operation would need a new implementation
and a separately verified contract.

## Reproduction

Run, from the artifact directory:

```sh
python3 logical_variant_search.py /path/to/BusyBeaver --out results
python3 logical_variant_search.py /path/to/BusyBeaver --out results --greedy --fusions
python3 bootstrap_countermodel.py
```

The first command reproduces the exact 23,040-member fixed-association
census and emits the three safe fusion words. The second additionally
reproduces the deterministic RePair and gate-fusion censuses. It may take
several minutes. A smaller search score would still require compilation,
universal physical contracts, and a correct logical compiler before it
could be called a smaller Con(PA) machine.
