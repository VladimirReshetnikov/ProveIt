# Source grammar investigation

This directory contains source-level compiler research. A count of 201, 202,
or 203 here counts distinct binary decoder subtrees, **not Turing-machine
working states**. No JSON in this directory by itself establishes a machine
with fewer than 246 states.

## Sources and environment

The reference is the exact `original203.json` literal from the supplied
`beyond252` archive. The archive's `vendor/dag_tools.py` and
`vendor/rotate_search.py` are used for source parsing, sharing, and depth
metrics. The default archive path is relative to the present research
directory. Set `BEYOND252_EXPLORATORY` to its `exploratory` directory when
moving these files elsewhere.

The search scripts require Python, NumPy, and SciPy with `scipy.optimize.milp`.
`analyze_candidate.py` is an independent standard-library checker and takes
explicit `--source` and `--entries` paths. The stronger independent
instruction-CFG checker is in the companion `agent_logic` investigation.

## Concrete ordered-source improvements

The source has 62 fixed control atoms and 141 closed sequence phrases. After
flattening only nodes whose two children are closed, its maximal sequence
words have lengths 1270, 12, 8, 6, 6, 5, 4, 3, 2, and 2. All ordinary grammar
searches preserve those exact ordered words and every fixed control atom.

### Minimal 202-node layout

Original node 74 is `(N39,N73)`, node 73 is `(N47,N63)`, and an existing
node 48 is `(N39,N47)`. Replacing node 74 by `(N48,N63)` makes node 73
unreachable. All of N39, N47, and N63 are closed. This is the elementary
association `A;(B;C) = (A;B);C`.

The resulting 202-node source has initial zero prefix 3, maximum zero run 7,
and maximum path length 34. Its normalized modal entry price is 190, compared
with 191 for the original source: old machine state 208 becomes unused in the
literal source interpretation.

This single move already appears among the archival `rotate_search.options`.
It should not be described as a newly invented source identity. The archived
negative search concerned reducing the maximum zero run below seven. Runtime
integration revealed the relevant obstruction: old contextual decoder state
218 uses the altered state 178 as a helper. A direct 245-state table is
incorrect; separating its two contexts yields a verified alternative table
with 246 states. See the runtime investigation for its exact certificate.

The minimal source is
`dictionary_max0_freq2_zero7_depth39_old1.json`.

### A 201-node global grammar

The finite dictionary MILP found a 201-node source with maximum zero run 7.
Its sparse original-ID description is `sparse201.json`:

* Add node 203 = `(N48,N79)`.
* Replace node 59 by `(N99,I1)`.
* Replace node 74 by `(N48,N63)`.
* Replace node 83 by `(N63,N203)`.
* Replace node 99 by `(N43,N203)`.
* Remove now-unreachable nodes 49, 73, and 82.

The ordered complete source program is unchanged modulo closed association.
The independent checker compares all 8,391 source leaf/guard cases and obtains
the same instruction CFG after mapping leaves by DFS occurrence. The MILP
result is `dictionary_max20_freq2_zero7_depth39_old1.json`; the concise
independent analysis is its `_analysis.json` companion.

Its 201 distinct source nodes map to 190 modal entries: source nodes 49 and
73 orphan old states 98 and 208, while source node 82 shares state 243 with a
retained node. One new phrase needs a new entry. Runtime contextual sharing
again costs more than this static price: old states 218, 243, and 244 depend
on context-sensitive decoding involving the changed phrases. The source
improvement is therefore not a certified 245-state machine.

### A 203-node layout with zero run six

Adding the five distinct useful phrases from the archived short-zero layouts
to the global phrase dictionary gives a 203-node source with initial zero
prefix 3, maximum zero run 6, and maximum path length 35. The candidate is
`dictionary_max20_freq2_zero6_depth39_old1_seed.json`. Its modal entry price is
193, so reducing the scanner length does not automatically save a state.

## Integer-program formulation

For each candidate sequence word `w`, the model has a binary selection `x_w`.
For every available split `w=a b`, it has a binary `y_(w,a,b)`, with
`sum(y)=x_w` and `y <= x_a,x_b` for non-atomic children. The ten maximal words
are required. These equations form a finite acyclic grammar because every
child is shorter than its parent.

The candidate dictionary consists of original phrases and repeated contiguous
subwords up to a chosen length. Optional archival seeds contribute additional
valid phrases. Optional integer height variables bound the maximum left-only
path (zero run) and total path length. All rounded returned integer values are
checked against every exact model constraint before emitting a source.

The `--tm-price` objective charges each retained original modal state once,
even if multiple original phrases share it, and charges one for each new
phrase. It is still a static estimate: it does not certify retention of a
contextual rewind fold. `--freeze 74,83` requires those exact original splits
and prevents their words from disappearing. In the tested length-20 ordinary
dictionary, freezing both returns the original modal price 191.

## A broader grammar: commuting closed register routines

`trace_grammar.py` and `trace_milp.py` implement a different source language.
Two closed atoms may commute if neither contains a halt instruction and the
unions of their read/written register sets are disjoint. Their partial normal
completion functions commute: each depends only on its own registers, each
preserves the other's registers, and either both orders complete with the same
result or both fail to complete. Excluding halt instructions is necessary:
swapping a halting atom with a divergent one can change machine halting.

A phrase now denotes a dependence partial order. Its normal form is the
lexicographically first topological ordering, and legal binary factors are
order ideals of that partial order. The optimizer enumerates factors through
a dictionary prefix trie, rather than limiting itself to contiguous pieces
of one concrete ordering. `--orders N` enriches the dictionary using factors
from N reproducible alternative topological orderings.

There are two immediately swappable original nodes, 31 and 173, each yielding
another 203-node source. Their original-ID files are `swap_sparse_31.json` and
`swap_sparse_173.json`. Flattening reveals many additional adjacent swaps.

The optional `--affine` extension uses `affine_atoms.py`. It recognizes a
restricted, syntactically checkable family of terminating transfer loops:
the left child is a decrement of register r; the body contains only
increments of other registers and a final continue returning to that test.
The loop acts as `r:=0; j:=j+c_j*old(r)`. Closed compositions have exact 10-by-10
homogeneous integer matrices. Two recognized total affine atoms may commute
when their matrix products commute, even if their register footprints
overlap. Recognizer witnesses distinguish this from fitting a matrix to
sampled executions.

The trace searches are research artifacts. Their equivalence must be checked
with the companion dependence-poset verifier, not with the ordinary ordered
leaf-CFG equality test. A compiler and blank-start certificate remain separate
requirements for every eventual transition table.

## Reproduction examples

```sh
python dictionary_milp.py --maxlen 20 --maxzeros 7 --maxdepth 39 --prefer-old
python analyze_candidate.py dictionary_max20_freq2_zero7_depth39_old1.json
python dictionary_milp.py --maxlen 20 --maxzeros 7 --maxdepth 39 --prefer-old --tm-price --freeze 74,83
python trace_milp.py --maxlen 20 --maxzeros 7 --freeze 74,83
python trace_milp.py --maxlen 20 --maxzeros 7 --freeze 74,83 --affine --orders 8
```

MILP optimality messages refer only to the finite selected dictionary and
model. They are not global lower bounds on source grammars or Turing-machine
state counts.

## Final campaign status

All active searches have completed. `campaign_summary.json` records 21 finite
models, their exact input filenames and hashes, solver status, integer
incumbents, source-equivalence checks, and independently recomputed static
modal prices. `summarize_campaign.py` regenerates that record.

| Model | Dictionary phrases | Source nodes | Maximum zero run | Modal entries | Solver outcome |
| --- | ---: | ---: | ---: | ---: | --- |
| Ordered, length 20, source price | 3526 | 201 | 7 | 190 | Finite-model optimum reported |
| Ordered, length 20, modal price, freeze 74/83 | 3526 | 203 | 7 | 191 | Finite-model optimum reported |
| Ordered, length 40, modal price | 6009 | 202 | 7 | 190 | Time limit; valid incumbent only |
| Ordered, archival zero-six seeds, source price | 3531 | 203 | 6 | 193 | Time limit; valid incumbent only |
| Ordered, archival zero-six seeds, modal price | 3531 | 204 | 6 | 193 | Finite-model optimum reported |
| Disjoint traces, length 20, freeze 74/83 | 3561 | 203 | 7 | 191 | Finite-model optimum reported |
| Disjoint traces, 16-order enrichment, freeze 74/83 | 13721 | 203 | 7 | 191 | Time limit; valid incumbent only |
| Affine traces, length 20, source price | 3528 | 201 | 7 | 190 | Finite-model optimum reported |
| Affine traces, length 20, freeze 74/83 | 3528 | 203 | 7 | 191 | Finite-model optimum reported |
| Affine traces, archival zero-six seeds, modal price | 3534 | 204 | 6 | 193 | Finite-model optimum reported |
| Affine traces, 8-order enrichment, freeze 74/83 | 13966 | — | — | — | Time limit; no incumbent |

The final affine 201-node incumbent is exactly the ordinary sparse 201-node
layout above. The new commutation language therefore did not yield an
additional priced improvement in these campaigns. No historical priority
claim is made for the commutation rule or trace-grammar optimization. A time
limit, especially without an incumbent, is not evidence that a better layout
does not exist.
