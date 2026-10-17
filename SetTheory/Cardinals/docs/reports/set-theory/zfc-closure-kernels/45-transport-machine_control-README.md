# Global register invariants and a 265-state exact-tree control

## Result and status

This package supplies a finite inductive analysis of the **actual 6,459-node,
6,460-leaf `Prog254.v` tree**, two independently checkable zero-register
specializations, and a complete **265-working-state binary control machine**
compiled from its exact 203-node shared DAG with Andrew James Wade's unchanged
public backend. All initialization and interpreter states are counted.

The 203-node DAG is **previously known**, explicitly documented in ProveIt's
source-09 decoder report. The 265-state table is a newly reproduced explicit
control using that known representation, not a new smallest machine, and
not a newly verified consistency machine. Its 203 decoder states preserve
every original leaf path and operation exactly. An independent checker
verifies that finite fact and inverts all 406 emitted decoder transitions.
The separate theorem that this Wade binary interpreter, including its blank
bootstrap, implements those register semantics is not supplied here.

The new experiment addresses a different question from uniform per-instruction
contracts: can the values known at *particular instruction positions* justify
global specialization? The answer is yes for two empty transfer loops, but
deleting them makes the compressed code **larger**:

| Compilation | Unfolded leaves | Shared decoder nodes | Framework states | Working states | Total binary rows |
|---|---:|---:|---:|---:|---:|
| Exact original tree | 6,460 | 203 | 62 | **265** | 530 |
| Two empty loops replaced by normal no-ops | 6,456 | 209 | 62 | 271 | 542 |
| Those no-ops also simplified in closed contexts | 6,454 | 207 | 62 | 269 | 538 |

These are actual backend emissions, not a decoder-size estimate. Framework
cost is not generally constant across programs; it happens to be 62 in these
three measured outputs. The baseline has maximum path depth 34 and maximum
consecutive zero run seven. Its framework consists of five bootstrap states,
18 low-level register states, six return states, 18 register-selector states,
seven dispatcher states, one root state, and seven control-jump states.
The terminal halt label is excluded from the working-state count.

The useful engineering conclusion is that a globally unused computation can
still save description length by making larger subtrees identical. A compiler
should retain such code as a candidate representative of an identity operation
under an invariant, and compare the **assembled machine**, including dispatcher
and bootstrap costs. Ordinary dead-code deletion is an unreliable objective.

## Reproduction

Use Python 3.10 or later, with only the standard library, in this directory:

```sh
python reproduce.py
```

The driver checks all delivered hashes, regenerates both register invariants,
checks them independently, recompiles all three controls, enumerates the finite
zero-macro search, checks the assembly, and checks that all regenerated files
are byte-identical to the delivered artifacts. There is no network access,
random seed, finite execution horizon, or machine-dependent timing field.

For certificate checking without rebuilding the fixpoint or compiler:

```sh
python verify_register_certificate.py inputs/Prog254.v register_abstract_np0.json
python verify_register_certificate.py inputs/Prog254.v register_abstract_k3.json
python verify_assembly.py
```

`verify_register_certificate.py` imports neither the producer nor the backend.
`verify_assembly.py` imports neither the compiler nor the register analyzer nor
the backend. They are ordinary executable finite checkers, not proof-assistant
kernels. Their mathematical soundness arguments and boundaries follow.

## Register-level invariant

The logical register order is:

| Index | Name | Reachable instruction positions where it is certified zero |
|---:|---|---:|
| 0 | `nextproof` | 0 |
| 1 | `topwff` | 918 |
| 2 | `wffstack` | 1,270 |
| 3 | `axiomcode` | 198 |
| 4 | `param1` | 14 |
| 5 | `param2` | 50 |
| 6 | `scratch1` | 1,476 |
| 7 | `scratch2` | 1,625 |
| 8 | `prooflist` | 0 |

These counts concern instruction *positions* in the unshared source tree,
not numbers of executions, and are the same in both certificates.

Each register's abstract value is a subset of the five disjoint atoms
`{0}`, `{1}`, `{2}`, `{3}`, and `{4,5,6,...}`. A subset is represented by a
five-bit mask: 1 means exactly zero, 30 means positive, and 31 means arbitrary.
The abstract register file is the independent product of nine such subsets.
Unreachable control positions are represented by `null`.

Increment maps exact atoms upward and maps the unbounded tail to itself.
Zero decrement retains only atom zero. Positive decrement discards zero,
maps exact positive atoms downward, and maps the tail to the union of atom
three and the tail. Joins are componentwise bitwise unions. These transfers
overapproximate their concrete operations: the only imprecision introduced
by a single transfer is that decrementing a value at least four can yield
either three or a value at least four.

The finite control graph is computed using Wade's literal path semantics.
For a leaf word `p`, let `inc(p)` be binary increment at that word length
(overflow gives all zeros), with implicit trailing zeros during subsequent
decoding. Let `strip_b(k,p)` remove suffix bits through the kth occurrence of
bit `b`, or remove the entire word if fewer occurrences exist. Successors are:

| Operation | Successor word |
|---|---|
| `INC r` | `inc(p)` |
| positive `DECNZ r` | `inc(p)` |
| zero `DECNZ r` | `inc(strip_0(1,p))` |
| `BREAK k` | `inc(strip_0(k,p))` |
| `CONTINUE k` | `strip_1(k,p)` |
| `HALT` | No successor |

The checker parses the pinned tree independently, decodes each successor,
and checks inclusion of every abstract successor in its target annotation.
It checks an initial vector of all zeros in `register_abstract_np0.json` and
of `nextproof=2` with all other registers zero in `register_abstract_k3.json`.
Both start by decoding the empty program counter at tree root. The zero
start addresses the public Wade backend's advertised initialization; the
two start addresses the register configuration used by the published Mira
machine. The certificates concern these register starts; they do not by
themselves prove either binary bootstrap reaches them.

Both certificates have **6,456 reachable instruction positions and 8,384
nonempty inductive edge obligations**. The four absent positions are the
bodies of the two empty loops below. The producer obtains a fixpoint, but
the checker does not trust that worklist calculation: it verifies the initial
inclusion and the complete finite set of edge inclusions.

**Soundness argument.** The initial concrete vector belongs to the checked
start annotation. If a concrete vector belongs to a source annotation, the
corresponding abstract transfer contains its concrete successor; checked edge
closure then puts that successor in the target annotation. Induction on
the finite number of register instructions proves membership at every
reachable instruction position. Consequently a `null` annotation is never
reached and a mask of 1 proves that register is zero whenever that position
is reached. No inference from a long finite simulation is used.

At the first root-decoded instruction, path `000` (`DECNZ prooflist`), the
invariant certifies `axiomcode=scratch1=scratch2=0`. For the two-start
certificate it also certifies `nextproof>0`. Other registers are unconstrained
there by this product abstraction. This is a statement about this root
instruction interface, not about arbitrary internal decoder states or tape
patterns.

## Two forced-zero loops and the specialization argument

Here `N(a,b)` is a binary sequence node, `D_r` is decrement-and-test,
`I_r` is increment, and `C_2` is continue at level two. Source positions are
zero-based preorder **leaf** indices.

| Leaf | Full path | Closed loop prefix | Loop | Certified entry zeros |
|---:|---|---|---|---|
| 6316 | `111010010110001100` | `11101001011000110` | `N(D_6,N(I_5,C_2))` | 3, 5, 6, 7 |
| 6434 | `111111000` | `11111100` | `N(D_1,N(I_6,C_2))` | 1, 3, 5, 6, 7 |

The first loop transfers `scratch1` into `param2`. The second transfers
`topwff` into `scratch1`. In each case the source register is zero on entry,
so the first decrement takes its zero branch, leaves every register unchanged,
and exits the entire loop normally. Its increment and continue leaves cannot
execute. The excluded leaf positions are 6317, 6318, 6435, and 6436.

Both loops are closed with respect to the surrounding break/continue depths:
their jumps bind within the displayed subtree. Therefore replacing the whole
loop by `BREAK 0`, a normal no-op, preserves the register vector and normal
continuation whenever the source invariant holds. Induction over visits to
the replaced closed subtrees establishes the usual stuttering correspondence
between the two whole register programs. The optimized program reaches the
same next corresponding context with the same register values; this also
transports the guards to later visits. An infinite execution cannot consist
only of steps inside these empty loops, because each visited loop exits after
one failed decrement. Halting equivalence follows at the register level.

The additional simplifications `N(BREAK 0,X) -> X` and
`N(X,BREAK 0) -> X` are applied only when `X` is closed. Then `X` is a
partial normal-returning register transformation: it may diverge, but it
cannot escape into surrounding control levels. Composition with a normal
no-op preserves its returned vector and divergence. This is an ordinary
semantic argument, not a new Lean or Coq proof.

The assembly checker independently reconstructs exactly these two source
transformations and compares them with the unfolded candidate DAGs. It thus
rules out unnoticed additional source edits. It does not replace the
register-level semantic argument or prove the binary runtime simulation.

## Register coalescing and grammar search

We tested a simple sufficient condition for sharing a physical register:
whenever an instruction touches either member of a proposed pair, the other
logical register must be certified zero. Starting from at most one nonzero
member, a shared cell could then represent their sum while every accessed
member has its proper value. **None of the 36 pairs** passes this condition.
For each pair, the certificate records three earliest abstract obstructions,
which the independent checker recomputes. An abstract obstruction may be an
overapproximation; this result does not prove that every more sophisticated
register allocation is impossible. It shows that the basic global product
invariant does not certify any whole-program pair merge.

The zero guards support a second experiment. At either empty-loop position,
any existing closed macro of the form `N(DECNZ r, body)` is also a normal
identity if `r` is certified zero there. Including an explicit no-op gives
15 choices at the first position and 18 at the second. The package checks
the guard certificates before enumerating all **270** combinations and
simplifying closed no-op contexts. The objective in this enumeration is
shared decoder-node count; only its winner is emitted as a binary table.

| Shared nodes | Number of candidate combinations |
|---:|---:|
| 203 | 1 |
| 204 | 1 |
| 205 | 16 |
| 206 | 1 |
| 207 | 14 |
| 208 | 29 |
| 209 | 208 |

The unique 203-node winner keeps precisely the original two transfer macros.
Its DAG, labels, named table, and total numbered table are byte-identical to
the baseline. This is a finite restricted-family result, not a minimality
theorem or an exhaustive search over machine programs.

## Total tables, terminal convention, and the remaining binary obligation

`global_baseline_total.tm` uses a single two-way infinite binary tape, blank
symbol zero, L/R moves, start state zero, working states 0 through 264, and
terminal halt label 265. Every working state has exactly two rows. The
other complete tables use the analogous contiguous convention. Their label
maps and original Wade named tables are included for audit.

The public Wade output has one undefined row, `1.inc` reading 1; the baseline
therefore has 529 defined rows. We fill it with write 1, move R, terminal halt,
adding no working state. Under the explicit convention that an undefined
transition means halting, this totalization preserves the halting predicate
for **every initial configuration**. Until a formerly missing row is reached,
the runs are identical. If it is reached, the partial run halts immediately
and the complete run makes one final move and halts. Tape contents are the
same; the terminal head position differs by one. Thus no unreachability
assumption is needed to justify this particular halting-preserving fill.

Wade's documented INC contract enters `1.inc` on the first zero of a gap of
at least three zeros. A proof that every relevant blank execution satisfies
that contract would show the filled row is unused. We do **not** claim that
proof here. A conservative finite-window abstraction from the blank tape
through radius six still permits both read symbols at that state, so that
test does not establish its unreachability. More generally, the complete
Wade backend/root/spacing simulation, and its connection to the separately
specified formal ZFC proof predicate, remain obligations for treating this
control as an end-to-end consistency machine.

## Files and provenance

- `inputs/Prog254.v`: unchanged full source tree, parsed as finite data.
- `wade/`: unchanged public backend and its retained `LICENSE.wade`.
- `register_abstract.py`: finite invariant producer.
- `verify_register_certificate.py`: independent edge-closure checker.
- `register_abstract_np0.json`, `register_abstract_k3.json`: complete annotations.
- `register_check_np0.json`, `register_check_np2.json`: checked summaries,
  including instruction-position zero counts and root/loop-entry masks.
- `compile_global.py`: exact-tree sharing, guarded source edits, Wade assembly.
- `verify_assembly.py`: independent source/DAG/table/totalization checker.
- `zero_macro_search.py`, `zero_macro_search.json`: finite 270-combination search.
- `global_*.json`, `global_*.tm`: exact DAGs, labels, tables, and measurements.
- `assembly_verification.json`: complete finite assembly-check summary.
- `MANIFEST.sha256`: hashes for all delivered files except the manifest itself.

The source is pinned to Jeff's public repository at
[`297ab8df7e5de329605c3875b4934643b371a5e3`](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3/ZF),
as imported by ProveIt at
[`61e77836565f63582561f54745f633d50efd9c7d`](https://github.com/VladimirReshetnikov/ProveIt/tree/61e77836565f63582561f54745f633d50efd9c7d).
The original source path is `ZF/m254/coq/tm/Prog254.v`; the backend paths are
`ZF/generator/TMBuilder.py`, `tm.py`, `tmdb.py`, and `LICENSE.wade`.
Its 203-node sharing is credited to the existing ProveIt source-09 decoder
report, including its `09-decoder-decoder-README.md` and prior certificate
work. See `NOTICE.md` for authorship and license boundaries.

The exact full-tree SHA-256 is
`1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746`.
The complete 265-state table SHA-256 is
`cc6237ce24f96d7b980529fdbfc85f81f06bb97f362ab2de6af9b4364eaac4fa`.
