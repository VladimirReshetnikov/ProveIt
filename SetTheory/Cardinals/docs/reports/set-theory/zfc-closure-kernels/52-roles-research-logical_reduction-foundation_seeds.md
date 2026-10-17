# Semantic startup certificates for the original consistency machine

## Result and scope

The original nine-register proof search admits a broader sufficient startup
criterion than the existing `C254`-theorem certificates. Initial formulas may
instead be uniformly true in a common model of ZFC. This is a change to the
soundness proof used to accept a bootstrap, with the original instruction
program, formula coding, logical axioms and theory schema retained.

For quantifier-free formulas in membership and equality, ZFC proves that truth
under every assignment of sets is equivalent to truth under every assignment
of hereditarily finite sets, and to validity in all equality partitions and
acyclic membership patterns on the finitely many variable names. This criterion
is decidable by an explicit finite search. A rejected pattern can be realized
by explicit hereditarily finite sets; it is therefore an actual falsifying
assignment, not merely a graph-theoretic obstruction. Leading universal
prefixes preserve the equivalence when the whole input is universally closed.

The executable `foundation_seed254.py` implements this decision procedure,
with conservative resource caps, and combines it with four sound closure rules
from the existing seed interface. Below 65,536 it accepts 13,962 formula codes,
versus 13,516 for the upstream incomplete pattern checker, and 4,082 stack
codes, versus 4,051. Thus it adds 446 formula recognitions and 31 stack
recognitions in that census. No assertion is made that the added formulas are
underivable in `C254`: the comparison is to an incomplete recognizer, not to
the theorem set. The mathematical allowance for arbitrary ZFC-valid seeds is
broader than requiring actual `C254` derivations, independently of whether
these particular small examples separate the two classes.

This work supplies no 251-state table. It gives a rigorously justified wider
acceptance condition for searching shorter blank initializers and register
permutations. A concrete smaller machine still needs its complete literal
startup, its runtime simulation and its actual state count.

## 1. The relevant original interfaces

The pinned baseline is ProveIt commit
`beb2c633ae57a0883d28fb6d0c75342d08cfdeda`, with attributed Mira-Cult/Jeff/Wade
sources vendored at busy-beaver commit
`297ab8df7e5de329605c3875b4934643b371a5e3`. The original numerical constructors
are

\[
P(a,b)=\frac{(a+b)(a+b+1)}2+b,\qquad
I(a,b)=4P(a,b),\quad R(i,j)=4P(i,j)+1,
\]
\[
A(i,b)=4P(i,b)+2,\qquad E(i,j)=4P(i,j)+3.
\]

Code 0 is the original semantic truth alias. The literal identity
`I(0,0)=0` is not interpreted as an infinite syntax tree: the total decoding
interface assigns it truth. Code 1 is `R(0,0)`, false at every valuation in a
model of ZFC. Every positive code has strictly smaller formula children.
The proof checker does not alter the code tags, nil convention or falsity
target.

At a structured root, the logical registers are

\[
[N,T,W,A,D,H,X,Y,L].
\]

The top formula is `T`, the cached formula is `H`, and the formula stack is
`W`. The other six fields have numerical/control meanings. The original
`DirtyProgram254.complete_from` establishes completeness from arbitrary values
of all nine fields. Its absorption map to a clean enumerator state leaves
`T`, `H` and `W` untouched. The established sufficient soundness predicate
requires that `T` and `H` be `C254` theorems and that every unshifted Cantor
stack entry be a `C254` theorem. The proposed semantic version replaces only
this soundness predicate.

The exact literal state vector and a whole binary root frame remain essential.
An arbitrary interior program counter is not covered. The logical tail beyond
register 8 and physical spare tape blocks remain separate interfaces.

## 2. Semantic safe-start theorem

Fix one model \(M\models\mathrm{ZFC}\), with its actual membership relation and
identity equality. Interpret every numerical code by the original total
formula interpretation, and put

\[
\operatorname{UTrue}_M(n)
\quad:\Longleftrightarrow\quad
\text{for every valuation }v,\ M,v\models\operatorname{decode}(n).
\]

Define \(\operatorname{USafe}_M(T,H,W)\) by requiring uniform truth of `T`,
`H`, and every head obtained by repeatedly unpairing `W`. Positive stack tails
strictly decrease; stack 0 is the infinite zero stream and contributes only
the already valid truth alias.

**Proposition 1 (semantic startup).** Within ZFC, let a machine execute the
unchanged original register proof search from a whole root frame. Suppose
that whenever ZFC is consistent, there is one model of ZFC in which its three
initial formula fields satisfy `USafe`. Then its nonhalting is equivalent to
\(\operatorname{Con}(\mathrm{ZFC})\), subject to the unchanged full binary
simulation and the supplied finite bootstrap contract.

**Proof.** First assume consistency. First-order completeness, formalizable
in ZFC, supplies a set-coded model of ZFC; use a model satisfying the stated
simultaneous seed condition. All original logical rows are valid uniformly.
The ordinary ZF container and Collection theorems validate the unchanged C/G
bundle, with its actual freshness gates. The same carrier, membership and
identity can be used; no well-founded quotient or reinterpretation of the
initial seeds is needed.

Each actual enumerator branch preserves `USafe`. A successful MP comparison
has top `p` and cache `p→q`, uniformly true, so `q` is uniformly true. Failed
MP produces code 0. DROP pushes the uniformly true top and loads the uniformly
true cache. NIP either pops an already uniformly true stack head or attempts
to halt with cache 1, which uniform truth excludes. AX pushes uniformly valid
logical and theory rows; its GEN output is valid because the previous cache
was true under every valuation, not merely under the currently selected one.
A failed gate produces truth 0. Candidate scheduling and dirty-root absorption
do not change these formula facts. Induction on the number of command steps
therefore excludes halting, and the full simulation transfers this to the
binary machine.

Conversely, inconsistency of ZFC gives a refutation in the original numerical
calculus by the existing calibrated endpoint. The established all-state
completeness theorem forces halting from every initial nine-register vector,
including the present one. This direction requires no seed condition. The
two implications prove the claimed equivalence. ∎

The model in this proof is fixed for the entire run. Separate satisfiability
of individual seeds is insufficient: they must be simultaneously true and
uniform in all valuations in one model, because GEN remains unrestricted.
It is especially convenient to certify every seed as true in every ZFC model;
then the same arbitrary model of ZFC validates all of them at once.

This is an ordinary mathematical proof of a ZFC theorem, with the same
original baseline contracts. No new Lean theorem identifying `USafe` with
`Enum254.Inv` is asserted; that identification would generally be the wrong
interface because the latter names actual derivability.

## 3. Exact acyclic-pattern criterion

Let \(\varphi\) be quantifier-free, using membership, equality, implication
and the semantic truth alias. List its finitely many variable names as
\(v_1,\ldots,v_k\). An equality partition \(\pi\) of those names records which
variables receive the same object. For each partition, let \(Q_\pi\) be the set
of distinct ordered pairs of different classes that occur as queried
membership atoms in \(\varphi\). Enumerate every subset
\(D\subseteq Q_\pi\) whose directed graph is acyclic. Interpret equality by
class identity, membership by `D`, all membership loops by false, and
implication materially.

**Theorem 2 (decision theorem, proved within ZFC).** The following are
equivalent: (i) \(\varphi\) is true under every assignment of sets; (ii)
\(\varphi\) is true under every assignment of hereditarily finite sets; (iii)
\(\varphi\) evaluates true for every finite partition/pattern pair above.
If the finite test fails, the construction below gives explicit hereditarily
finite sets falsifying it. Thus, for each fixed input, the positive case has
an ordinary ZFC proof of its universal closure, and the negative case has an
ordinary ZFC proof of a finite counterassignment. The proof is not an assertion
that ZFC's theoremhood itself is decidable.

**Forward justification of the acceptance test.** Work in ZFC and take an
arbitrary valuation by sets, with the partition induced by actual equality.
Foundation excludes every finite membership cycle and every loop.
The true queried edges therefore form one of the enumerated acyclic patterns.
Unqueried membership edges are irrelevant to evaluation. Induction on the
Boolean formula gives exactly the enumerated truth value, hence truth under
the original valuation. This proves (iii) implies (i); (i) implies (ii) is
immediate.

This argument works even when a model is externally ill-founded: every
externally finite membership cycle is excluded by a finite consequence of
Foundation. Within ZFC the entire construction is a finite induction on codes
and finite sequences, so it has no external soundness assumption about ZFC.

**Realizing a failed pattern.** Suppose the partition has \(m>0\) classes.
Use the von Neumann ordinals \(0,\ldots,m\), and set

\[
t_i=\{i,m\}\quad(0\le i<m).
\]

The `t_i` are pairwise distinct and each has rank \(m+1\). In a topological
order of the finite acyclic graph define

\[
x_i=\{t_i\}\cup\{x_j:(j,i)\in D\}.
\]

Every `x_i` has rank at least \(m+2\), so no vertex object is a tag. If
\(x_i=x_h\), then \(t_i\in x_h\), so \(t_i=t_h\), forcing \(i=h\).
Consequently the vertex objects are pairwise distinct. Moreover

\[
x_j\in x_i\quad\Longleftrightarrow\quad(j,i)\in D,
\]

because the only other possible member of `x_i` is its lower-rank tag.
Assign each source variable the vertex object for its partition class. This
realizes every queried truth value and equality value exactly, so it falsifies
the same formula. Only hereditarily finite sets are used. The complete
extensional set DAG has at most \(3m+1\) nodes: the \(m+1\) ordinals, the
\(m\) tags, and the \(m\) vertex objects. ∎

Thus a negative result is stronger than failure of a heuristic recognizer:
within the supported fragment, it has a concrete counterassignment in HF.
The finite graph by itself is not claimed to be a model of ZFC. It represents
the membership pattern of the displayed finite collection of actual sets
inside such a model. If one phrases the result as an equivalence with
"validity in every ZFC model," that model class must be assumed nonempty;
otherwise validity is vacuous when ZFC is inconsistent. The within-ZFC
set-assignment/HF equivalence above has no such hidden model-existence premise.

Leading universal prefixes introduce no difficulty. After closing all free
names, a finite sequence of leading universal binders holds exactly when its
quantifier-free core is true at every assignment. Repeated or unused binders
do not change that assertion. The `semantic_fragment` API records the exact
removed prefix and classifies its core. Embedded quantifiers are outside this
decision theorem.

## 4. Concrete examples

All examples use the literal original four-tag encoding and falsity code 1.

| Formula with universal closure understood | Code | Result |
|---|---:|---|
| \(v_1\in v_1\to F\) | 688 | valid |
| \(v_0\in v_1\to(v_1\in v_0\to F)\) | 19364 | valid by finite-cycle exclusion |
| \(v_0\in v_1\to(v_1\in v_2\to(v_2\in v_0\to F))\) | 353335282844 | valid by finite-cycle exclusion |
| \(v_0=v_1\to(v_0\in v_2\to v_1\in v_2)\) | 74042232 | valid by identity substitution |
| \(v_0\in v_1\) | 9 | false at the emitted HF assignment |
| \(v_0\in v_1\to(v_1\in v_2\to v_0\in v_2)\) | 72830340 | false at a three-vertex HF chain |

The last negative example is a useful control: Foundation does not make
membership transitive. The test uses acyclicity, not transitivity, of its
graph. Equality partitions are also essential; treating different variable
names as distinct elements would incorrectly validate many false formulas.

The closure recognizer additionally accepts uniform truth, universal
generalization of an accepted formula, implication identity with any payload,
ex falso with any payload, and weakening whose consequent is accepted. These
are semantic rules, with arbitrary embedded quantified payloads permitted
where the rule does not inspect them. The quantifier-free decision procedure
is exact within its resource limits; the combined recognizer remains
incomplete on arbitrary numerical codes.

## 5. Reproduction and independent checks

Run from the delivery directory, supplying the pinned original recognizer:

```sh
python -B foundation_seed254.py \
  --upstream-seed /path/to/ProveIt/Computability/BusyBeaver/Research/ZFC/safe_seed254.py \
  --output foundation-seed-evidence.json
```

`--upstream-seed` is optional; it is used only for the comparative census.
The checker otherwise depends solely on Python's standard library and can be
imported directly by a bootstrap search. No upstream source is changed.

The supplied evidence records:

* All 65,536 formula codes round-trip through the explicit decoder/encoder.
* All 13,516 inputs accepted by the old syntactic formula checker remain
  accepted. The new counts are 13,962 formulas and 4,082 complete stacks.
* Forty-four small query formulas agree with a separate enumeration of full
  finite acyclic relations and all assignments, which does not use equality
  partitions or restrict itself to queried edges.
* Twenty-three negative cases in that suite carry explicit HF set DAGs and
  are falsified by a separate evaluator reading the literal numeric codes.
* A second independent semantic evaluator checks all 13,962 accepted census
  inputs plus the four named positive examples in the actual finite universe
  \(V_3\), with Ackermann codes `{0,1,2,3}`. It checks 155,977 valuations of up
  to four free names and reports no failure. This finite universe is a
  diagnostic structure, not a ZFC model.
* Falsity 1, stack 1 and buried-falsity stack 60 remain rejected. The old
  unshifted stack representation is preserved.
* Name and edge resource limits return `unsupported` (unknown), never a
  negative mathematical conclusion or a positive certificate.

These computations check the executable implementation. The unrestricted
mathematical arguments are the induction and HF construction above; finite
sampling is not offered as their replacement.

## 6. Integration into a smaller-machine search

A candidate bootstrap should first be parsed as the required whole root tape
frame, including the exterior, exact head, empty PC, padding, nine primary
registers and all spare blocks. Convert the physical register order to the
logical order of that candidate, then call `state(logical)`.

Only the formula fields are checked. The six numerical fields `N,A,D,X,Y,L`
retain the freedom of the checked dirty-root absorption interface. Each stack
head is examined all the way to tail 0, so a buried inconsistency is not
ignored. The result can be stored with the exact startup tape as a finite
semantic certificate. The existing syntactic certificate can still be
preferred when available, since it composes directly with the already checked
`Enum254.Inv` theorem; semantic-only certificates require the separate
model-relative soundness invariant of Proposition 1.

This criterion can be combined with independently proved reset or stack-barrier
families by taking the union of their certified bootstrap conditions. In
particular, the source-42 ordinary barrier result recorded in
`dirty_program254.md` permits arbitrary old formula fields at its exact
`PL=NP=D=0` entry. That is a different sufficient condition, with its own
actual-enumerator composition obligation. Semantic certificates remain useful
when those special numerical equalities fail, because the six numerical fields
are unrestricted here. No barrier theorem or reset continuation is inferred
merely from the success or failure of this formula checker.

For an interior root candidate or a modified instruction program, this check
alone is insufficient. One must prove that the continuation reaches a genuine
root while preserving the proposed model-relative invariant. A runtime
optimization must still have its own complete simulation proof. The added
446 small formula and 31 stack cases quantify the widened search screen; they
are not a state-count saving or evidence that a 251-state machine exists.

The corpus review also rejects several tempting shortcuts: the retired
equality-free C/G 252-state benchmark has an abstract finite-sort
countermodel; GEN elimination has a correct source argument but measured
285-state cost; the successful-MP dummy-push deletion already has an exact
literal-table mapping but retains all 252 states and lacks a sufficient changed
bootstrap. None of those results may be converted into a state reduction by
subtracting formula nodes or partial compiler costs.

## Attribution and proof boundary

Mira-Cult designed the original machine and calculus; Jeff supplied its
verification; Andrew James Wade supplied the compiler framework; mira-emmy
supplied the prior 253-state reduction. ProveIt supplies the current register
permutation, the calibrated 252-state endpoint, dirty-root contracts and
incomplete syntactic seed recognizer. This contribution supplies the explicit
semantic seed checker, the broader startup soundness argument and its exact
finite-pattern/HF certificate interface. The HF tag construction was found
and independently reviewed within this investigation. No literature-wide
priority claim is made for the elementary decision theorem, and no smaller
verified machine is claimed.
