# Formalism branch: selector coordinates outside the equality quotient

## Concrete result

The new finite experiment reduces the inherited FC13B **complete equational
packet from 2,324 to 2,194 bits**, a saving of 130 bits. It keeps the original
function symbols `C` and `I`, and replaces `V`, `A`, `U`, `F` by four constant
selectors applied to one ternary function `H`:

\[
 V(x,y)\mapsto H(t_V,x,y),\quad
 A(x,y)\mapsto H(t_A,x,y),\quad
 U(x,y)\mapsto H(t_U,x,y),\quad
 F(x,y)\mapsto H(t_F,x,y).
\]

The four selector constants are fresh symbols and are fully included in the
packet, signature, arities, and every term occurrence. They are not old terms
assumed to have distinct values. The theorem below does not require an infinite
original model, or even four elements in the original model.

The precise improvement is to require congruence only in the two *object*
coordinates of `H`. The selector coordinate is an auxiliary implementation
coordinate, not an operation on the interpreted equality quotient. One clause
replaces four function-congruence clauses:

\[
 E(x,x')\land E(y,y')\ \longrightarrow\
 E\bigl(H(t,x,y),H(t,x',y')\bigr).
\tag{H-cong}
\]

There is deliberately no premise or conclusion transporting the selector from
`t` to an `E`-equivalent `t'`. This is sound because every interpreted original
function uses its own **fixed actual selector** on both sides.

| Encoding | Completed clauses | Equations | Expanded term nodes | Complete bits |
|---|---:|---:|---:|---:|
| Inherited FC13B equational packet | 23 | 21 | 446 | 2,324 |
| New: keep C/I; pack V/A/U/F | 20 | 18 | 420 | **2,194** |
| New: pack all six operations | 18 | 16 | 480 | 2,492 |

The final row illustrates why the number of clauses alone is a poor cost
metric. Packing `C` adds an extra dummy argument to every binary operation;
packing the frequent `I` adds many selector occurrences. Those costs exceed
the saved congruence clauses.

The 203 partitions of the six original positive-arity function symbols were
all emitted and checked under the stated fixed Boolean/Horn encoding. The
minimum is scoped to this family, not to all presentations or all bitcodes.
No Turing-machine state count follows from these numbers. This is an
additional concise finite input for a future ground-rewrite backend, independent
of the new 242-state machine developed on the main branch of this session.

## General theorem and proof

Let T be a finite universal clause theory in a finite first-order signature
with native equality, at least one constant d, and any finite collection of
relation and function symbols. Form its ordinary equality-free completion:
replace native equality by a binary predicate E; assert reflexivity and the
Euclidean law for E; assert E-congruence of each positive-arity function and
relation. Constants need no congruence clause. This completion is satisfiable
iff T is satisfiable, by expansion and the quotient by E.

Partition some of the positive-arity function symbols into groups G. For a
group whose largest arity is r, introduce one (r+1)-ary operation H_G and one
fresh selector constant t_f for each f in G. Replace an occurrence of an
n-ary f by

\[
 H_G(t_f,x_1,\ldots,x_n,\underbrace{d,\ldots,d}_{r-n}).
\]

Keep the equality-equivalence clauses and relation-congruence clauses. Keep
full congruence for every unpacked function. Replace the separate function
congruence clauses for G by the single object-coordinate clause

\[
 \bigwedge_{i=1}^r E(x_i,y_i)
 \ \longrightarrow\
 E(H_G(t,x_1,\ldots,x_r),H_G(t,y_1,\ldots,y_r)).
\]

**Theorem.** The resulting equality-free universal clause theory P(T) is
satisfiable iff T is satisfiable. This equivalence is provable in ZFC. No
cardinality hypothesis on a model of T is needed.

**Forward direction.** Let M be a nonempty model of T. Fix m0 in M, and let
J be a finite set containing 0 and one separate code j_f for every selector.
Use the carrier A=M×J. Set π(m,j)=m and e(m)=(m,0), and interpret

\[
 E_A(a,b)\quad\Longleftrightarrow\quad\pi(a)=\pi(b).
\]

Every original relation is pulled back along π; every unpacked original
function g is interpreted by e∘g_M∘π in its object coordinates; every original
constant c is interpreted as e(c_M). Define the new selector constant by
t_f=(m0,j_f). Thus selectors are distinct *actual* elements of A, although
they all lie in the same E_A-class. For a fixed group G define

\[
 H_G(t,a_1,\ldots,a_r)=
 \begin{cases}
 e(f_M(\pi a_1,\ldots,\pi a_n)),&t=t_f\text{ for }f\in G,\\
 e(m_0),&\text{otherwise}.
 \end{cases}
\]

Ignore padded arguments in the selected branch. Distinct actual selectors
make this definition unambiguous. For every fixed actual t, this function
depends on each object input only through π, so its required object-coordinate
congruence holds. No congruence in t is claimed or needed.

An induction on original terms proves
π([[translated u]]_A,η)=[[u]]_M,π∘η. Predicate and equality literals therefore
have the original truth values under π∘η, including negative literals. Every
translated universally quantified clause holds on *all* assignments into A,
including those that use selector objects as original object-variable values.
All retained congruence and equivalence clauses hold by construction. Hence
A models P(T).

**Reverse direction.** Let A model P(T). The retained reflexive/Euclidean
laws make E an equivalence relation. Interpret T on the quotient A/E. An
unpacked function is well defined by its retained congruence clause. For a
packed f in G define

\[
 f^*([a_1],\ldots,[a_n])
 = [H_G(t_f^A,a_1,\ldots,a_n,d^A,\ldots,d^A)].
\]

The selector is the same actual constant t_f^A in every representative
calculation. Object-coordinate congruence is exactly what makes f* independent
of all chosen object representatives. There is no need for H_G itself to be
an operation on A/E. Relation congruence gives the original quotient relations.
Term induction now transfers every translated clause to its original clause
in T. Therefore A/E models T.

The proof uses only finite products, finite choice of a point in a nonempty
model, ordinary set quotients, and induction on finite syntax. For a recursive
family, the construction and term translations are effective. This note
claims the ZFC-level equivalence; it does not export a PA proof-code theorem.

## From clauses to the complete equational packet

The experiment applies this theorem to the first 13 native-equality FC13B
clauses, then retains their exact inherited equality-equivalence and predicate
congruence clauses, keeps the congruence clauses for C and I, and inserts
(H-cong). No unselected axiom is deleted. It then uses the existing source70
Boolean algebraization unchanged. Its theorem applies to **arbitrary**
equality-free universal clause theories with a constant; it does not require
their auxiliary operation H to preserve E in every coordinate.

Consequently the new packet's nontrivial equational models are equisatisfiable
with the original FC13B clauses. The ordinary ZFC-consistency calibration of
FC13B and the Boolean single-axiom theorem remain inherited dependencies. The
contribution here is the new intermediate theory, its complete proof above,
and its exact concrete data. It is not a fresh reconstruction of FC13B's
entire class-theory interpretation.

The serialized signature, in actual packet order, is

`d:0, top:0, C:3, I:2, p_E:2, p_Inc:2, p_Eq:2, N:2,
tag_V:0, tag_A:0, tag_U:0, tag_F:0, H0:3`.

There are six local variable slots and thirteen constructor slots, each paid
for by a 5-bit opcode. The complete 2,194 bits are 55 signature/capacity bits,
2,119 equation/framing bits, and 20 ground-endpoint bits. The endpoints remain
N(top,top) and top. The 18 equations supply 36 rewrite orientations. The ASCII
bit file's SHA256 (including its trailing newline) is
`1471e362996f04ca2ea59e6e66ee5279e5ea0b9d61413b8dfe2d45812221c4fc`.

## Reproduction and verification

The directory `formalism_dispatch/` is portable. Run

```sh
python formalism_dispatch_packing.py
```

It reads only its five local reference files and the Python standard library,
checks all 203 partition packet roundtrips, checks each retained/added Boolean
equation on every assignment to its distinct propositional atoms, checks the
unaltered baseline as exactly 2,324 bits, and writes all records under
`formalism_dispatch_results/`. The measured best candidate has 114 relevant
Boolean assignments across its equation groups. It also executes 38,416
finite lifted-model assignments checking object-coordinate congruence for
arbitrary fixed selectors, and verifies an example where equivalent selectors
produce inequivalent outputs. That last example demonstrates why imposing
full selector congruence would lose the arbitrary finite-model construction.

These are finite checks of code and the exact input; the unbounded guarantee
comes from the preceding proof. They are not FC13B finite models, ZFC models,
nonhalting tests, or a state-minimality proof. The finite lifted model uses
arbitrary toy operations solely to check the general construction.

The loader, codec and baseline data are unchanged copies of source70. Their
original ProveIt paths, exact hashes and repository pin are retained in
`reference/provenance.json`. This experiment's derivation of a cheaper input
does not assign historical priority to generic dispatch encoding or currying.

## Primary sources inspected and prior-work delta

- Current 243 machine and its calibrated scope:
  https://github.com/VladimirReshetnikov/ProveIt/blob/e58338db7545909907e07a7603e8eb88625c527a/Computability/BusyBeaver/Research/ZFC/candidate-combined243/README.md
- Existing logical engine and why equality deletion breaks substitution:
  https://github.com/VladimirReshetnikov/ProveIt/blob/e58338db7545909907e07a7603e8eb88625c527a/Computability/BusyBeaver/Research/ZFC/logical_engine_completeness.md
- Source70 equational backend, input, proof scope and 2,324-bit baseline:
  https://github.com/VladimirReshetnikov/ProveIt/blob/e58338db7545909907e07a7603e8eb88625c527a/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-166.md
- Source71 alternative bases, equality fusion, NIP and grammar experiments:
  https://github.com/VladimirReshetnikov/ProveIt/blob/e58338db7545909907e07a7603e8eb88625c527a/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-167.md
- Author's original verified 254 machine and SIR source semantics:
  https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/README.md
  https://github.com/jeff87654/busy-beaver/blob/zf-254/ZF/m254/design/logic.md
- Boolean single-axiom primary theorem used by the inherited backend:
  https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf

The current repository already has positive-closure variants, full-profile
quotients, finite-coordinate engines, captured tableaux, quantified NAND,
finite clause kernels, equational search, and alternative propositional bases.
Those are predecessors and controls. The new concrete delta is retaining
separate selector identity outside the interpreted equality quotient and
pricing its exact dispatch packing against the existing packet.

The next useful engineering target is a direct streaming ground-context
rewrite verifier over this finite packet, with all packet initialization,
term storage, repeated-variable checking and fair enumeration charged in the
binary table. A 130-bit input saving is useful only if that complete backend
is competitive; it cannot be subtracted from the existing 243/242-state
register interpreter.
