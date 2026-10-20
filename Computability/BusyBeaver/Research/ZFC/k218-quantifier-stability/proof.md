# K/S plus quantified double-negation elimination

This is an ordinary syntactic calibration proof for one precise replacement
calculus. It is not a new machine construction or a proof-assistant check.
It uses the exact Code254 numerical operations and KCode222 retained rows.

Let `T=0`, `F=1=R(0,0)`, `N A=I(A,F)`, and
`Ex_i A=N(Q_i(N A))`. Replace only unrestricted rho8 by the two K/S
schemas and the new two-parameter schema

    NN(Q_i A) → Q_i A.                                      (QS)

Retain truth zero, MP, theorem-only GEN, rho1–rho6, merged equality G, and
every original gated bundle, with its exact literal gate `c≠a,b`. In
particular, retain B6 `Ex_i(Q_i A)→A`. No substitution or renaming rule is
added. The conclusion is pointwise equivalence of numerical derivability
with the accepted unrestricted-rho8 calculus, including derivability of
the sole falsity code 1.

The scratch checker `check_derivation.py` constructs explicit finite
parametric Hilbert proof DAGs. Its only proof rules are MP and GEN on a
closed theorem. Temporary assumptions are eliminated by the explicit K/S
deduction transformation; no open assumption is generalized. Every
primitive axiom formula is generated from its named row and parameters.
Its bundle instances use `c=max(a,b)+1`, an explicit witness for the
unchanged gate. A parameter means an arbitrary native natural code,
not a formula variable with an assumed substitution theorem.

## Intuitionistic infrastructure from retained rows

K gives `F→N(Q_i(N(Q_i A)))`, because its consequent is itself an
implication ending in F. Compose with B6 to obtain `F→A`. K/S and this
explosion family support ordinary intuitionistic implicational reasoning.
The checker expands that reasoning into K/S and MP.

For each fixed label i, rho1 gives `N(Q_i(N E(i,0)))`. Necessitate the
closed theorem `F→N E(i,0)` and use rho2. Thus `Q_i F→Q_i(N E(i,0))`,
and rho1 gives seriality `Q_i F→F`. This works also at i=0, and does not
use universal instantiation or any freshness premise.

If a closed theorem `X→Y` is available, intuitionistic contraposition,
theorem GEN and rho2 give `Q_i NY→Q_i NX`. Contraposition once more
gives existential monotonicity `Ex_i X→Ex_i Y`. This derived operation
is applied only to closed theorems below.

## Persistence implies stability

Suppose `NN(A→Q_i A)` is a closed theorem. Intuitionistic reasoning gives
the closed theorem `h': A→NN(Q_i A)`: from A and `N(Q_i A)`, an assumed
`A→Q_i A` yields F, contradicting the given double negation.
Necessitating this closed h' and using rho2 gives
`Q_i A→Q_i NN(Q_i A)`.

Put `Z=Q_i N(Q_i A)`. Under Z and `Q_i A`, the last implication and
normality give `Q_i F`, hence F by seriality. So `Z→N(Q_i A)`. Combining
with h' gives `Z→NA`. Consequently `NNA→NZ`. The exact retained B6
instance is `NZ→A`, so `NNA→A` follows. Every necessitation in this
argument is of a closed theorem; temporary Z/A assumptions are discharged
with K/S only.

## Membership and equality bases

For arbitrary label codes a,b choose `c=max(a,b)+1`. The exact native
bundle is `N(I(V,J))`, where `V=I(R(a,b),Q_c R(a,b))` and
`J=nks(a,b,c)` is the literal seed core. From NV, explosion gives V→J,
which contradicts the bundle. Thus NNV. The persistence lemma proves
`NN R(a,b)→R(a,b)` for every membership atom. The J subterm is kept
literal in the checker; no assumption about its content or truth enters.
The code/private-label coupling in J is preserved, and both gate
inequalities are checked by the fresh-label witness.

For equality reflexivity put `k=R(a,a)`. The exact unrestricted merged
row G(a,a,k) is

    E(k,a) → (E(k,a) → Q_k E(a,a)).

Contraction gives `E(k,a)→Q_k E(a,a)`. Existential monotonicity and
rho1(k,a) give `Ex_k Q_k E(a,a)`; B6 gives E(a,a). Then G(a,b,a),
followed by MP with reflexivity, gives
`E(a,b)→Q_{R(a,b)}E(a,b)`. Double-negation introduction and the
persistence lemma prove stability of every equality atom. Neither a
quantifier-instantiation rule nor an equality-substitution theorem is used.

## All native codes are stable

Strong induction on the actual natural code n proves `NN n→n`.

* At n=0, truth zero and K give `NN0→0` directly.
* A positive remainder-1 code is an R atom, covered above. This includes
  F=R(0,0)=1.
* A remainder-3 code is an E atom, covered above.
* A remainder-2 code is Q_i A, so its stability is the new QS axiom.
* A positive remainder-0 code is I(A,B). Its components are smaller than
  n: the pairing inequalities give each component ≤pair, and positive
  n=4·pair gives pair<n. In fact only stability of B is needed.

The last step is intuitionistic. Under `NN(A→B)` and A, an assumption
NB would refute A→B, a contradiction. Thus NNB, then B by its induction
hypothesis. Discharge A and `NN(A→B)` to get stability of I(A,B).

The raw alias I(0,0)=0 creates no circular induction: handle zero before
the positive-code split. All other positive constructor components have
the required strict bound. More code equalities merely identify formulas
of our schematic derivations; no proof step relies on constructor
injectivity, disjoint tags, or an occurs-check. The finite checker tests
I(0,0)=0 and also constructs a stability proof for the syntactic I(0,0)
term; its instantiation is a valid proof of the same native-zero theorem.

This is a uniform constructive proof transformation. Native decoding,
fresh max+1, and the fixed proof-DAG operations are primitive recursive;
the strong recursion on smaller codes can be implemented by bounded
course-of-values recursion. No search for a model or for an unbounded
proof is needed.

## Recovering the exact classical row

For completeness, arbitrary code stability gives Peirce directly. Under
`(A→B)→A`, assume NA. Explosion gives A→B, hence A and contradiction.
So NNA, then A. Discharge the initial hypothesis.

One can recover rho8 without calling Peirce. Under
`h:(C→U)→A` and `k:A→C`, assume NC. From an assumed C, explosion
gives U; discharge C to get C→U. Applying h then k yields C,
contradicting NC. Therefore NNC, then C by its code-induction stability.
Weaken by arbitrary B and discharge k,h. The result is exactly

    ((C→U)→A) → ((A→C)→(B→C)).

The checker includes the closed finite conditional theorem
`(NNC→C)→rho8(A,B,C,U)`. Apply it to the already constructed stability
proof for the actual code C. This explicitly respects all four numeric
parameters and does not replace the fourth parameter by a code-dependent
atom.

Every original-calculus proof therefore translates, node by node, into
the replacement calculus: retained axiom nodes are identical; rho8 nodes
use the construction above; MP/GEN are unchanged. Conversely, the
original unrestricted-rho8 calculus proves K and S and classical DNE for
every numerical code, hence QS. Translating these three new axiom kinds
back and retaining all other nodes gives the reverse proof translation.
The existing accepted classical propositional basis supplies this upper
direction; it is not assumed in the lower construction. Thus the two
calculi have exactly the same derivable codes and the same consistency
statement. Any later machine claim still requires exact enumerator
coverage, literal source binding, source/runtime checks, and state counts.

## Checked scope and preserved attempt

The own executable Hilbert-DAG check passed on its second attempt.
The first attempt failed solely because a local Python list named
`serial` shadowed the seriality-builder function before execution of the
proof construction; the exact script/logs and two-name correction are
preserved in `history/attempt1`. No failed mathematical assertion was
relaxed. The passed finite proof constructions and raw outputs are in
`result.json`, `proof-dag.json`, and `run2.*.log`. This remains ordinary
proof plus a rule-level executable check, not a Lean/Rocq
kernel theorem. In particular no source-DAG or binary-state saving is
claimed here.
