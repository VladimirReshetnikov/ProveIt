# Local mathematical results and exact limits

This package supplies new local source experiments and finite implementation
checks. It supplies no binary machine below 196 states, no internal PA
consistency biconditional, and no proof compiler for a changed numeric calculus.
The repository snapshot is `3268f238cb6be4b9c68b6cddaf289f173f77566e`.

## 1. Eight equivalent spellings of the gate

Put `X = M(a,b)`, `P = property`, and `Y = M(c,b)`. The matrix of the original
separation clause is

    (X -> (P -> Y)) and (Y -> P).

Its first conjunct is equivalent to `P -> (X -> Y)`: both are false exactly
when `X` and `P` are true and `Y` is false. The two conjuncts may also be
exchanged. These two choices yield four matrices. They are equivalent under
every assignment in every first-order structure, so placing them under the
same quantifier preserves their meaning. The outer gate has shape

    not (Delta -> (V -> Q)).

Exchanging `Delta` and `V` preserves this formula, since both spellings mean
`Delta and V and not Q`. Thus the choices give eight gate spellings. The
original first axiom head remains present, so its existing finite derivation
of explosion, followed by the classical implication basis, supplies the
ordinary propositional proof transformations. This argument does not justify
changing that first head itself, or rearranging the sole propositional basis
axiom before recovering its implication rules.

The script `gate_variants.py` checks 40 Boolean cases and emits all eight
77-macro words, with either equality orientation. Its dynamic program also
establishes a narrowly defined minimum: over the three atoms `X,P,Y`, the
constants false and true, and implication alone, a formula for this matrix
requires six implication occurrences. It enumerates exactly four minimum
formulas. The dynamic program is complete for this additive tree-size metric
because a minimum formula's children must have minimum size for their truth
functions. This is neither a lower bound for shared DAGs nor a lower bound on
the complete gate, source program, or Turing-machine state count.

## 2. Reversing membership and equality encodings

Let `pair(a,b) = (a+b)(a+b+1)/2 + b`. Mode bit 0 reverses the two numerical
label arguments of equality; mode bit 1 reverses membership. Implication
remains `4*pair(A,B)`, and universal quantification remains
`4*pair(body,binder)+2`. The decoder reverses precisely the corresponding
atomic arguments. All four modes retain truth code 0 and false target
`1 = M(0,0)`.

Define `R_mode(0)=0`. On a nonzero implication code, recursively recode both
children. On a universal code, recursively recode the body and keep the
numerical binder. On an atomic code, swap its two literal labels exactly when
the relevant mode bit is set. These definitions terminate: at every recursive
call the child is strictly below the positive parent code, by the component
bounds for Cantor pairing. The exceptional code 0 is a separate base case.

**Lemma.** For every natural code `n`, decoding `R_mode(n)` in the new
convention gives exactly the same named syntax as decoding `n` in mode 0.
Furthermore `R_mode(R_mode(n))=n`, and all names and free-name sets are
preserved.

**Proof.** Induct on the decoded finite constructor tree. At an implication,
both child induction hypotheses apply. At a quantifier, the body induction
hypothesis applies and its binder is literally unchanged. At an atom, the
recoder's argument exchange is undone by the decoder; applying the exchange
twice gives the original labels. Code 0 stays the special truth alias. These
same cases show involution and name preservation. Equivalently, the induction
can be carried out by strong induction on positive code, using the strict
recursive-child bound. No numerical labels are recursively treated as formula
codes in the atom or binder cases.

**Freshness lemma.** Every label occurring in a decoded positive code `n` is
strictly below `n`, in each orientation. In particular both `n` and
`R_mode(n)` are fresh names for the common decoded syntax.

**Proof.** For an atom the two labels are Cantor components, each at most the
pair value, and the tag makes the positive parent larger. At a quantifier its
binder satisfies the same bound, and every name of its body is below the body
code by induction. At a positive implication both children are strictly below
the parent; apply induction. Code 0 has no names. Orientation does not change
these inequalities. Apply name preservation for the claim about the old code,
and the same lemma to the new code for the claim about the new code.

These syntactic lemmas do **not** make the private-code gate commute with
recoding. Recoding a gate with original property code `c` keeps the binder
label `c`, while the property has code `R_mode(c)`. The new emitter instead
uses its property code as its binder. Even the outer guard can change: in the
membership-transposed mode, `R(5)=9`. The old parameters `c=5,a=9,b=0` satisfy
`c!=a,b`, but naively replacing `c` by 9 fails the new guard.

Uniform transport of native proofs therefore requires an actual fresh-binder
or padded-property argument, including alpha-renaming and guarded instances.
It is not provided here. The exact result supplied by
`membership_transpose_config.py` is an emitter-search family: four encoding
conventions, six independently renamed axiom heads, their permitted
antecedent exchanges, and eight gate spellings. It checks 1,792 numerical
emissions and reproduces the inherited two equality-only modes exactly.
`orientation_recoding.py` checks the inductive lemmas on 16,384 mode/code pairs
and verifies the explicit guard counterexample.

## 3. A direct macro for a transposed implication

Use registers `T=r1, W=r2, A=r3, D=r4, H=r5, S=r6, R=r7, L=r8`.
The original 67-site `node75` reads a field `x` from the Cantor-coded input,
adds it to `D`, and constructs `4*pair(T,D+x)`. A direct 37-site alternative
constructs `4*pair(D+x,T)`, with the same field consumption and frame.
It consists of four closed fragments:

    node32; node53; copy D to S preserving D using R; node64.

Here `node32`, `node53`, and `node64` are unchanged source fragments.
The new copy fragment is exactly

    ((dec4, node40), (dec7, node52)),

where `node40=(inc7,(inc6,continue3))` and
`node52=(inc4,continue2)`. Its contract assumes `S=R=0`. After `k` iterations
of its first loop, from initial `D=d`, the values are
`D=d-k,S=k,R=k`; the loop terminates at `k=d`. After `j` iterations of the
restoration loop, they are `D=j,S=d,R=d-j`; this loop terminates at `j=d`.
Thus it preserves `D`, copies it to `S`, clears `R`, and leaves every other
register unchanged.

The unchanged `node32` has the Cantor-reader contract
`L=pair(x,tail),S=R=0` to `L=tail,S=x,R=0` with the other registers unchanged.
The unchanged `node53` drains `S` into `D`. For `node64`, its first fragment
`node46` starts from `T=t,S=s,R=0` and finishes with
`T=S=0,R=triangle(s+t)+t`. One way to see its rank is to group its transfer,
one decrement, and restoration loops. After the initial transfer the total
counter is `s+t`; successive outer iterations decrease that total by one,
adding its triangular sum to the initially accumulated `t`. Its last fragment
`node63` replaces each unit in `R` by four increments of `T` and clears `R`.
Consequently `node64` computes `T=4*pair(s,t)` and clears `S,R`.

Composition gives the all-natural contract

    (T,D,L,S,R)=(t,d,pair(x,tail),0,0)
       -> (4*pair(d+x,t), d+x, tail, 0,0),

with every other register unchanged. All loops terminate by the displayed
decreasing counters and the unchanged Cantor-reader invariant.

The literal occurrences of old `node75` are the half-open source intervals
`[224,291)` and `[3693,3760)`. Replacing both removes 60 primitive sites:
3812 becomes 3752. All five binary associations of the four closed fragments
have the same effect, but the complete source DAG grows from 159 to 162
internal nodes. No state reduction follows. The implementation checks 400
finite old/new contract cases and emits each exact subtree.

Reversing implication throughout the calculus also changes formula emission.
The rho8 prefix has a further scheduling issue: it uses the original `D`
before adding the newly read field. `implication_transpose_words.py` preserves
that order explicitly. It uses one reversed stack-pair macro at the final
rho8 constructor. This macro is `node17; swap(T,S,node46); node63`, so its
pairing contract follows by register renaming of the preceding argument. The
file checks 343 local reverse-pair cases and 243 complete prefix cases. The
inherited source association is expensive for these words (237--245 internal
nodes); they need a new association and physical allocation. They are not a
completed implication-transposed consistency machine.

## 4. A concrete logical trap avoided

It is tempting to replace the first axiom head
`(exists D forall D H) -> H` by `not H -> forall D not forall D H`, using
classical contraposition. In this native calculus, however, `not A` means
`A -> 1`, and explosion for 1 is derived using the original first head.

The replacement alone does not give an equivalent derivation system. Consider
the following algebraic valuation of all numeric codes: implication is
classical Boolean implication, universal quantification is the identity,
all equality atoms are false, and `M(a,b)` is true exactly when the literal
labels are equal. Code 0 is true, consistently with its implication alias;
code 1 is also true. Hence every relative negation `A -> 1` is true.
All instances of rho8, quantifier commutation and distribution are true.
The two membership-transport heads have a false equality antecedent, and the
equality-existence head, every gate, and the proposed replacement head are
true. Modus ponens and generalization preserve truth. But `H=M(0,1)=9` is
false, and the old first head with `D=0,H=9` is false. Induction on derivations
therefore proves that this old head is not derivable in the changed calculus.
`head1_countermodel.py` implements this valuation and checks 14,497 finite
instances as a transcription check. The argument itself covers all parameters.

Adding an explicit explosion schema `1 -> H` would repair this particular
defect: explosion and Peirce yield double-negation elimination, and the new
first head then yields the old one. It also adds an emitted axiom and changes
the command interface. That repaired system was not compiled here.
