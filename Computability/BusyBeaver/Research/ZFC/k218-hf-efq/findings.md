# HF plus explicit explosion: exact progress and remaining gap

Opening, 20 October 2026. This note studies the native numerical calculus with truth0, MP, theorem-only GEN, retained rho1–rho6/G and the full literal gated bundle, replacing rho8 by

    HF(A,B,C) = ((C→F)→A) → ((A→C)→(B→C))
    EFQ(A) = F→A,

where F=R(0,0)=1. The native implication alias I(0,0)=0 is retained. No arbitrary formula substitution, K, S, deduction theorem or implication-context composition is assumed. There is currently **no calibration or full-calculus countermodel** in this packet.

## A positive proof transformation

For any supplied closed derivation of NN(C), instantiate HF(F,B,C):

    NN(C) → ((F→C)→(B→C)).

One MP with the supplied derivation and a second MP with the exact EFQ(C) axiom derive B→C. Thus **weakening of double-negated theorems** is admissible. With B=0, another MP with native truth derives C. This is a primitive-recursive, three-MP transformation establishing **closed-theorem DNE**. It is not a derivation of the formula NN(C)→C: that would require a still-unproved deduction/composition principle. No GEN is used.

There is an unconditional modal bootstrap. Put Z_i=Q_i N(Q_i F). The retained rho6(i,F) is literally NN(Z_i). The transformation yields B→Z_i for every natural B and then Z_i itself. The explicit seven-node proof uses rho6, HF, EFQ, truth and three MPs only. `validation.json` records the exact parameterized ASTs. At C=0, the final major I(0,0) is simply native0; native MP with0 still returns0. No positive-code assumption on C was introduced.

This bootstrap genuinely escapes the propositional closure described next. It gives quantified theorems and their weakenings, but it does not presently yield N(Z_i), K/S, arbitrary identity, or a reflection rule that drops an arbitrary Q.

## An exact obstruction for the propositional fragment alone

Consider **only** truth, HF, EFQ and MP. No quantifier, equality, membership, bundle or GEN axiom/rule is included in this subclaim. Define

    E(x) = F→x,
    H(a,b,c) = HF(a,b,c),
    L(b,c) = (F→c)→(b→c),
    D(b,c,d) = (L(b,c)→N(c))→(d→N(c)).

All MP theorems of this fragment lie in the four families 0, E, H and D. Conversely every D is obtained by one MP:

    minor: H(F,b,c) = NN(c)→L(b,c),
    major: H(L(b,c),d,N(c)),
    result: D(b,c,d).

The following exhaustive major/minor inversion proves MP closure on actual native codes. Implication is injective, including its zero alias. Every N(c) is positive and implication-headed, hence cannot equal the atomic falsum F.

* An E major requires the minor F. All four families have implication tag or equal0, so none is F.
* A native0 major is I(0,0) and can only return0 from minor0.
* An H major requires a minor N(C)→A. An E minor would force F=N(C); a zero minor would force N(C)=0. Both are impossible. A D minor would force N(c)=F, also impossible. An H minor H(a,b,c) forces a=F, C=N(c), A=L(b,c), and returns exactly D(b,c,B).
* A D major requires a minor L(b,c)→N(c). An E minor would force F=L(b,c), an implication-headed positive code. A zero minor is impossible because N(c)>0. An H minor would have consequent (a→x)→(y→x)=N(c), forcing y→x=F. A D minor would force its own N(x)=F. These are all impossible.

The special possible zero consequent of H does not evade these cases: matching it to a positive N(c) already excludes zero; in the successful H/H case the forced parameter a=F excludes the all-zero alias.

For example, the K instance

    K(0,F) = 0→(F→0)

is outside all four families: it is positive with antecedent0, while every E/H/D antecedent is positive. Therefore **HF+EFQ do not supply even this K instance through propositional MP alone**. The retained native rows must play a substantive role in any positive calibration. This fragment theorem is not an obstruction to the full proposed basis: the modal bootstrap Z_i above explicitly leaves the four-family grammar.

## One focused bounded constructor search

A single15-second search included truth, HF, EFQ, rho1–rho6, merged G, theorem-only GEN and exact universal numeric schema instantiation followed by MP. It retained at most2,500 nodes of syntactic size at most55; it produced1,699 nodes, processed1,120, and tried1,554,830 ordered schema pairs. No universal identity, K, S, Peirce, formula-DNE or QS target was found.

The literal gated bundle was **omitted**, never ungated or replaced by a stronger axiom. The constructor unifier is incomplete, including occurs-check exclusions and its handling of possible zero-alias solutions. Consequently the negative search result proves no unprovability, consistency or completeness statement for either the whole calculus or the searched fragment.

Every one of the1,699 saved DAG nodes was separately rechecked by `validate.py`, including the two explicit universal instantiations for every condensed MP and closedness of each GEN. The same inert reader checked the seven-node modal bootstrap and the two-step generic weakening transformation. Its first manual-instantiation validation used recursive unifier substitution for an identity mapping, incorrectly detecting a cycle. That reader-only failure and source are preserved in `history/validator-attempt1/`; the successor uses ordinary simultaneous substitution for manual axiom instantiations. The search DAG was unchanged.

## Consequence for further work

The exact missing issue is formula-context composition or an alternative proof encoding that exploits the retained modal/native rows. Admissible DNE alone does not license discharging the premise of its proof transformation. Likewise the full negative bundle cannot be converted to persistence or a negated core using an assumed K/S deduction theorem. Any such conversion needs an explicit new proof.

This packet does not run a finite-model search, price source macros, invoke a proof assistant or change a machine. It gives one useful proof rule, a precise propositional limitation, and a bounded search record while leaving the full calibration open.
