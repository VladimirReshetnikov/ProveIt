# Exact syntactic gap behind the fresh-diagonal argument

> Update, 2026-10-20: the fixed R(b,c) reverse-calibration lead has since closed negatively by a full-seed syntactic consistency invariant. See `UPSTREAM_FIXED_ORIENTATION_CLOSURE_REVIEW.md`. The conditional semantic theorem and earlier gap analysis below remain valid historical results; statements that full consistency was still open are superseded.

Date: 2026-10-20. Follow-up to RESULTS.md. This note isolates native proof obligations; it supplies no new T_bc proof of DNE, K/S, or unrestricted rho8. No additional formula enumeration was performed.

## 1. What can be written down with no missing inference

All expressions below denote exact natural-number codes using the pinned functions I, R, Q, E, with raw truth 0 and F=1. Define, for c>0,

    u_c = R(0,c)
    h_c = I(I(I(c,u_c),1), I(I(1,c),I(0,c)))
    d_c = I(I(I(c,1),1),c)
    k_c = I(I(1,c),I(0,c))
    g_c = I(I(I(c,1),1),k_c).

Thus h_c is the literal changed row L(1,0,c,R(0,c)); d_c is DNE(C); g_c is the diagonalized row L(1,0,c,1).

T_bc proves h_c by its changed rho8 rule and Q(c,h_c) by the primitive theorem-GEN rule. Because no label in decoded c equals c, capture-free replacement of variable label c by 0 in the decoded h_c gives exactly g_c. This last sentence is an identity between decoded formulas, NOT an admissible proof transformation.

The exact specialization bridge needed to turn that identity into a two-MP proof is

    J_c = I(Q(c,h_c),g_c).

There is no universal-instantiation rule in Thm222.v. The retained rho6 is

    I(Ex(i,Q(i,A)),A),
    Ex(i,A)=I(Q(i,I(A,1)),1),

not I(Q(i,A),A), and it is not an arbitrary substitution rule. Merely applying GEN cannot justify J_c.

## 2. The exact equality information is available, but its elimination is not

Two retained literal rows are

    rho3(c,0,0) = I(E(c,0),I(R(0,c),1)),
    rho1(c,0)   = Ex(c,E(c,0)).

The first says that under equality of the endpoint labels, the offending membership atom implies native F. The second supplies an equality witness in the native negative-universal encoding.

To use them in the intended way one needs both:

- Positive-context transport from R(0,c)->1 to h_c->g_c.
- Elimination of the equality witness with the c-free conclusion g_c (or an equivalent specialization theorem).

Neither operation is primitive. In particular, they cannot be introduced by writing a proof under an equality assumption and then silently discharging that assumption. The usual deduction theorem already depends on propositional K/S or equivalent structure.

A useful explicit transport target, without claiming it is proved, is

    M_c = I(I(u_c,1), I(h_c,g_c)).

This is an ordinary intuitionistic propositional theorem once a suitable implicational basis is present. It uses composition inside the antecedent C->u_c and then twice through surrounding implications. Obtaining M_c from the changed row is an actual remaining proof task, not a consequence of numerical freshness.

Even M_c alone is insufficient: after combining it with rho3 one still needs the equality-witness elimination/fresh-conclusion step. The concise combined target remains J_c.

## 3. Equality reflexivity itself currently imports the missing machinery

The exact source is latest219_baseline/k225-formal/rocq224/src/G222.v, read as inert text. Its proof of E(x,x) starts with z=R(x,x), e=E(z,x), p=Q(z,E(x,x)). Merged G gives the literal theorem

    I(e,I(e,p)).

The proof then uses a contraction/deduction step to obtain I(e,p). A sufficient explicit contraction formula is

    I(I(e,I(e,p)),I(e,p)).

It next uses existential monotonicity, implemented through the theorem

    I(Q(z,I(e,p)), I(Ex(z,e),Ex(z,p))).

GEN of I(e,p), this theorem, and rho1(z,x) give Ex(z,p). Retained rho6(z,E(x,x)) then gives E(x,x).

The checked upstream proof of the contraction step uses the deduction machinery from full propositional logic. Its existential-monotonicity proof uses contraposition, quantifier normality, and that same deduction machinery. Therefore neither equality reflexivity nor general equality substitution may currently be cited as already available in T_bc. This is a dependency issue, not a claim that they are unprovable there.

The primitive membership-substitution rows remain usable exactly as displayed in Section 2; they do not by themselves give substitutivity of every formula context.

## 4. Diagonalization does not syntactically equal DNE

The resulting g_c is literally

    NN C -> ((F -> C) -> (0 -> C)),

not NN C -> C. In a Heyting algebra F->C=top and top->C=C, which was legitimate in the semantic theorem. Those simplifications cannot be assumed as equations between native codes, nor as unproved proof rules in T_bc.

There is a clean conditional sufficient package:

1. Native K(p,q)=I(p,I(q,p)).
2. Native S(p,q,r)=I(I(p,I(q,r)),I(I(p,q),I(p,r))).
3. Native explosion I(1,p).
4. J_c for every positive c.

If these four families are derived in T_bc, unrestricted rho8 follows by a uniform finite proof translation. Indeed, J_c and GEN h_c give g_c. Under the sole temporary assumption NN C, MP with g_c gives (F->C)->(0->C); MP with explosion and then native truth gives C. The ordinary propositional deduction theorem, justified by K/S and using no GEN under that temporary assumption, yields d_c. For c=0, the desired DNE-to-truth implication follows from K and truth. K/S/explosion/DNE give the classical implicational basis and every unrestricted L instance.

This package is sufficient, not asserted minimal, and none of its unproved families is being added to the candidate for free.

## 5. Why a DNE-only result would not establish calibration

The previously proved full-HC countermodel for the U=F restriction validates:

- all retained native non-rho8 rows and the entire support-bearing seed K;
- every L(A,B,C,F);
- unrestricted identity, K, and explosion;
- unrestricted native DNE;
- ordinary universal-instantiation formulas under its Boolean designatedness quantifier.

Nevertheless it refutes composition B and S. In its implication matrix, let p have value 1, q value 0, and r value 2. Then both

    B(p,q,r)=(p->q)->((q->r)->(p->r))
    S(p,q,r)=(p->(q->r))->((p->q)->(p->r))

have value 0, not designated 3. Contraction (p->(p->r))->(p->r) also fails when p=1,r=2.

These are genuine native instances: choose p=R(2,3)=73, q=F=1, r=R(4,5)=201 and use disjoint coordinate pairs to realize the two membership colors. Their exact codes are

    B(73,1,201) = 24117706726831771846144,
    S(73,1,201) = 8877867661581053609800.

The new fixed finite checker check_bootstrap_gap.py verifies the matrix statements and these code calculations; bootstrap_gap_receipt.json records them. Full seed soundness is supplied by the earlier unbounded HC proof, not by that finite check.

This does NOT give a model of T_bc: that model fails its original coupled rows. The exact conclusion is that an attempted lower proof which throws away the coupled row's extra content and factors only through diagonalized U=F rows, DNE, identity, K, explosion and ordinary instantiation still lands in a known weak full-K theory. Recovering genuine composition/congruence remains essential.

## 6. The inherited short K proof also cannot be reused literally

The pinned CD230 proof of K has the path

    cd16(p,q)
      -> cd15(0,p,q)
      -> cd1(p,p,q,I(q,p),0)
      -> cd0(p,I(q,p),p,q).

The last leaf is unrestricted L(A=p,B=q,C=p,U=I(q,p)). Under the bc restriction it would require I(q,p)=R(q,p). This is impossible for every natural p,q: the former is congruent to 0 modulo4 and the latter to1, including p=q=0. Thus this literal proof needs a substantive replacement, not an auxiliary-variable renaming. This observation does not exclude other K proofs.

## 7. Concrete next bridge to price, without a source-fit claim

S is the strongest standard three-input bridge worth targeting first: it supplies the implicational distribution underlying deduction and context congruence; unlike diagonalized rho8 or DNE, it is directly excluded by the old full-HC matrix. B is a smaller related transport target, but it does not by itself supply the contraction/discharge step.

Both use only the existing three numeric input fields and the existing implication constructor; neither restores a fourth independent input reader. That makes a shared or fused source implementation a concrete pricing question. It does NOT prove that adding either row fits the 205-node source, that source nodes correspond one-for-one to native states, or that S alone completes the above sufficient package. With only a one-node source margin, an unpriced extra row should not be proposed as an accepted <=218 machine. No such compilation or source-count claim is made here.

Current outcome: the semantic obstruction is rigorous; syntactic substitution, K/S and reverse consistency remain open. No further generic model search or formula enumeration is recommended until one of the displayed native bridge families is actually derived or a genuinely new implementation/calculus idea is specified.
