# Code-dependent rho8: a fresh-diagonal obstruction and exact remaining gap

> Update, 2026-10-20: the fixed R(b,c) reverse-calibration lead has since closed negatively by a full-seed syntactic consistency invariant. See `UPSTREAM_FIXED_ORIENTATION_CLOSURE_REVIEW.md`. The conditional semantic theorem and earlier gap analysis below remain valid historical results; statements that full consistency was still open are superseded.

Date: 2026-10-20. Status: ordinary mathematical proof with an independent textual review and a small finite receipt. No new consistency calibration or <=218-state machine is claimed.

## 1. Exact proposal and result

The proposal T_bc keeps all K219 rows, the entire support-bearing enabled seed-K bundle, raw truth 0, MP and GEN. It replaces only unrestricted

    L(A,B,C,U) = ((C -> U) -> A) -> ((A -> C) -> (B -> C))

by

    L(A,B,C,R(b,c)),

where b and c are the actual natural-number codes of B and C, also used as variable labels. In the native codec I(a,b)=4P(a,b), R(i,j)=4P(i,j)+1, Q(i,A)=4P(i,A)+2, E(i,j)=4P(i,j)+3, with raw 0 true and F=1=R(0,0).

The strongest new result is a model-class collapse theorem: **every Heyting-valued assignment interpretation satisfying the weak locality assumptions below and validating the changed row already validates every unrestricted L instance.** Consequently this semantic class cannot supply a separating countermodel, with or without the full seed K. This does NOT establish that every consistent T_bc admits such a model.

## 2. Fresh-diagonal theorem

Let H be any Heyting algebra, with implication interpreted by its Heyting implication. Assume:

1. Native raw 0 has value top and F has value bottom.
2. Membership is irreflexive in value: r(x,x)=bottom. It is enough to require the corresponding diagonal fact at each assignment; a fixed relation across assignments is stronger than needed.
3. The permitted assignments are closed under s -> s[c:=s(0)]. For every positive native code c, this modification preserves the value of the formula decoded from c.
4. Every literal changed rho8 row is top under every permitted assignment.

Assumption 3 follows from the usual native strict support bound and standard assignment semantics: every label in the decoded positive code c is strictly below c. No quantifier law beyond this specific fresh-coordinate invariance is needed.

Fix c>0 and an assignment s, and write x for the value of decoded C. Use the single literal row whose raw parameters are a=1, b=0, and this c. Change only coordinate c to s(0). The values of A=F, B=truth and C are respectively bottom, top and x. Coordinate 0 is unchanged because c>0, and U=R(0,c) is now diagonal, hence bottom. Therefore that exact row has value

    ((x -> bottom) -> bottom)
        -> ((bottom -> x) -> (top -> x))
      = not-not x -> x.

Validity gives not-not x <= x. The reverse inequality holds in every Heyting algebra. Thus x is regular (double-negation stable). Code c=0 is separately regular because its value is top. This proves regularity for EVERY realized native formula value, including quantified formulas and arbitrary native junk codes interpreted by the native recursion.

No native proof-renaming, formula substitution, separation, or projection from the seed bundle was used. This is a semantic argument at exactly the original numeric code c, not an implicit recoding of C.

## 3. Why regular C alone validates unrestricted L

For arbitrary a,b,u in H and a regular element c, put

    d = ((c -> u) -> a) meet (a -> c).

Since not c <= c -> u, we have d meet not c <= a. Intersecting with the second factor also gives d meet not c <= c, hence d meet not c = bottom. Residuation gives d <= not-not c = c. Therefore d meet b <= c, which by repeated residuation is exactly

    L(a,b,c,u) = top.

This avoids any need to identify regular elements with the Boolean center, which would be inaccurate in general. In fact, for fixed c:

    c is regular iff L(a,b,c,u)=top for all a,b,u.

The reverse direction uses a=bottom, b=top, u=bottom. The ambient algebra need not be Boolean, and values a,b,u need not be regular for the forward implication.

Together with Section 2, this shows that the same interpretation validates every unrestricted native rho8 instance. If the interpretation also validates all the retained logical rows and full seed K, it is already a model of the original native calculus in this semantic sense. It cannot be a countermodel distinguishing the two calculi.

## 4. Concrete rejection of the earlier K/S instability model

The earlier six-element Heyting interpretation uses H={0,1,4,5,6,7}, top=7, and q(6)=4. Let

    C = Q_3(not R(1,2)), code c=11,409,850.

Under s(1)=0, s(2)=1, its value is 4 and not-not 4=6. Set s(0)=s(c)=0. The changed row at a=1,b=0 has fourth code

    R(0,c) = 260,369,422,504,101

and value 5, not designated top 7. Thus that earlier logical-fragment countermodel cannot be repurposed for T_bc. It did not validate seed K in the first place; this explicit failure is not itself a new full-K countermodel.

The independently authored check_fresh_diagonal.py reconstructs the Heyting implication operation from the upset order rather than copying the earlier table. It checks 864 instances with regular C, all six diagonal reductions, and the exact native arithmetic of this witness. See fresh_diagonal_receipt.json. This finite receipt supplements, and does not replace, Sections 2-3.

## 5. The older four-valued full-HC model fails for T_bc as well

In the older matrix the only failures of L are (A,B,C,U)=(0,3,1,2) and (1,3,1,2). Set raw a=1, b=0, c=R(2,3)=73. Then U=R(0,73). The endpoint pairs (2,3) and (0,73) are disjoint. Whenever the fixed membership relation attains both colors 1 and 2, assign these pairs independently to witnesses for those colors. The literal T_bc row is then undesignated.

Consequently a fixed-relation interpretation using that exact matrix can validate T_bc only if one of colors 1 or 2 is absent from its membership range. With its Boolean equality and Boolean designatedness quantifiers, each remaining three-element range is closed under implication and implication is material at designatedness. The old HC false-color mechanism is therefore unavailable. This is a semantic class restriction, not a completeness/model-existence theorem.

The same independent-label argument applies even if the pairs' domain values overlap; only their coordinate labels need to be disjoint. No freshness or alpha-conversion of a proof is being assumed.

## 6. Bounded exact-code-schema experiment

A freshly authored condensed-detachment experiment treated native constructors I/R/Q/E as numeric-code term functions. Schematic variables represent arbitrary natural-number inputs, not arbitrary replacements of decoded membership atoms. The exact coupled row was a schema throughout. Other seeds were truth, rho1-rho6 and merged G; GEN used a genuinely new arbitrary binder parameter. No seed-K axiom, atomic-vacuity projection, equality-reflexivity theorem, or K/S schema was silently assumed.

The unifier explicitly handles I(0,0)=0 in both directions: equating I(x,y) with raw0 imposes x=y=raw0. Positive constructors retain their distinct tags. The method is deliberately incomplete for cyclic equations involving raw0; that can miss proofs but cannot create an unsound equality.

Bounds: 1,200 stored terms, 150,000 detachment attempts, 55 constructor/leaf nodes per formula, 20 seconds. The final run stored 451 terms, made 150,000 attempts, and took about 0.46 seconds. It found none of unrestricted identity, K, explosion, Peirce, B, S, or equality reflexivity. The initial run was corrected to include bidirectional raw0-alias unification; only the corrected run is retained as the current receipt.

Files: bounded_cd_coupled.py and bounded_cd_coupled_result.json. This is a bounded negative observation about the retained logical fragment, not an impossibility theorem or an analysis of the full seed K. No received search code or target machine was executed. No heuristic search beyond these small capped passes was performed.

One actual self-detachment is possible in the bc proposal, confirming why the earlier no-first-MP rank argument for ab/ca does not apply. Put

    Cnew = Cold -> R(Bold,Cold),
    Aold = R(Bnew,Cnew),
    Anew = (Aold -> Cold) -> (Bold -> Cold).

The old L_bc axiom is exactly the antecedent of the new L_bc axiom. MP therefore gives (Anew -> Cnew) -> (Bnew -> Cnew). This is a valid schema over raw codes, but not the missing unrestricted propositional bootstrap.

## 7. What remains open and what to test next

The straightforward direction Con(ZFC) -> Con(T_bc) still follows by axiom inclusion. Neither a uniform reverse-consistency proof nor a ZFC-constructible full-seed-K countermodel was found in this lane.

The missing representation step cannot be hidden: a general Lindenbaum term structure for T_bc need not be a Heyting algebra, need not have a single designated value, and need not satisfy the required assignment locality. Deriving K/S, a suitable deduction/congruence theorem, or a justified alternative representation is still substantive work. Applying ordinary classical completeness here would be circular.

A generic finite search checking only finitely many seed instances would not resolve the requested full-K problem. A useful model search would first need a proved reduction covering the complete captured seed template, such as a finite semantic family with universal verification for every possible matrix value/function. The existing singleton three-valued/shared-quantifier search already exhausts one narrow such route. The newly proved collapse suggests prioritizing a precise syntactic bootstrap or genuinely non-Heyting/nonlocal/multi-designated semantics, rather than reusing the earlier HC or Heyting models.

The 205-source-DAG-node measurement does not imply a correct <=218-state blank-start implementation. The independent machine lane has separate startup and shared-decoder obligations.

## Sources and independent review

- Exact current proposal: research218_round2_review/inert/ZFC_218_State_Search_2026-10-20/research/membership_fourth_parameter.md and report Section 6.4.
- Exact retained native rows: research218_companion/evidence/logic/Codes230.v and latest219_baseline/k225-formal/rocq224/src/{Codes222,Thm222}.v (read as inert text).
- Earlier full-HC proof: latest219_baseline/reports/140-k219-res-theory-restricted_rho8_strong_countermodel.md.
- Earlier six-element model: research218_junk/KS_RHO6_LOGIC_COUNTERMODEL.md.
- Current upstream conditional single-designated fresh-label result for the ab proposal: https://github.com/VladimirReshetnikov/ProveIt/blob/f8ec6158f3bdc885139ee395ae34fe44c3251b9f/Computability/BusyBeaver/Research/ZFC/k219-fourth-parameter/fresh-label.md . Its model-existence gap is distinct and remains open; the present Heyting theorem does not assume its Boolean-negation condition.
- Independent textual reviewer verify_fresh_diagonal_lemma confirmed Sections 2-3, the assignment-closure qualification, and the sharper claim that regularity of C alone suffices. This is not a Lean/Rocq compilation.
