# Independent ordinary proof review: RBC and RCB

Reviewer: `review_upstream_reflection`, 20 October 2026. I read the complete held `rbc-invariant.md` and independently checked every last-generator inversion against the literal native row shapes. I previously reviewed the RAB invariant and authored the separate bounded singleton-algebra search. I did not author this extension, run its schema search, or check a Lean adaptation.

Fix **one** orientation `W(b,c)=R(b,c)` or `W(b,c)=R(c,b)`. Both satisfy membership tag, `W(b,c)>c`, and `W(b,c)=F` iff `b=c=0`. Write

```text
p(b,c) = I(c,W(b,c))
H(a,b,c) = I(I(p(b,c),a), I(I(a,c),I(b,c)))
J(b,c) = I(I(p(b,c),c), I(b,c))
a(b,c,d) = W(d,p(b,c))
h(b,c,d) = I(I(a(b,c,d),c), I(b,c))
D(b,c,d) = I(I(h(b,c,d),p(b,c)), I(d,p(b,c)))
```

The auxiliary class T adds all J and D instances to the earlier MP-free generators. Both their immediate fields are I-headed. Thus they introduce no R/E-headed member, no extra way to produce a Q-headed member, and no witness of the old forbidden shapes `I(E,F)`, `I(Q NQ,F)`, or `I(V,nks)` (the latter has Q-headed right field). The original rho1–rho6/G/bundle arguments therefore survive this extension.

For an H major the required minor is `I(p(b,c),a)`. Matching its last generator gives:

| Minor generator | Consequence |
|---|---|
| Identity | `a=p(b,c)`; the H consequent is exactly J(b,c). |
| H(x,y,z) | `c=p(y,z)`, `x=W(b,c)`, `a=I(I(x,z),I(y,z))`; the consequent is exactly D(y,z,b). |
| J(y,z) | `c=p(y,z)>=z=W(b,c)>c`, impossible. |
| D(y,z,e) | `p(y,z)=W(b,c)`, an I/R collision. |
| rho6 | `W(b,c)=F`, hence c=0, but matching also makes c a positive Q code. |
| Bundle | Its Q-headed core would equal W(b,c), impossible. |
| Other generators | Wrong outer or antecedent tag. |

The H/H case is genuinely allowed. Substituting `a=W(d,p(b,c))` in H(a,b,c) makes it the exact antecedent of H(h(b,c,d),d,p(b,c)); the single MP result is D(b,c,d). The proof does not incorrectly discard this new detachment or assume that no native MPs exist.

A J major requires `I(p(b,c),c)`. Identity is excluded by p>c. An H minor forces `x=W(b,c)` and `c=I(I(x,z),I(y,z))>=x>c`. A J minor forces `z=W(b,c)` and `c=I(y,z)>=z>c`. A D minor forces its I-headed p to equal W. The rho6 and bundle cases are excluded just as above. All remaining generators have incompatible tags. Hence no J major can fire.

A D major requires `I(h,p)`, abbreviating the fixed b,c,d parameters. Identity would imply h=p, whose right-field comparison is `I(b,c)=W(b,c)`, impossible. A rho6 minor has right field p and therefore left field X(i,p); comparing X(i,p)=h forces `F=I(b,c)`. An H minor's right field equals p only if `I(y,z)=W(b,c)`. A J minor's right field forces y=c,z=W(b,c), while its left field then forces `z=I(b,c)`. A D minor's right field forces its I-headed p(y,z)=W(b,c). Each fails a tag comparison. Bundle has right field F rather than I-headed p; all other generators are excluded by antecedent tags. Hence no D major can fire.

The resulting major-premise induction establishes MP closure: H produces an admitted J or D; J and D have no available minor; the other cases are exactly the earlier proof. In the quantifier-monotonicity case the recursive call uses the strictly smaller major witness, after stripping the minor's leading Q. No general substitution, renaming, classical implication, or semantic completeness premise enters.

Zero aliases cause no omitted case. p is positive since p>=W>c, and all J/D formulas have the stated I tags even if a subsidiary I(0,0) is zero. Constructor injectivity still applies to numerical I at zero. T contains truth via the identity I(0,0), and excludes F by root residue.

The ordinary argument therefore proves consistency of each fixed RBC or RCB calculus and is formalizable in ZFC by finite witness induction. Together with the independently reviewed RAB/RBA/RAC/RCA cases, this covers all six fixed ordered distinct-input membership replacements. It does **not** cover a calculus admitting multiple orientations as a union of axiom schemes, an added K/S basis, or arbitrary code-dependent builders. No machine/runtime endpoint follows from this proof alone.

The bounded schema-search evidence in the author note is not used by this peer and was not independently replayed. Any later Lean receipt must remain separate from this ordinary proof review.
