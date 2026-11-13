# Independent audit: equation-only Back at the newest parameter

## Verdict and scope

The proposed answer to `ch07_wit.tex`, question `wit:q:ab-back`, is mathematically sound on the stated raw syntax, subject to the definitions below. I checked it against the exact pinned repository `798856e4ef2d02b7f9c0f1660828c5ce58f277f2`. The new result restricts Back to literal equations while keeping the newest-parameter restrictions of Use and Close. It does not remove the generic substitution operation required by Alias and by clause instantiation, and by itself it establishes no checker-size improvement.

Call the restricted calculus E_nu. It has exactly A_nu's rules, except that the conclusion F of Back must be a literal equation. It is plainly a subcalculus of A_star, and therefore sound under the inherited ordinary reading. The useful claim is equivalence on all scoped judgments, not merely on closed public formulas.

## Persistent families

Keep the article's worlds w=(Pi;Gamma) and append-only extension relation. A persistent family w |= A is an effective constructor of a derivation of A at every extension of w. A persistent realizer of [A;y.B] takes an extension, an arbitrary term r there, and a persistent family of A, and returns a persistent family of B(r). These are metatheoretic proof constructors; they add no logical rules or trusted oracle.

### Preliminaries requiring no compound Back

1. Any literal context clause has a persistent realizer. At an arbitrary extension, append a fresh c=r. The antecedent family supplies A. Because c is newest, Use gives B(c). Alias discharges c=r and produces B(r). With an empty antecedent omit the premise. This construction can be rerun at every later extension.
2. Reflexivity t=t is persistent: append c=t, use that assumption, and Alias-export it.
3. Atomic backward transport: persistent s=t and E(t), for an equation template E(v), give persistent E(s). At a chosen extension append c=s. Use yields c=s. A first equation-only Back, with conclusion c=t and minor s=t, yields c=t. A second equation-only Back, with conclusion E(c) and minor E(t), gives E(c). Alias yields E(s). Freshness ensures all displayed substitution identities hold literally, even if the original t contains variables occurring in s.
4. Symmetry and forward atomic transport follow from 2 and 3. Symmetry uses the equation template t=v, with known t=t, to obtain t=s.
5. Every diagonal zero row is persistently derivable. If M(x,y) is literally I(y,y;u.h)=I(y,y;v.k), then M(b,0) is I(0,0;u.h')=I(0,0;v.k'). Each endpoint is equal to 0 by I0; atomic equality gives their equality. This is a family because the construction is repeated at each extension. No IS, induction, coverage, or compound Back occurs here.

## Full persistent transport by formula-depth induction

Prove the following once, before compiling source derivations:

If w |= s=t and w |= H(t), then w |= H(s), for every Eq/D formula template H(v).

The induction parameter is the number of D binders in H. The base is preliminary 3. Since substitution inserts numerical terms only, it never increases this parameter.

For H(v)=D_{x,y} B(v,x,y), fix an arbitrary extension w' of w. Use the member of H(t)'s family at w' as the major of Open. Open at a fresh b, giving

  w_b = (Pi_{w'},b; Gamma_{w'}, [B(t,b,0);y.B(t,b,y)]).

The goal in this branch is H(s), which does not contain b. Apply target Close at w_b. The chosen witness is exactly b because b is newest before Close. Let z be its fresh eigenvariable, and let w_z append the actual Close assumption to w_b.

We construct a persistent family of B(s,b,0) at w_z as follows.

* If the target matrix B(s,x,y) is non-diagonal, Close's assumption is precisely B(s,b,0), so preliminary 1 realizes the assumption.
* If it is diagonal, preliminary 5 supplies B(s,b,0); Close's actual progressive assumption B(s,b,z) is unused. Its presence causes no issue because all families are constructed directly in the larger world.

Restrict the persistent equality family s=t to w_z. By atomic symmetry and the induction hypothesis on the strictly smaller template B(v,b,0), transport the preceding family to B(t,b,0). The opened source clause has a persistent realizer by preliminary 1. Apply it at the arbitrary term S z to produce a persistent family of B(t,b,S z). Apply the induction hypothesis to the strictly smaller template B(v,b,S z) to get B(s,b,S z). Take its member at w_z. This is the required premise of target Close, giving H(s) at w_b. Open discharges b and yields H(s) at w'.

The construction is uniform in w', so it gives the required persistent family. The only recursive transport calls have fewer formula binders. All uses of Back are in the atomic base case and have literal-equation conclusions. Auxiliary aliases in clause realizers and in transport are discharged before returning a member at the requested world. In particular they never change which parameter Close chooses.

No comparison between the source and target syntactic modes is needed in this lemma. This observation is useful even where substitutions can change a guard's shape. Only the target's progressive zero row is used.

## Compilation of unrestricted derivations

Now repeat the article's theorem `wit:thm:ab-newest` with target E_nu instead of A_nu. The strengthened induction statement is unchanged: for every injective map theta from the source scope into a target world and every assignment of persistent realizers to the renamed source clauses, construct a persistent family of the renamed conclusion.

The cases check as follows.

* I0 and IS are copied at each world.
* Use invokes the assigned realizer at the renamed arbitrary target term.
* Back invokes the full persistent-transport lemma just proved. If the source replacement t contains its source parameter b, define H(v)=(theta F)[v/theta b]; then H(theta t)=theta(F[t/b]) still holds because substitution is simultaneous and inserted terms are not recursively substituted again.
* Alias chooses a genuinely fresh target parameter b', supplies its new equality clause with preliminary 1, invokes the induction hypothesis on the proper branch subderivation, and applies Alias. No substitution is performed on a completed target derivation; it is the primitive Alias conclusion.
* Open similarly adds the actual opened clause, realizes it by preliminary 1, invokes the branch induction hypothesis, and applies Open.
* Close aliases the source witness theta t to a fresh b. At the aliased world b is newest, so target Close chooses b. Its new eigenvariable z' is appended after b. In that branch the two actual assumptions b=theta t and theta B(b,epsilon(z')) have persistent families. Full transport gives theta B(theta t,epsilon(z')), which realizes the source assumption. The induction hypothesis on the source Close premise yields theta B(theta t,S z'); full transport returns theta B(b,S z'). Target Close and Alias finish. The diagonal mode is invariant under injective renaming of free parameters, so source and target mode agree here. Equality-transport uses inside this construction choose their own fresh aliases, each discharged before returning.

Each recursive compiler call is on a proper source subderivation. Clause realizers and the independent formula-depth transport lemma are already defined. The source Close assumption's realizer does not invoke compilation of that same Close premise. Therefore there is no circular proof-construction dependence.

At the initial world with the identity renaming, actual clauses have realizers by preliminary 1. The compiled family yields a derivation at that world. Hence A_star <= E_nu <= A_nu <= A_star.

## Consequences and limits

All scoped Eq/D sequents are equivalent. The inherited comparison with the diagonal clause calculus K, and then the native scalar core, transfers unchanged. Consequently the inherited iPRA interpretations, their full formula round trips, actual equality, whole numerical domains, and identity numerical comparison maps also transfer.

The proof is a mathematical derivation transformation, not a Lean/Rocq formalization. It answers the article's explicit open question and does not settle the requested checker-size frontier. It is stronger than a theorem stated only for persistent premises: persistence of an arbitrary E_nu derivation follows afterward by compiling it as an A_star derivation. One must not use that corollary during the proof above.

## Further audit: one-term crossed Back (XBack)

The stronger proposed restriction is also sufficient. Replace EqBack by

  b=t,  h[t/b]=r
  ---------------- XBack
        r=h

where b is the newest scope parameter, h and r are numerical terms, and t may contain b. Only h is substituted; in particular r is allowed to contain b and is left unchanged. Ordinary equality validates this rule. It has one term template in place of an equation template and reverses the resulting equation.

Here is a complete replacement for preliminary 3, checked term by term. Write the arbitrary equation template E(v) as a(v)=d(v). Given persistent s=t and a(t)=d(t), fix a target extension and append a fresh b=s. In that world:

1. Use the last clause to obtain b=s.
2. XBack with major b=s, h=b and r=t takes minor s=t and gives t=b.
3. XBack with major b=s, h=t and r=b takes minor t=b and gives b=t. The term t contains no b by freshness, so h[s/b] is literally t. Here r contains b, which is permitted.
4. XBack with major b=t, h=a(b) and r=d(t) takes minor a(t)=d(t) and gives d(t)=a(b).
5. XBack with major b=t, h=d(b) and r=a(b) takes minor d(t)=a(b) and gives a(b)=d(b). Here r again contains b and is not substituted.
6. Alias exports the last equation by b:=s, giving a(s)=d(s).

Thus four XBack applications supply full atomic transport on persistent families. Every major has the actual newest parameter b as its source. All other premises are obtained in that same world; families regenerate input derivations there. This proof needs no computation axiom, no induction, and no compound equality template as a primitive rule.

Reflexivity remains the two-step Use/Alias construction. Symmetry can either be derived from atomic transport or more directly: from s=t append b=s, perform XBack with h=b,r=t to obtain t=b, then Alias-export t=s. This uses just one XBack.

The formula-depth transport theorem and the A_star compiler above then go through with no other changes. Diagonal zero rows use I0 and the just-established atomic equality operations. Consequently the X_nu calculus, with the same newest Use and Close and with this one-term XBack, has exactly the same scoped Eq/D consequences as A_star, A_nu, and E_nu.

This establishes a stricter and more economical mathematical equality rule. Its complete-checker metric must still be measured. The rule calls numerical substitution once rather than twice in a direct EqBack checker; Alias continues to require formula substitution.
