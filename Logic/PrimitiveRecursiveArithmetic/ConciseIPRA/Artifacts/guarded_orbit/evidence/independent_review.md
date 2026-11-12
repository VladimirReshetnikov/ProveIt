# Independent mathematical and comparison review

Reviewed in full:

- `agent_math/orbit_bootstrap.tex`
- `agent_math/inventory_and_composites.tex`
- `candidates/combined_metrics.json`
- `candidates/combined_strict_metrics.json`

## Assessment

The orbit bootstrap establishes the claimed equivalence on the existing guarded public Eq/D language, provided the proof language allows unguarded administrative orbit formulas. The proof is a new composition theorem. It is not the naive combination of two admissibility theorems, and it does not prove completeness for every unrestricted administrative formula. I found no mathematical gap in the main construction after the qualifications and small clarifications below.

This is an independent review in the same research run, not proof-assistant verification or external peer review.

## Checked dependencies

### 1. Why canonical-only composition fails

The regular/zero-left invariant is valid for the strictly guarded clause calculus. The restriction s != literal 0 forces a regular transport conclusion to have regular major and minor premises. The computation axioms are regular; guarded atomic D rules use regular endpoint formulas; compound D rules use compound formulas. A constant clause with consequent 0=x cannot contribute to a regular proof. Thus erasing this assumption would turn a hypothetical proof of x=0 into an unconditional false standard-model theorem. Orbit elimination deliberately breaks this invariant by providing a clause whose zero antecedent is zero-left and whose successor consequent is regular.

### 2. Safe equality

Reflexivity uses the iterator-headed source W(r) twice, so it also works when r is literal zero. Restricted symmetry needs only the original source nonzero; its resulting left endpoint may be zero, but the proof never silently uses such a result as an admissible transport major. Transitivity is used only through a syntactically nonzero middle until zeroJoin and zeroSym are available.

The zeroJoin derivation is correct. For p=0 with p nonzero syntax, it first obtains p=W(0), with all active sources p, W(p), or W(0). Joining p and q then uses the nonzero middle W(0). No induction, numerical cases, or forbidden zero-source conversion occurs.

### 3. Stable-left numerical cases

Padding E by D G(E) is available before full transport when E's left term is nonzero syntax. Restricting the case template's left term to outer I or S makes all its zero and successor instances nonzero syntax. This gives exactly the restricted cases principle used for the singleton tests.

The proof does not perform numerical cases under an assumption depending on the case eigenvariable. The two branch derivations are made under their common independent retained context, then padded and combined by compound D case introduction. Each newly introduced padding counter is fresh for the equation being padded.

### 4. Singleton tests and the reversed filter

All case templates actually used have I-headed left sides: H(v)=S K(v), L1(Sv)=Z(v), and C(Z(v),v,0)=v. The successor branch joining two zeros uses zeroJoin, not unrestricted transitivity through zero.

The reversed filter is the essential orientation choice. After it is proved at a target t, reversing it is allowed because its source is a selector term, irrespective of whether t itself is zero. In the later zeroSym argument the assumption t != literal 0 is separately present before t is used as a transport source.

For maximal clarity, replace the phrase that the filter branches "contract to 0=0 / Sv=Sv" with the explicit derivable chains

    C(Z(0),0,0) = C(1,0,0) = 0,
    C(Z(Sv),Sv,0) = C(0,Sv,0) = Sv.

Each first equality is congruence at an I-headed zero-test source, and each second is a computation. This avoids suggesting that a reverse normalization from reflexivity was silently used.

### 5. Orbit and zero-source symmetry

The administrative orbit D[y=I(y,t;u.Su)] is introduced by progress at a fresh source variable z. That variable is syntactically nonzero in the actual derivation. It is never specialized to literal zero inside that derivation. DE merely uses the resulting anchored closure at the requested target, which is a legitimate distinct rule.

Under 0=t with t nonzero syntax, reversing I(0,t;u.Su)=t yields an equation with permitted source t. This makes the zero-left assumption usable as the orbit base. The specialization at 1 gives 1=St, and the singleton test plus filter gives t=0. All numerical helper lemmas can be constructed at their needed parameters, or safely substituted because their active sources have stable S/I heads. No unrestricted substitution is required before the bootstrap is complete.

### 6. Full equality and canonical binder transport

For transitivity through zero, first turn 0=q into q=0 via zeroSym, then apply zeroJoin when both exterior endpoints are nonzero; the literal-zero exterior cases reuse a premise. For congruence from 0=t, handle t=literal 0 by reflexivity, and otherwise reverse to t=0, use restricted congruence, and reverse the result. The proof text should explicitly mention that trivial case.

Transport through a canonical D is correctly split by matrix root. Compound matrices use compound case introduction and the smaller-formula equivalence. Guarded atomic matrices have a provable base, so the opened source clause produces each successor instance without using the target progress hypothesis. The target can therefore be introduced by progress. An orbit target is already a theorem, so full transport also holds in the auxiliary enlarged guarded grammar G+.

## Substitution after the bootstrap

The strategy in `inventory_and_composites.tex` is valid, with its scope kept explicit:

1. Regard the constructed mathematical derivations as proofs in G+ with ordinary clauses and **derived unrestricted transport on G+ formulas**.
2. Numerical substitution is admissible in that derived calculus because its grammar is stable under capture-free substitution and its transport rule has no source restriction.
3. Expand every substituted unrestricted-transport node back into the proved restricted derivation.

This permits the zero and successor specializations of a supplied step proof in the recovered contextual equation-induction argument. It does **not** assert that one can substitute into an arbitrary primitive U0 proof, and it does not establish substitution for all unrestricted administrative formulas. The recursive native-to-guarded translation builds its output in the G+ clause calculus, so the needed supplied step proofs meet the stated scope. Mentioning that scope at the point where equation induction is reused prevents an apparent circularity.

## Exact relationship to the current Eq/Q/D kernel

The explicit translation in the second fragment is correct:

    T(s=t) = s=t,
    T(Q_y B) = D_{r,y} P(TB), with r fresh and unused,
    T(D_{x,y} B) = D_{x,y} P(TB),

where P sends an equation E to the compound padding L(E), and fixes a compound guarded formula. All output D matrices are compound.

The translated QE rule opens the dummy-witness D, pads its base, applies the clause, and unpads. In translated DE, the opened clause constructs exactly the formula T(Q B(b,-)) expected by the recursively translated minor; cutting that formula is legitimate. Translated direct Q progress uses the recovered contextual equation-induction macro under the padded base, then compound-case introduction.

The native composite A <-> JT(A) uses padding, ordinary binder congruence, and Q B <-> D_dummy B in the current kernel. The guarded composite B <-> TJ(B) uses compound binder congruence, with the guarded atomic case D E <-> D L(E) relying explicitly on the true base. These arguments are uniform in parameters and retained contexts and therefore preserve full consequence, not merely theoremhood.

The inclusion in the other direction is even simpler than mixed-model soundness: every administrative rule is a primitive or derived rule of the current native kernel under the **ordinary anchored D reading**. Arbitrary formula transport is `NPrf.tr`; witnessed atomic progress is `NPrf.dIProg`; compound case introduction, QE, DE, hypothesis, and computation already exist. This gives direct syntactic soundness. The mixed progressive interpretation is optional evidence that arbitrary noncanonical administrative formulas need not have the same consequence relation; it is not needed for the main conservativity proof.

## Size claims checked

The measured candidate profiles are:

| Profile | Tokens | AST nodes | Normalized bytes | gzip-9 |
|---|---:|---:|---:|---:|
| AST | 262 | 281 | 606 | 348 |
| bytes | 265 | 303 | 525 | 331 |
| tokens | 258 | 287 | 571 | 339 |

The envelope 258 / 281 / 525 is attained by **three different programs**. Against the inspected old envelope 259 / 283 / 526, this improves one token, two AST nodes, and one normalized byte. It is a modest frontier improvement under the existing canonical-input checking contract. It is not one simultaneous 258-token, 281-node, 525-byte checker.

The explicit guarded public-goal validator gives 1,205 bytes / 491 tokens / 563 nodes / gzip 572, compared with 1,208 / 491 / 568 / 574 for the previous **same guarded goal grammar**. That is a valid small improvement. The older scalar core with its different explicit public-goal grammar is 1,109 bytes / 450 tokens / 521 nodes / gzip 538. Therefore the new strict program is not a global strict-checker size record. Do not describe the 525-byte program as a self-validating parser for the guarded public language, or hide the strict parser's cost.

The measurements use CPython 3.12.14 and charge each complete selected module. Gzip-9 is informational and should remain separate from the minimized coordinates.

## Required presentation boundaries

- State that the new theorem is written mathematics and has not been checked in Lean/Rocq.
- State the public grammar and the permissive intermediate proof grammar separately, because the orbit formula is the reason the composition succeeds.
- Claim exact equivalence on canonical guarded end sequents only.
- Keep the current native kernel and the two pre-existing reductions explicitly attributed; the new contribution is their nontrivial composition using the administrative orbit bridge.
- Give the byte/token/AST changes as the measured small improvement, without claiming absolute simplestness or a substantial arithmetic breakthrough.
