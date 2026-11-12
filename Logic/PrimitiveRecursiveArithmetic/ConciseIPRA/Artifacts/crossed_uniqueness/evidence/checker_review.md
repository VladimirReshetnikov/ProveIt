# Independent review of the crossed-uniqueness reference checker

Review completed 12 November 2026 by a separate same-run analysis agent. This is a code and mathematical-specification review, not a proof-assistant verification.

Reviewed source SHA-256:

- uniqueness_checker.py: ac328f7267ccea4875a8aa13a5317006bbbcab0db362da4eea053d4aa4e7f301
- build_certificates.py: 9acbd37e2caf3a67cab1b1e0e320901e33bc1a3234a25534ed6add4f74d86943
- verify.py at review: 1dadeac9f2aab06be977bd6605af1fedbb659b42960cdcb10d906251e495f178

## Findings

No concrete soundness defect was found. The inferred proof forms match exactly Hyp, Ref, QE, DE, DI-by-cases, and arbitrary-seed crossed uniqueness U.

1. **DE opening.** A D matrix has local y at index 0 and x at index 1. Opening adds one fresh outer variable b. Q(matrix) then binds y at index 0 and reads the previous x index as the newly free b under Q, while all older numerical parameters retain their correct positions. Context formulas are lifted. The normalized exported formula is checked not to contain b, including occurrences underneath term/formula binders, before b is removed.

2. **DI opening.** The base simultaneously substitutes y=0 and x=t. For the successor branch the checker first raises passive parameters past a new z, keeping the two matrix coordinates in place, and then opens y=S z and x=t lifted under z. The branch context contains exactly the lifted old context plus B(t,0). The witness t cannot mention the freshly created z.

3. **U opening.** f and h each have one template variable at index 0. The checker raises only their passive parameters before opening them in the recurrence scope. Thus f(S z) and h(f(z)) use a common newly created z, while h's independent outer parameters cannot refer to it. Neither seed a nor target n can refer to z. The recurrence branch receives only the lifted retained context, with no induction hypothesis.

4. **Normalization.** The trusted normalizer unfolds exactly the zero and successor equations of scalar iteration, with capture-avoiding de Bruijn substitution. It also normalizes underneath term and formula binders. Canonical term comparison introduces definitional computation only, not arbitrary arithmetic equality. Inputs need not already be normal, because goals, contexts, rule instances, and inferred conclusions are normalized by the checker.

5. **Input boundary.** The parser accepts precisely the documented constructors and scopes. Variables are exact Python ints, excluding bool. Negative or out-of-scope numerical variables and hypothesis indexes are rejected. The outer record has the four required keys exactly. Malformed proof tags, wrong field counts, and bad base/step premises do not reach acceptance.

6. **Certificates.** The common-source joining certificate expands its numerical case argument through DI, DE, and QE. There is no hidden case primitive in the checker. Equality symmetry/congruence/transitivity are certificates built from U and the stated logical primitives. Their success demonstrates nontrivial local rule use; it does not verify the full scalar UR-to-iPRA bootstrap.

## Metric clarification

The initial verify.py removed docstrings before ast.unparse and reported 1909 tokens, 2087 AST nodes, 5618 normalized bytes. The original documented checker under ast.unparse preserving docstrings measures 1914 tokens, 2097 AST nodes, 6686 normalized bytes. The author was asked to ship the exact docstring-free normalized executable as a separate artifact and associate the smaller figure with that artifact, or else explicitly disclose the stripping. Both counts are far larger than the inspected compact envelope, so this issue does not change the conclusion that no size record has been established.

## Substitution stability

The mathematical claim of direct substitution stability is correct on the computation-normal quotient. All rule templates are stable under capture-avoiding substitution; no syntactic matrix/witness test changes mode. After eigenparameter freshening, the only extra step is normalization coherence:

  nf(nf(t)[sigma]) = nf(t[sigma]).

The implementation's de Bruijn shifts encode the required freshening discipline. This remains a written argument, not an executable proof of the metatheorem.

