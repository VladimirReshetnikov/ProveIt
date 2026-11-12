# Audit of the current incoming frontier

Snapshot: 831081033253cca2115196cf86bb99c77ed2aeae.
All five copied ZIP archives were authenticated against their exact Git blob SHA-1.

## What is already present

- `ipra_clausal_canonical.zip`: five patterns on canonical successor-seeded R terms and Eq/D formulas: successor computation, one-term crossed transport, clause use, D elimination, witness-directed D introduction. Q is a dummy-witness D macro; ordinary assumptions are constant clauses with a provable neutral antecedent. Complete matched checker 3305 bytes / 946 tokens / 1072 AST, versus matched control 3820 / 1107 / 1266. The 516-byte compact profile is explicitly not beaten.
- `ipra_raw_clausal_2026-11-11.zip`: five patterns on raw 0,S,I terms and Eq/D: Refl, three-branch Eval, clause use, D elimination, witness-directed DI. Complete checker 3046 bytes / 853 tokens / 993 AST; matched canonical control 3175 / 903 / 1035. Exact effective proof translations both ways, whole domains, actual equality, identity numerical composites. The central ideas Refl/Eval and clauses are acknowledged as inherited.
- `ipra_equality_from_iteration_2026-11-11.zip`: deletes the root branch of Eval using zero-evaluation twice on identity frame W(s)=I(0,s;u.0). Raw checker 2996 bytes / 954 tokens / 1019 AST vs 3039 / 959 / 1026. Also gives zero-normal arithmetic basis Refl plus one successor-evaluation schema; total six displayed rules with Hyp,QE,DE,DI. Companion checker 3011 bytes / 979 tokens / 1047 AST. Thus one-case Eval on zero-normal terms is already established.
- `ipra_reflexive_base.zip`: introduction mode selected by whether the instantiated zero base is literally reflexive. Six rules on zero-normal language; seven on raw language with asymmetric selector gate. Crucially it proves all cases and substitution admissibility even when a nonreflexive base becomes reflexive. Exact-0=0 base guard and pre-witness variants also already discussed. Checker 3084 bytes vs 3095 (same 1013 tokens). No global minimum.
- `ipra_scalar_uniqueness.zip`: fully proves scalar recursion uniqueness UR equivalent to equation induction over I0,IS, coverage,separation, first-order intuitionistic equality logic. UR has single premise f(Sz)=h(f(z)), conclusion f(t)=I(t,f(0);u.h). It constructs predecessor and actual equality reflection before recovering EI; no general recursion compiler assumed circularly. Native checker 3393 bytes vs 3322 EI control; mathematics established but simplicity criterion unmet. Separate 866-byte unchanged-calculus scope refactor is not a UR implementation.

## Explicit no-repeat warnings

1. Removing Q via clauses is already done, including the assumption/closure-use merger and both round trips.
2. Deleting Eval root composition, or zero-normalizing to one successor Eval, is already done.
3. Replacing witness-zero DI by reflexive-base selection, including its raw version, is already done.
4. The raw-clausal report proves no finite set of closed true equality seeds replaces Refl with Eval/U/E/I fixed. Interpret atom s=t as actual equality at a value in finite A; all rules preserve truth and unseen-numeral reflexivity fails.
5. A permanent universal reflexivity clause plus 0=0 merely relocates the universal axiom; four remaining rule tags are not four-pattern mathematics.
6. Removing final canonical computation axiom with nothing replacing it fails the all-equations-false countervaluation.
7. Raw-clausal proves successor rigidity SR0 implies contextual zero-equation induction, but explicitly leaves full scalar equality reflection unresolved. Do not silently import unrestricted uniqueness's predecessor bootstrap into SR0.

## Remaining identifiable frontier

The only clear mathematical gap explicitly retained is full iPRA from SR0: from f(0)=0 and f(Sz)=S(f(z)), infer f(t)=t. This narrower principle gives q(n)=0 induction by a reset-trajectory construction. Existing predecessor proofs use unbounded equalities of trajectories with updates other than successor; their use here would be circular. A successful reduction needs either a new actual-equality test derived from SR0, or a new proof of the needed unbounded recurrences under SR0.

A composition of the existing clause calculus with the reduced arithmetic Eval would be a valid new complete combination but should be labeled that precisely, with a matched checker comparison; it is not a novel mathematical deletion on its own.
