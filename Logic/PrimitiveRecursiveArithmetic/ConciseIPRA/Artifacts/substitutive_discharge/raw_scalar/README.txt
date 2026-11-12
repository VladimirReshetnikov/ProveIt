RAW CONTEXTUAL WITNESS DISCHARGE -- SUPPORTING EXPERIMENT

This directory supplies a fully validated standalone checker on RAW scalar
iterator terms, a matched separate-rule control, proof constructors and
finite exact-goal certificate translations. There is no normalization.

Inference families:
  c: the two iterator computation equations (zero / successor counter).
  u: use a retained unary-premise clause [A; y.B(y)].
  i: the inherited witness-directed introduction of D.
  e: contextual witness discharge: open D B at fresh b, prove s=t and H(s)
     in that scope, export H(t) provided b is absent from the exported goal.

The template H has a separate distinguished variable. Its passive variables
may include b, as may s and t. The result alone must be in the outer scope.
No equality, reflexivity, induction, structural or logical rule is implicit.
An ordinary formula assumption F is the clause [H0; v.F], where v is unused
and H0 is I(0,0;u.0)=0, one fixed instance of the computation schema.

BOOTSTRAP
H0 is a computation theorem. D_{x,y}H0 is introduced at witness S0, ignoring
its local hypothesis. This trivial D major embeds any full formula transport
into e. Given I(0,t;u.0)=t, transporting that equation along itself with
H(v)=(v=t) derives t=t. Ordinary D-elimination is e with a constant template
and the equality H0. Thus neither a reflexivity axiom nor normalization is
needed. These are written proof transformations, not a new Lean verification.

EXACT COMPARISON (CPython 3.12.14; docstring removed; ast.unparse + LF)
                         Bytes Tokens AST Gzip9
New raw checker           2550   744  828   949
Matched separate control  2606   756  837   958
Historical raw CE5        3046   853  993   990
Incoming fullnormal Name  2273   732  813   903

The isolated fusion saves 56 bytes, 12 tokens, 9 AST nodes and 9 gzip bytes.
The raw checker improves the historical raw CE5 source but does NOT beat the
incoming full-normalized witness-discharge checker in these size coordinates.
Its concrete tradeoff is structural primitive-recursive certificate checking
without a total uniform normalization procedure or an added fuel parameter.
No absolute minimality or global source-size-record claim is made.

FILES
checker.py           Complete new standalone verifier.
control_separate.py  Identical architecture with separate e and t families.
proofs.py            Untrusted constructors; including used equation induction.
translate.py         Both-direction exact-goal translations for the control;
                     forward translations from the frozen CE5 checker.
reference_ce5.py     Frozen upstream comparison source (MIT-0 upstream).
verify.py            Positive/negative/open-sequent/translation/CLI checks.
examples/            Generated closed positive certificates.
verification.json    Executed test and source-measurement results.

REPRODUCE
  python3 verify.py
  python3 checker.py < examples/equation_induction_uses_hypothesis.json

PROVENANCE
reference_ce5.py is unchanged from:
  VladimirReshetnikov/ProveIt, commit
  17898ea7e6a1300dfdcad71040d5daeed67916d4,
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/raw_clausal/code/clausal_eval.py
The shared traversal/checking architecture adapts the incoming package
ipra_witness_discharge_2026-11-11, code/checker.py, from the same inspected
repository snapshot. Its full normalization has been removed; clauses have
unary antecedents; the computation and generalized template-Open rules are new
to this experiment. The companion main report owns the overall claim scope.
