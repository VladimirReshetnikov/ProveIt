ZERO-NORMAL CLAUSAL iPRA: ONE ARITHMETIC EVALUATION SCHEMA

Status: a completed composition of existing mathematical reductions, with
a complete standalone verifier and an executed raw-to-canonical proof
compiler. It is a companion, not the recommended checker-size result.

Complete checker sizes, using ast.unparse and CPython 3.12.14:

                              bytes  tokens  AST nodes
Raw current CE5                 3046     853        993
Canonical with root retained    3107     879       1023
Canonical successor Eval only   3050     871       1011

The 2999-byte root-deleted RAW checker in the main construction remains
smaller. Canonical syntax reduces the arithmetic rule interface, but its
normalizing substitution has a measured cost. No global record is claimed.

Primitive data:
  - Terms x, 0, S(t), I(n,a;u.h), with I nodes forbidden at literal n=0.
  - Formulas s=t and D_{x,y}B only.
  - Context clauses [A; y.B], read as A -> forall y B.
  - Five instruction patterns: U, Refl, UE, E, I.

The only arithmetic inference apart from Refl is

        smartI(c,a;h)=t      I(S c,a;h)=r
        ---------------------------------
                    r = h<t/u>

where smartI(0,a;h)=a and h<t/u> is substitution followed by
zero-normalization. No zero-evaluation or root-equality branch remains.
All logical clauses use the inherited raw-clausal interface, with
normalized substitution. The introduction mode is progress iff its
matrix has equation root and its supplied canonical witness is literal 0.

FILES
  code/canonical.py          Complete standalone proposed checker.
  code/canonical_control.py  Same grammar plus direct root equality.
  ../code/baseline.py        Exact current raw CE5 checker.
  code/canonical_translation.py
                            Untrusted raw -> canonical proof compiler.
  proof.txt                 Equivalence argument and exact boundaries.
  evidence/verification.json
                            Executed checks, not proof-assistant verification.
  examples/                 Raw/canonical certificate pairs.

EXECUTED VERIFICATION
  33 accepted translated source certificates, including all 32 inherited
  positive certificates and an additional case whose witness normalizes
  to zero and therefore requires an actual mode repair;
  28 rejected certificates;
  244 public CLI runs (original and normalized verifier, Python with and
  without -O). Inherited test generation additionally ran its own checks.

The forward compiler is complete for the displayed raw CE5 proof format.
It handles the subtle witness-mode change by choosing the canonical alias
Z=I(S0,0;u.0), transporting the local equation assumption from Z to 0,
replacing uses of the affected ordinary clause, then transporting the
successor conclusion from 0 back to Z. It does NOT blindly normalize a
witness and assume the same introduction mode survives.

The reverse mathematical translation is established by the inherited
normalization equivalence, with both formula composites. A reverse
canonical-to-raw certificate compiler has not been implemented here.
Do not describe the Python evidence as bidirectional proof compilation.

REPRODUCTION
  python3 reproduce.py

The reproduction script reads the unchanged inherited corpus from
../baseline/ipra_raw_clausal and the exact raw verifier from
../code/baseline.py. The proposed standalone verifier itself has no
imports from the other artifacts.

SOURCES
  ProveIt snapshot 831081033253cca2115196cf86bb99c77ed2aeae.
  docs/incoming/ipra_raw_clausal_2026-11-11.zip supplies the clause interface.
  docs/incoming/ipra_equality_from_iteration_2026-11-11.zip supplies the
  single-successor arithmetic rule and normalization equivalence.
  Research/zero_normal and Lean/ConciseIPRA/ZeroNormalization.lean supply
  the inherited normalization laws. This composition adds neither a new
  arithmetic principle nor a new claim of proof-assistant verification.
