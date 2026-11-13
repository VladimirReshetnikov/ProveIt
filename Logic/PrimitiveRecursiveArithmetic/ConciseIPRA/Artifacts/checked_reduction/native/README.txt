Eager opening and an empty administrative premise for native iPRA
================================================================

The complete standalone strict checkers exhibit:

  code/checker_tokens315.py    315 tokens / 365 AST nodes / 618 bytes
  code/checker_ast353.py       323 tokens / 353 AST nodes / 630 bytes
  code/checker_bytes589.py     324 tokens / 367 AST nodes / 589 bytes

The coordinate envelope is 315 / 353 / 589, versus the pinned strict
317 / 356 / 597. Different programs attain the coordinates. The public
native Eq/D grammar and whole-input exact integer/list validation are
preserved; the administrative neutral major uses [] instead of 0.

This combines known semantic constructions. It deletes no arithmetic axiom
and does not claim a universal lower bound or a breakthrough in the theory.
The compact promised-grammar family is a different, smaller comparison class.
See PROOF.txt for the semantic proof and the limits of the comparison.

Quick reproduction:
  python3 code/checker_bytes589.py < examples/zero_computation.json
  python3 code/readable_checker.py < examples/zero_computation.json
  python3 measure.py
  python3 verify.py

The byte checker takes a JSON stack ending in the public goal. Each earlier
consumed packet is [source, seed, template, major]. The token and AST checkers
use the existing supply packets [major, source, seed_or_mode, template].
Packets are consumed from the end. Unused prefix items are permitted, but
must obey the whole-input integer/list alphabet. ACCEPT followed by LF on
normal exit is success; exceptions reject.

To translate an existing canonical control certificate:
  python3 translate.py byte OLD.json NEW.json
or, for a token/AST supply certificate:
  python3 translate.py supply OLD.json NEW.json

Only an exact integer 0 in the major field becomes []; numerical fields,
mode markers, formulas and the goal are unchanged. The translator is for
canonical compiled certificates; arbitrary auxiliary aliases need not retain
the same acceptance behavior because eager opening validates more images.

Files:
  code/          Three selected checkers and readable byte expansion.
  controls/      Exact matched strict controls from the pinned incoming ZIP.
  fixtures/      Unmodified inherited test collections and provenance.
  evidence/      Source measurements and execution receipts.
  PROOF.txt      Soundness, grammar, phase, completeness and novelty argument.
  PROVENANCE.json, LICENSE-ProveIt.txt

The work is based on ProveIt commit
798856e4ef2d02b7f9c0f1660828c5ce58f277f2. The eager-opening lemma and empty neutral
already occur in the unified article; the new contribution is their complete
validated implementation composition with uniform zero and context phase.
