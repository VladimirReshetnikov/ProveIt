OPAQUE STRUCTURAL PARAMETERS: EXECUTABLE VALIDATION

Run: python3 verify.py

checker_opaque_stream.py is the exact standalone checker tested here.
controls/checker_tokens239.py is the pinned upstream standalone control.
translate.py is untrusted test-fixture tooling. It runs the old and new
protocols together, translates free scalar parameters into opaque tokens,
and refuses unsupported source cases. It is not a universal compiler for
arbitrary raw certificates and is not imported by either checker.

All generated certificates have exact integer/list input, including labels
inside opaque names. Runtime Boolean zero aliases are normalized to integer
zero when writing those labels; Python compares the resulting trees equally.

The eight positive fixtures include ordinary computations, equality
elimination, a compound implication proof, and guarded equation induction
whose induction hypothesis is used. quantified_reflexivity.jsonl is a new
five-packet hand-written source proof, translated into the new protocol:

  D_{x,y}(I(y,0;u.0) = I(y,0;u.0)).

This is a canonical CLOSED PUBLIC GUARDED formula; x is unused. The proof
uses a fresh parameter in later packets, so it exercises name compilation.

negative/fixed_name_capture.jsonl is a specific eigenvariable-capture attack
against the false canonical public formula

  D_{x,y}(I(y,0;u.x) = I(y,0;u.y)).

Its ordinary reading forces x=1 and x=2. The correct checker rejects it.
negative/deliberately_unsound_fixed_name.py changes the eigenname to the
fixed token [0,0,0,0] and ACCEPTS this false formula. That program is only
a negative control; never use it as a proof checker. The attack chooses
the witness S(F), where F is the fixed eigenname. The purported successor
case then collapses to reflexivity because the witness captures the case
variable. A structurally fresh token prevents that collapse.

Every CLI check runs in a separate Python process, both normally and with
-O. False-root mutations and inherited false-goal/capture/context attacks
are included. Parameter fixed-point checks range across positive and negative
depths and apparent exposed-slot labels.

The receipt records exact source hashes, measured sizes, translation traces,
and each executable outcome. These finite checks support the written
soundness and completeness argument; they do not replace it. No end-to-end
Lean or Rocq verification of this Python checker is asserted.

Inherited control and seven fixtures originate in
VladimirReshetnikov/ProveIt at
fc05b10f0e03f22edbfdde9298a29fb2fee5dc59,
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Artifacts/
fused_blocks_and_checkers/checkers/.
