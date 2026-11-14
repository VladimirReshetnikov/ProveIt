The combined189-token logical emitter has this concrete dictionary of
concatenation cost66. This is not a66-state or195-state machine.

The dictionary was obtained from a60-second mixed-integer search; the
incumbent objective was65.99999999999929 and the reported lower bound
59.60825634629345. These are results for that grammar model, not global
machine-state bounds. The retained exact witness needs no solver to verify.

Run:
  python3 combinations/joint_dictionary/check_obstruction.py

The checker reconstructs the exact macro word, recomputes its integral
cost66, and identifies a source path with at least seven consecutive zeroes
forced by the fixed dictionary. The inherited return reader allows at most
six. All associations of those fixed productions retain this obstruction.
The check therefore records why this promising source compression was not
accepted as a physical improvement. New dictionary productions or a new
reader may still work. No impossibility statement about arbitrary machines
is inferred.
