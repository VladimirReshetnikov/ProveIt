# Simultaneous formula / variable-label recoding

This folder contains a calculus-level proof idea and exact executable
constructor definitions. It does not contain a smaller Turing machine.

The proposed constructor partition is I=2*pair, M=6*pair+1,
U=6*pair(body,binder)+3, E=6*pair+5. Recode every natural number recursively,
including variable labels. This keeps a gate's property code and binder
synchronized and fixes both the truth alias0 and false code1. The recoding is
a bijection but not monotone, so restricted propositional rows must first be
replaced by their derived unrestricted-schema proofs.

Run `python3 recoding.py` for finite transcription controls. Read
`recoding.tex` for the general induction argument, proof-transport scope,
and physical implementation obligations. The script uses only Python's
standard library.
