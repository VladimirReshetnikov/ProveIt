Nested binary constructor encoding: research proposal
====================================================

This folder documents a possible future encoding of the same proof calculus.
It is not the encoding used by the accepted PA194QNS and PA194QS machines.
Those machines retain the supplied radix-four formula constructors.

nested_binary_code.tex defines the proposed constructors, proves their total
decoding and bijective recoding with the existing language, and explains the
required proof translation for the dominated implication schema. The proof
uses syntactic recoding and the existing unrestricted-schema derivation;
it does not assume that the recoding preserves the numerical order of codes.

nested_binary_code.py and its receipt provide bounded arithmetic diagnostics.
These support the coding calculations; the all-natural claims are the
mathematical arguments in the TeX document, not inferences from the tests.

The grammar-search score of 74 is not a verified effective-reader count or
a machine-state count. It includes four scanner penalties and eleven nominal
folds that were not jointly certified at that endpoint. No 203-state or
207-state machine was accepted from this experiment, and it produced no
verified 193-state or 194-state candidate. The theoretical fixed-control
budget is 133; under that accounting, a 193-state construction would need a
compatible effective reader cost of at most 60. The search gives no lower
bound and does not rule out a better organization of this encoding.
