From Coq Require Import Extraction ExtrOcamlBasic ExtrOcamlNatInt.
Require ConcretePrefixCredit.
Extraction Language OCaml.
Extraction "codec.ml"
  ConcretePrefixCredit.ConcretePrefixCredit.word
  ConcretePrefixCredit.ConcretePrefixCredit.raw.
