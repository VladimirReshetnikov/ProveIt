# Order-bijections preserve greatest elements

`greatestImage` proves in source natural deduction that, given explicit source equality principles and an order-bijection, the image of a greatest element is greatest. The proof uses right-totality, typing, functionality and order preservation. This is a structural lemma toward successor transport; it does not yet construct a restricted isomorphism, discharge its equality context in the source theory, or prove translated induction or an iPRA endpoint.

Run `bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-order-iso-extrema.sh "$PWD" NEW_EMPTY_OUTPUT` from the repository root. The incremental checker rebuilds the three existing formula-equality modules and this theorem against hash-pinned prebuilt dependencies, including `PA194FoundationOrdinalSuccessorClosureLinear` from `/dev/shm/pa194-ax-probe`; the complete transitive dependency closure is not rebuilt. It rejects `sorryAx`.
