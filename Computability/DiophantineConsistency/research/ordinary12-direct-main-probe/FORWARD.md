# Positive forward witness map

`DirectMainForward.lean` proves in every IΣ₁ model, for arbitrary natural ports, that replacing the XQ91 input at index 11 by `gamma+w` gives an evaluation of the direct draft whose output is zero exactly when the original XQ91 output is zero. The transformed valuation remains strictly positive whenever the original valuation is. Therefore existence of a positive XQ91 zero implies existence of a positive direct-draft zero.

The equivalence in this theorem is only at valuations in the image of that explicit transformation. It is not a reverse existence implication for arbitrary direct-draft zeros. No model-to-halt equivalence or internal iPRA proof-existence theorem is claimed here.

`run-forward.py` produced `observations/forward-attempt01/` with exit 0 and no reported warnings. Source SHA-256 is `de770e415209f42b1d0222a8e41edb573efe86cf0884ee88b786a6f536f6c491` and output object is `46ace173cb7c23931d94b46fbf829ae86b69e16242d6ca88363000151be7e8fd`; all three theorem axiom reports list `propext`, `Classical.choice`, and `Quot.sound`. The draft graph and XQ91 objects and selected 1,291-object union were pinned and rechecked. Package, dynamic, and source-to-object ancestry are inherited rather than fully rebuilt. Resource samples and exact pins are in the receipt; temporary paths may disappear.
