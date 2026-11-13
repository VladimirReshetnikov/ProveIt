ATTRIBUTED REFERENCE MATERIAL

All inherited source is from VladimirReshetnikov/ProveIt under its MIT-0
license. Snapshot:6c6a164d211f0af34e913d55c9f46f8ef7cb560f.

upstream_base.tex is the current complete base-theory chapter:
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/docs/Article/chapters/ch01_base.tex
Git blob346086e60b963ccb65ee01b529e13a011f9f9549.

ch11_cert.tex is the current complete checker chapter at the same path prefix.
Git blobf94df2c8fbe8ca909c953a2c3009e9eb983200a1.

upstream_preamble.tex is the article preamble, supplied to make its custom
notation inspectable. These chapter sources are not standalone build targets;
the new report's main TeX file is standalone and contains its own proofs.

NativeBiInterpretation.lean is the exact current
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/
NativeBiInterpretation.lean. It identifies the inherited kernel theorems.
The imported dependency tree is not included or newly compiled. This file
does not verify the raw Python checker or the new shifted-codec theorem.

control_tokens243.py and control_ast264.py are the exact current compact
coordinate controls from the incoming computation_leaves archive. They
read line-delimited JSON, unlike the stack reader of offset472.py. Their
metrics are included to avoid falsely claiming a joint record.

These files are not uncounted executable dependencies of offset472.py.
