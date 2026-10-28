from pathlib import Path
p=Path('/home/codex/.codex/worktrees/46be/Proofs/Logic/Interpretability/ZFCinPA/Lean/ZFCinPA/ValidatorSeedGuardedComprehension222.lean')
s=p.read_text()
a='simpa [irreflexiveSentence,memTerm,FirstOrder.Semiformula.quote_def,\n      Matrix.vecHead,Matrix.vecTail] using h'
b='simpa [irreflexiveSentence,FirstOrder.Semiformula.Operator.mem_def,\n      memTerm,FirstOrder.Semiformula.quote_def,Matrix.vecHead,Matrix.vecTail] using h'
assert a in s;s=s.replace(a,b,1)
a="cl_prover [hc',hb,ht',hs]";b="cl_prover 96 [hc',hb,ht',hs]"
assert a in s;s=s.replace(a,b,1)
p.write_text(s)
