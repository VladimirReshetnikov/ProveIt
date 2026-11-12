#!/usr/bin/env python3
"""Bounded textual arity check for selected inert Lean residual vectors."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parent.parents[1]
items=[
('research/adaptive-aq17-factored94-model-draft/AQ17Factored94Residuals.lean.src',8,17),
('research/adaptive-aq20-substituted104-model-draft/AQ20Substituted104Residuals.lean.src',11,20),
('research/adaptive-aq22-quotient110-model-draft/AQ22Quotient110Residuals.lean.src',13,22),
('research/adaptive-aq26-quotient122-model-draft/AQ26Quotient122Residuals.lean.src',17,26),
('research/adaptive-qm36-conditional-model-draft/AdaptiveQM36Residuals153.lean.src',27,36),
('research/adaptive-qm36-conditional-model-draft/AdaptiveQM36Residuals155.lean.src',27,36),
('research/adaptive-qm37-conditional-model-draft/AdaptiveQM37Residuals.lean.src',28,37),
('research/adaptive-qm38-residual-evaluation-draft/AdaptiveQM38Residuals.lean.src',29,38),
]
out=[]
for f,expected,vars in items:
 b=(D/f).read_bytes();s=b.decode()
 decl=re.findall(r'def residuals \(p : Fin 4 → ℤ\) : Fin (\d+) → Expr \(Fin (\d+)\) :=',s)
 vectors=re.findall(r'^  !\[([^\n]+)\]$',s,re.M)
 assert len(decl)==len(vectors)==1,f
 arity,actualvars=map(int,decl[0]); entries=vectors[0].split(',')
 assert arity==expected==len(entries) and actualvars==vars,f
 assert all(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',x) for x in entries),f
 out.append({'path':f,'sha256':hashlib.sha256(b).hexdigest(),'declared':arity,'entries':len(entries),'variables':vars})
print(json.dumps({'scope':'bounded textual arity check, no Lean','files':out},sort_keys=True,indent=2))
