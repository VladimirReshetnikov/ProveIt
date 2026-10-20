#!/usr/bin/env python3
"""Generate the conditional-K specialization; the separate checker imports no generator."""
from pathlib import Path
import sys,json
HERE=Path(__file__).resolve().parent
from hilbert_builder import Builder,term_census
B=Builder();a,b,k='a','b','k';m=B.term('meta','m');rel=lambda x,y:B.term('Rel',x,y);eq=lambda x,y:B.term('Eq',x,y)
r=rel(b,k);subset=B.Q(k,B.I(rel(k,a),rel(k,b)))
request=B.Q(b,B.I(m,B.Ex(b,B.And(m,r))))
support=B.Ex(a,B.And(m,B.Q(a,B.I(subset,request))))
closure=B.Q(b,B.I(r,support))
core=B.I(m,B.Ex(k,B.And(r,closure)))
vr=B.I(rel(a,b),B.Q(k,rel(a,b)));ve=B.I(eq(a,b),B.Q('kappa',eq(a,b)))
old=B.And(core,B.And(vr,ve))
Wf=B.Q(b,B.I(m,B.N(B.Q(b,B.I(m,B.N(r))))))
Uf=B.Q(a,B.I(subset,Wf));Hf=B.Q(b,B.I(r,B.N(B.Q(a,B.I(m,B.N(Uf))))))
Kf=B.I(m,B.N(B.Q(k,B.I(r,B.N(Hf)))))
target=B.N(B.I(Kf,B.I(vr,B.N(ve))))
_,normalized,pf,pb=B.normalize(old);assert normalized==target
cert=B.export((pf,pb),old,target);cert.update(equality_binder='kappa',core='conditional',old_census=term_census(B,old),new_census=term_census(B,target))
(HERE/'conditional_fusion_certificate.json').write_text(json.dumps(cert,separators=(',',':'))+'\n')
print(json.dumps(dict(closed_proof_nodes=len(cert['proofs']),formula_dag_nodes=len(cert['terms']),old=cert['old_census'],new=cert['new_census']),indent=2))
