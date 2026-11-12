#!/usr/bin/env python3
"""Independent exact toy full-graph evaluation; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return json.loads(b)
g=pin('research/ordinary13-residue-first82/candidate.json','bb90faa3815c5ff46f5fdbf41c2d001790d565baa17d97c79514c33fa928f1d2')
p=pin('research/ordinary13-qcube-unscale84/candidate.json','2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77')
r=pin('research/ordinary13-residue82-firstnorm-companion-obstruction/result.json','f9ebcb2e2cfc07cbcc1d1898c25882d9f694051412634130b07945ee528cd11c')
assert g['witnesses']==p['witnesses'] and g['fixed_numerals']==p['fixed_numerals']
q=47;beta=46;X=47;Y=q**3;m=X*Y**2;k=8*m+4;tau=8*m*m+8*m+1;ell=m*k
w={'J':1,'F':1,'alpha':45,'f':2,'i':1,'T':1,'X':X,'s':1,'r':45*k+1+tau-ell,'eta':1,'zeta':k-1,'y':1,'gamma':1}
ports={'beta':beta,'K0':0,'MC':1,'MF':1}
assert w==r['inputs'] and ports==r['ports'] and all(w[x]>0 for x in g['witnesses'])
def evaluate(graph):
 env={**ports,**w}
 for name,op,a,b in graph['source']:
  av=a if type(a) is int else env[a];bv=b if type(b) is int else env[b]
  if op=='+':env[name]=av+bv
  elif op=='-':env[name]=av-bv
  else:assert op=='*';env[name]=av*bv
 return env
u=evaluate(g);v=evaluate(p)
assert u['q']==q and u['Y']==Y and u['C']==1 and u['Bt']==46 and v['Bt']==0
assert k==8*m+4 and tau*tau==1+m*(m+1)*k*k and ell<tau<ell+k
assert u['Z']==beta*tau and u['A0']==0 and u['Bt']%beta==0
assert u['R']==4771536 and 24<=u['R'] and u['R']+q**3+q+1<=q**4
assert 0<ports['MC']<beta and 0<ports['MF']<2*beta and X<q*q
assert all(u[x]!=0 for x in ('A1','Fam','g72','out'))
assert u['out']==u['A0']**2+u['A1']**2+u['Fam']**2+u['g72']**2
print(json.dumps({'scope':'exact toy graph evaluation: first residual zero but full output nonzero; no Lean','toy_ports_not_compact':True,'all_13_coordinates_positive':True,'first_norm_zero':True,'other_three_residuals_nonzero':True,'full_output_nonzero':True,'companion_B_zero':True,'X_lt_q_squared':True,'rank_window_holds':True,'lean_elaborated':False},sort_keys=True,indent=2))
