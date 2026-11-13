#!/usr/bin/env python3
"""Exact positive first-residual control; not a full graph zero."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(p,h):
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,(str(p),hashlib.sha256(b).hexdigest());return json.loads(b)
g=pin(D/'research/ordinary13-residue-first82/candidate.json','bb90faa3815c5ff46f5fdbf41c2d001790d565baa17d97c79514c33fa928f1d2')
p=pin(D/'research/ordinary13-qcube-unscale84/candidate.json','2293d98affce104dc1522ddd69a0cf904ee752034dbd8959f4d3f41a3c604a77')
assert g['witnesses']==p['witnesses'] and g['fixed_numerals']==p['fixed_numerals']
b=46;q=b+1;Y=q**3;m=q*Y*Y;k=8*m+4;tau=8*m*m+8*m+1;ell=m*k;P0=b;t=1;r=k*(P0-1)+t+tau-ell
v={'J':1,'F':1,'alpha':45,'f':2,'i':1,'T':1,'X':q,'s':1,'r':r,'eta':1,'zeta':k-1,'y':1,'gamma':1}
ports={'beta':b,'K0':0,'MC':1,'MF':1};assert all(v[x]>0 for x in g['witnesses'])
def calc(graph):
 e={**ports,**v}
 for n,o,a,b0 in graph['source']:
  a=a if type(a) is int else e[a];b0=b0 if type(b0) is int else e[b0]
  e[n]=a*b0 if o=='*' else a+b0 if o=='+' else a-b0
 return e
c=calc(g);a=calc(p)
assert q==1+b and c['q']==q and c['Y']==Y and c['C']==1 and c['Bt']==b and a['Bt']==0
assert c['A0']==0 and c['Z']==b*tau and tau*tau==1+m*(m+1)*k*k
assert k==8*m+4 and ell<tau<ell+k and 0<c['Bt'] and c['Bt']%b==0
R=c['R'];assert 24<=R and R+q**3+q+1<=q**4 and 0<ports['MC']<b and 0<ports['MF']<2*b
assert all(c[x]!=0 for x in ('A1','Fam','g72','out')) and v['X']<q*q
print(json.dumps({'scope':'exact positive first-norm and rank-window control, NOT a full zero or consistency statement','inputs':v,'ports':ports,'q':q,'Y':Y,'m':m,'k':k,'tau':tau,'R':R,'residue_carrier':c['Bt'],'companion_carrier':a['Bt'],'first_residual_zero':True,'remaining_residuals_nonzero':True,'full_output_nonzero':True,'rank_window_holds':True,'X_lt_q_squared':True,'lean_elaboration':False},sort_keys=True,indent=2))
