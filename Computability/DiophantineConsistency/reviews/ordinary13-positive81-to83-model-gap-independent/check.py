#!/usr/bin/env python3
"""Pinned graph-chain, companion and rank controls; never executes Lean."""
from pathlib import Path
import hashlib,itertools,json
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[1]
pins=json.loads((HERE/'pins.json').read_text())
for p,h in pins.items():assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h,p
r=ROOT/'research'
paths=['ordinary13-residue-first81/candidate.json','ordinary13-qcube-main83/candidate.json',
 'ordinary13-unit-product80/candidate.json','ordinary13-natural-unit-product89/candidate.json',
 'ordinary13-natural-unit-product88/candidate.json','ordinary13-natural-forced-gamma87/candidate.json',
 'ordinary13-natural-forced-w86/candidate.json','ordinary13-eta-zero-graph-adapter-audit/prototype.json']
a,b,c,n89,n88,n87,n86,n85=[json.loads((r/p).read_text()) for p in paths]
assert [len(g['source']) for g in (a,b,c,n89,n88,n87,n86,n85)]==[81,83,80,89,88,87,86,85]
assert a['witnesses']==b['witnesses']==c['witnesses']
assert a['fixed_numerals']==b['fixed_numerals']==c['fixed_numerals']
assert a['source'][:-8]==c['source'][:-7]
ra={z[0]:z for z in a['source']};rb={z[0]:z for z in b['source']}
assert set(rb)-set(ra)=={'g25','g28'}
for x in ra.keys()&rb.keys():
 if x not in ('g26','Bt'):assert ra[x]==rb[x],x
assert ra['g26']==['g26','+','X','K0'] and rb['g26']==['g26','+','X','g25']
assert ra['Bt']==['Bt','-','g27','F'] and rb['Bt']==['Bt','-','g27','g28']
raw={'f','r','y'};out=[[n,'+','n_'+n,1] for n in c['witnesses'] if n not in raw and n!='zeta'];rename={n:'n_'+n for n in raw}
for name,op,x,y in c['source']:
 if name=='g52':continue
 if name=='k':out.extend([['kbase','+','eta','n_zeta'],['k','+','kbase',1]])
 elif name=='r0':out.append(['r0','-','kbase','R'])
 else:out.append([name,op,rename.get(x,x),rename.get(y,y)])
assert out==n89['source']
for parent,child,name,var in zip([n89,n88,n87,n86],[n88,n87,n86,n85],['J','gamma','w','eta'],['n_J','n_gamma','n_w','n_eta']):
 assert parent['witnesses']==child['witnesses'] and parent['fixed_numerals']==child['fixed_numerals']
 assert [[var if x==name else x for x in row] for row in parent['source'] if row!=[name,'+',var,1]]==child['source']
assert n85['witnesses'][3]=='n_f' and n85['witnesses'][11]=='n_y'
# Independent finite controls on both carrier positivity directions and rank.
count=0
for q,F,alpha,X,K,J,MC,MF in itertools.product(range(3,10),range(1,9),range(1,9),range(1,15),range(4),range(3),range(2),range(2)):
 if F+alpha>=q:continue
 C=q-F-alpha;D=C*K-F;bp=C*(X+K)-F;B=C*(X+K*q)-F*q
 assert B==bp+(q-1)*D
 if B>0:assert bp>0
 if X>=q*q and bp>0:assert B>=2*q
 A=(q-F)*(q-1)+alpha;R=A*(q*q-1)+(MC+q*MF)*J
 assert A>=2*q-1>=q+1 and R>=q**3>=q*q
 count+=1
# Scalar control: selected positive witnesses complete a single nonzero graph assignment.
beta,J,F,alpha,K,X,MC,MF=46,1,1,45,0,47,1,1;q=1+J*beta;C=q-F-alpha
bp=C*(X+K)-F;B=C*(X+K*q)-F*q
R=(alpha+(q-F)*(q-1))*(q*q-1)+(MC+q*MF)*J
assert (bp,B,R)==(46,0,4771536) and X<q*q and R>=q**3 and R+q**3+q+1<=q**4
v={n:1 for n in a['witnesses']};v.update({'J':J,'F':F,'alpha':alpha,'w':1,'s':1,'beta':beta,'K0':K,'MC':MC,'MF':MF})
prime=1000003;e={x:y%prime for x,y in v.items()}
for name,op,x,y in a['source']:
 A=x if isinstance(x,int) else e[x];Bv=y if isinstance(y,int) else e[y]
 e[name]={'+':lambda:A+Bv,'-':lambda:A-Bv,'*':lambda:A*Bv}[op]()%prime
assert e['X']==X and e['out']!=0
# Root update identity/control, not an existence proof for tau.
for b,P,t,ell,k,tau in itertools.product(range(1,5),range(1,8),range(1,5),range(5),range(1,5),range(1,9)):
 if P!=b*t or tau<=ell:continue
 rr=k*(P-1)+t+tau-ell
 assert rr>0 and b*(ell+k+rr-k*P)-P==b*tau
print(json.dumps({'source_pins':pins,'exact_graph_and_forward_shift_rows':True,
 'carrier_rank_finite_controls':count,'partial_scalar_control_output_mod_prime':e['out'],
 'partial_scalar_control_prime':prime,'lean_executed':False,
 'scope':'bounded source/math audit, not all-model proof or graph endpoint'},sort_keys=True,indent=2))
