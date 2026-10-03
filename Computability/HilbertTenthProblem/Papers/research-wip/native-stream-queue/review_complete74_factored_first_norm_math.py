#!/usr/bin/env python3
"""Independent exact-factor/domain review; no historical compiler imports."""
import argparse,hashlib,json
from collections import Counter
from pathlib import Path
PINS={'source':'7c4b10fa78a3fa6517083c41fc6228dd403fec5ac87f2ca6b80b45dd60e8b908','receipt':'7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28',
 'complete75_half_binomial.py':'5383b009a41abc19bb4c94e3f25c96ccfd4122d6a016c27b54fda0a75f7acab5','complete75_half_binomial.json':'a46ffb29e0d0db2f6c531edb442f0b5adb0f29a8a3f13dcdd8be9c64b4d17ea0',
 'complete75_positive_elimination.py':'70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749','complete75_positive_elimination.json':'03743efca27972fd97667501af214626481acb4993ed006b9d4033766c0ec703',
 'complete75_signed_projection_elimination101.py':'5a781fdacabab7feda2a8879c1cc207936045a1e4aa063c064a0bfffcdc9b4c8','complete75_signed_projection_elimination101.json':'00de69d028b79d3837bbd892a202d78d95092711d68ca6f40bf7d5e2ab20c3e3'}
def need(x,s):
 if not x:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 return type(a)is type(b) and (a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a) if type(a)is dict else len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b)) if type(a)is list else a==b)
def add(a,b,sign=1):
 c=dict(a)
 for m,v in b.items():c[m]=c.get(m,0)+sign*v
 return {m:v for m,v in c.items() if v}
def mul(a,b):
 c={}
 for m,v in a.items():
  for n,w in b.items():q=tuple(sorted(m+n));c[q]=c.get(q,0)+v*w
 return {m:v for m,v in c.items() if v}
def sos(rows,pairs):
 out=list(rows);squares=[]
 for i,(a,b) in enumerate(pairs):
  r='residual_'+str(i);q='square_'+str(i);out.extend([[r,'-',a,b],[q,'*',r,r]]);squares.append(q)
 name=squares[0]
 for i,v in enumerate(squares[1:],1):q='sum_'+str(i);out.append([q,'+',name,v]);name=q
 return out,name

def env(rows,values):
 e=dict(values)
 for n,o,a,b in rows:
  aa=e[a] if type(a)is str else a;bb=e[b] if type(b)is str else b;e[n]=aa*bb if o=='*' else aa+bb if o=='+' else aa-bb
 return e

def expressions(rows,inter):
 e={}
 def tok(x):
  if x not in inter:inter[x]=len(inter)
  return inter[x]
 for n,o,a,b in rows:
  if n=='L9':e[n]=tok(('proved_exact_coefficient_identity',));continue
  aa=e[a] if type(a)is str and a in e else tok(('free',a)) if type(a)is str else tok(('integer',a))
  bb=e[b] if type(b)is str and b in e else tok(('free',b)) if type(b)is str else tok(('integer',b))
  e[n]=tok((o,aa,bb))
 return e

def dense(rows,values):
 def plus(a,b,sgn):
  c=[(a[i] if i<len(a) else 0)+sgn*(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 def times(a,b):
  c=[0]*(len(a)+len(b)-1)
  for i,x in enumerate(a):
   for j,y in enumerate(b):c[i+j]+=x*y
  while len(c)>1 and c[-1]==0:c.pop()
  return c
 e=dict(values)
 for n,o,a,b in rows:
  aa=e[a] if type(a)is str else[a];bb=e[b] if type(b)is str else[b];e[n]=times(aa,bb) if o=='*' else plus(aa,bb,1 if o=='+' else-1)
 return e

def run(source,receipt,root):
 paths={k:Path(source) if k=='source' else Path(receipt) if k=='receipt' else root/k for k in PINS}
 for k,p in paths.items():need(sha(p.read_bytes())==PINS[k],'Pinned '+k)
 author=json.loads(paths['receipt'].read_text());need(author['source_sha256']==PINS['source'],'Frozen source provenance')
 raw=json.loads(paths['complete75_half_binomial.json'].read_text())['source'];pos=json.loads(paths['complete75_positive_elimination.json'].read_text());sgn=json.loads(paths['complete75_signed_projection_elimination101.json'].read_text())['source']
 modes={'raw30':(raw['schedule'],[v['equality'] for v in raw['sources']],None,52),'positive22':(pos['polynomial_schedule'][:75],pos['retained_equalities'],pos['retained_positive_witnesses'],84),'signed20':(sgn['polynomial_schedule'][:75],sgn['comparisons'],sgn['positive_witnesses'],84)}
 constants={'Bm1','Kconstant','twice_cell_bits','inner_bits','MC','MF'};records=[];count=Counter();wrong_k=None
 for item in author['forms']:
  mode=item['mode'];old,pairs,witnesses,degree=modes[mode];child=item['packet'];rows=child['source'];k='k' if mode=='raw30' else 'R10b';nodes={n:[o,a,b] for n,o,a,b in old}
  need(nodes['UM']==['*','wn2','sn2'] and nodes['ksn2']==['*',k,'sn2'],'Literal E and actual kY')
  if mode!='raw30':need(nodes['R10b']==['+','eta','zeta'],'Projected k definition')
  else:need('k' not in nodes and ['k','R10b'] in pairs,'Independent supplied k remains compared')
  removed={'UM2','scaled_norm_coefficient','ratio_product2'}
  for n in removed:need(not any(n in pair for pair in pairs),'No removed comparison operand')
  need({n for n,o,a,b in old if 'UM2'in(a,b)}=={'scaled_norm_coefficient'},'UM2 private')
  need({n for n,o,a,b in old if 'scaled_norm_coefficient'in(a,b) or 'ratio_product2'in(a,b)}=={'L9'},'Other removed gates private')
  expected=[]
  for n,o,a,b in old:
   if n=='L9':expected.extend([['first_root_base','*','UM','ksn2'],['first_next','+','first_root_base',k],['L9','*','first_root_base','first_next']])
   elif n not in removed:expected.append([n,o,a,b])
  need(exact(rows,expected) and exact(child['comparisons'],pairs),'Every complete gate/comparison preserved')
  # Independent three-variable expansion of the actually selected local block.
  X={('X',):1};Y={('Y',):1};K={('k',):1};E=mul(X,Y);KY=mul(K,Y);L=mul(E,KY)
  lhs=mul(add(mul(E,E),X),mul(KY,KY));rhs=mul(L,add(L,K))
  need(lhs==rhs=={('X','X','Y','Y','Y','Y','k','k'):1,('X','Y','Y','k','k'):1},'Full local coefficient identity');count['exact_local_expansions']+=1
  os,oo=sos(old,pairs);ns,no=sos(rows,pairs);need(exact(ns,child['polynomial_source']) and no==child['output'],'Every actual finalizer gate paid')
  inter={};oe=expressions(os,inter);ne=expressions(ns,inter)
  for i,(a,b) in enumerate(pairs):
   for n in (a,b):need(oe.get(n,('free',n))==ne.get(n,('free',n)),'Identical comparison operand');count['exact_comparison_operands']+=1
   need(oe['residual_'+str(i)]==ne['residual_'+str(i)],'Identical complete residual');count['exact_residual_DAGs']+=1
  need(oe[oo]==ne[no],'Same full SOS polynomial');count['exact_complete_SOS_DAGs']+=1
  cc=Counter(o for _,o,a,b in rows);pc=Counter(o for _,o,a,b in ns)
  need((len(rows),cc['*'],cc['+']+cc['-'])==(74,40,34),'Full certificate ledger')
  need((len(ns),pc['*'],pc['+']+pc['-'])=={'raw30':(130,59,71),'positive22':(106,51,55),'signed20':(100,49,51)}[mode],'Full SOS ledger')
  if witnesses is None:witnesses=sorted({v for _,o,a,b in old for v in(a,b) if type(v)is str}-set(nodes)-constants-{'x'})
  need(set(child['witnesses'])==set(witnesses) and len(witnesses)=={'raw30':30,'positive22':22,'signed20':20}[mode],'Unchanged supplied witnesses')
  degrees=[]
  for B in (16,32):
   slopes={n:2+(i%4) for i,n in enumerate(witnesses+['x'])};values={n:[1,v] for n,v in slopes.items()};values.update({n:[v] for n,v in dict(Bm1=B-1,Kconstant=17+29*B,twice_cell_bits=2*(B.bit_length()-1),inner_bits=3,MC=B-2,MF=B+3).items()})
   a=dense(os,values);b=dense(ns,values);need(a[oo]==b[no],'All dense coefficients of whole parent/child source agree')
   lead=slopes['w']**4*slopes['s']**8*slopes['k']**4*slopes['q']**36 if mode=='raw30' else 16*(B-1)**60*slopes['delta']**4*slopes['w']**10*slopes['s']**10*slopes['Jrep']**60
   need(len(b[no])-1==degree and b[no][-1]==lead,'Correct inherited exact degree/leader')
   degrees.append(dict(B=B,degree=degree,residual_degrees=[len(b['residual_'+str(i)])-1 for i in range(len(pairs))],coefficient_digest=sha(json.dumps(b[no]).encode())))
   count['whole_dense_polynomial_identities']+=1
  if mode=='raw30':
   wrong=[r[:]for r in rows]
   for r in wrong:
    if r[0]=='first_next':r[3]='R10b'
   # Move R10b before its mistaken new consumer to test a closed wrong DAG.
   r=next(r for r in wrong if r[0]=='R10b');wrong.remove(r);wrong.insert(0,r)
   bad,bo=sos(wrong,pairs);v={n:1 for n in witnesses+['x']};v.update(Bm1=15,Kconstant=83,twice_cell_bits=8,inner_bits=3,MC=14,MF=19)
   a=env(ns,v);b=env(bad,v);need((a['L9'],b['L9'],b[bo]-a[no])==(2,3,5),'Supplied-k versus R10b exact full offzero counterexample')
   wrong_k=dict(assignment=v,correct_L9=2,wrong_L9=3,whole_SOS_change=5)
  records.append(dict(mode=mode,certificate={'M':40,'A':34,'total':74},SOS={'M':pc['*'],'A':pc['+']+pc['-'],'total':len(ns)},comparisons=len(pairs),strictly_positive_witnesses=len(witnesses),actual_k_port=k,degree=degree,degree_checks=degrees))
 return dict(status='PASS',pins=PINS,counts=dict(count),forms=records,wrong_k_counterexample=wrong_k,scope='Same-coordinate complete comparison operands and full SOS polynomial over all commutative rings; unchanged strictly positive universal domains. Three-source degree scopes52/84/84. No parent theorem rerun, hostile API audit or accepting Pell tuple.')
def main():
 p=argparse.ArgumentParser();p.add_argument('--source',type=Path,required=True);p.add_argument('--receipt',type=Path,required=True);p.add_argument('--root',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();o=run(a.source,a.receipt,a.root)
 if a.expect:need(exact(o,json.loads(a.expect.read_text())),'Exact receipt replay')
 if a.output:a.output.write_text(json.dumps(o,sort_keys=True,indent=2)+'\n')
 print(json.dumps({'status':o['status'],'counts':o['counts'],'forms':[{k:v for k,v in f.items() if k!='degree_checks'} for f in o['forms']]},sort_keys=True))
if __name__=='__main__':main()
