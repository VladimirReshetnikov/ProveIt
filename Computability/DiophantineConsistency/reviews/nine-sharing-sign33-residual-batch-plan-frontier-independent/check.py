#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-residual-batch-plan';f=d/'research/nine-sharing-quartic65-sign33-candidate/seed.json'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
assert h(f)=='a8cd4d01962b9380065ebbd3d7b75db3ffcadf18969099398bd151c4e2219e75'
assert h(p/'check.py')=='11bafab69512332c0ed04263a7a3274806aba2758c874e36c97d800241932c57' and h(p/'result.json')=='95244a5e2a3e94856144d5caae192b6d7cac454a4622aadf2eb9924e91fbf7a8'
out=subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,check=True);assert not out.stderr and out.stdout==(p/'result.json').read_bytes();record=json.loads(out.stdout);data=json.loads(f.read_text())
assert (data['coordinate_count'],data['jones_witness_count'],data['input_coordinate'])==(34,33,0) and data['fixed_ports']==['beta','K0','MC','MF']
names='q2 q3 X Y E kY ell Delta main_root c2 Dc2 N1 gap tau N0 Nt f2 cTminusR V normalized_S normalized_S2 V2minusY2 Na scaled_Ns'.split();assert len(data['residuals'])==24
cut_names='q2 q3 X Y E kY ell Delta main_root c2 Dc2 gap tau f2 cTminusR V normalized_S normalized_S2 V2minusY2'.split();cuts={r['name']:r for r in data['gate_records'] if r['kind']=='materialized'};assert set(cuts)==set(cut_names)
for j,n in enumerate(cut_names):
 c=cuts[n];idx=c.get('positive_coordinate',c.get('sign_coordinate'));assert idx==15+j and idx-1==14+j
 assert c.get('sign',1)==(-1 if n=='V2minusY2' else 1);assert record['materialized_cuts'][n]=={'full_fin34_index':idx,'orientation':c.get('sign',1)}
portsets=[{'beta'},set(),set(),set(),{'beta','MC','MF'},{'beta','K0','MC','MF'},set(),set()];tally={'positive':0,'signed':0,'norm':0}
for i,(r,n) in enumerate(zip(data['residuals'],names)):
 assert r['gate']==n;tally[r['kind']]+=1;stack=[r['expr']];ps=set();vs=set()
 while stack:
  t=stack.pop();assert isinstance(t,list);op=t[0]
  if op=='port':assert len(t)==2 and t[1] in data['fixed_ports'];ps.add(t[1])
  elif op=='var':assert len(t)==2 and type(t[1]) is int and 1<=t[1]<=33;vs.add(t[1]);assert 0<=t[1]-1<33
  elif op=='num':assert len(t)==2 and type(t[1]) is int
  else:assert op in {'add','sub','mul'} and len(t)==3;stack.extend(t[1:])
 rr=record['rows'][i];assert rr=={'residual_index':i,'gate':n,'kind':r['kind'],'ports':sorted(ps),'full_fin34_indices':sorted(vs)}
 if n in cuts:
  idx=cuts[n].get('positive_coordinate',cuts[n].get('sign_coordinate'));assert r['expr'][0]=='sub' and r['expr'][1]==['var',idx]
for b in range(8):assert set().union(*(set(record['rows'][i]['ports']) for i in range(3*b,3*b+3)))==portsets[b]
assert tally=={'positive':14,'signed':5,'norm':5};assert data['residuals'][21]['expr'][2]==['sub',['mul',['add',['var',13],['num',1]],['add',['var',13],['num',1]]],['mul',['var',30],['var',30]]]
print(json.dumps({'status':'PASS','residuals':24,'cuts':19,'norms':5,'batches':8,'scope':'external inventory and indexing only; no Lean proof'},indent=2,sort_keys=True))
