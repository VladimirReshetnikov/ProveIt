#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-single-cut-survey';S=D/'research/nine-sharing-sign26-sextic-gap-congruence-candidate/seed.json';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert H(P/'survey.py')=='ca7d6fb93ca293f1ab135850ad94cbbf0a5b768c16696e90015276288c9df0cf' and H(P/'result.json')=='fe877dbe047599877219c920023723221b19de9051ecdea11ad43b37be960dc3' and H(S)=='36efa7dd3b2ea06d210b8975db2cbfc4f7494549c87204ada18747a720cb1f25'
s=json.loads(S.read_text());record=json.loads((P/'result.json').read_text());rows=s['residuals'];assert len(rows)==17 and record['status']=='PASS'
# Independent iterative postorder tropical evaluation. Addition and subtraction
# take max, multiplication adds. This evaluates the syntax, not cancellations.
def weight(tree,coordinate=None,replacement=1):
 todo=[(tree,False)];vals=[]
 while todo:
  t,done=todo.pop();assert isinstance(t,list) and t
  op=t[0]
  if op in ('var','num','port'):
   assert len(t)==2;vals.append((replacement if t[1]==coordinate else 1) if op=='var' else 0)
  else:
   assert len(t)==3 and op in ('add','sub','mul')
   if not done:todo.extend([(t,True),(t[2],False),(t[1],False)])
   else:
    right=vals.pop();left=vals.pop();vals.append(left+right if op=='mul' else max(left,right))
 assert len(vals)==1;return vals[0]
def vars_(t):
 todo=[t];out=set()
 while todo:
  u=todo.pop()
  if u[0]=='var':out.add(u[1])
  elif u[0] in ('add','sub','mul'):todo.extend(u[1:])
 return out
cases=[]
for i,row in enumerate(rows):
 t=row['expr']
 if t[0]!='sub' or t[1][0]!='var':continue
 v=t[1][1];rhs=t[2];assert v not in vars_(rhs);w=weight(rhs);ds=[(other['gate'],weight(other['expr'],v,w)) for j,other in enumerate(rows) if i!=j];cases.append({'gate':row['gate'],'kind':row['kind'],'coordinate':v,'rhs_degree':w,'max_remaining_degree':max(d for _,d in ds),'above_three':[{'gate':name,'syntactic_degree':d} for name,d in ds if d>3]})
assert len(cases)==11 and len({c['coordinate'] for c in cases})==11 and cases==record['cases'] and all(c['max_remaining_degree']>3 for c in cases)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'survey.py')],check=True,capture_output=True,timeout=120);assert json.loads(r.stdout)==record
print(json.dumps({'status':'PASS_INDEPENDENT_SYNTACTIC_AUDIT','seed_rows':len(rows),'literal_cuts':len(cases),'all_maxima_above_three':True,'scope':'single literal cuts, syntactic upper degrees only; no exact degree, positivity, model equivalence, impossibility, or Lean claim'},sort_keys=True,indent=2))
