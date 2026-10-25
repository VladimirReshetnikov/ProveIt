#!/usr/bin/env python3
"""Independent count/inventory checks. No producer imports or writes."""
import argparse,collections,gzip,hashlib,json
from pathlib import Path

def need(c,m):
 if not c: raise ValueError(m)
def load(p): return json.loads(p.read_text())
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def direct(p):
 e=load(p/'equation.json'); q=load(p/'expanded_polynomial.json'); m=load(p/'METRICS.json')
 out=collections.Counter()
 for row in e['residuals']:
  terms=row['terms']; need(all(len(v)<=2 for c,v in terms),'nonquadratic row')
  for c,v in terms:
   for d,w in terms: out[tuple(sorted(v+w))]+=c*d
 out={k:v for k,v in out.items() if v}; actual={tuple(v):c for c,v in q['terms']}
 need(len(actual)==len(q['terms']),'duplicate terms');need(out==actual,'square expansion differs')
 support=set(i for v in out for i in v)
 a={'variables':len(support),'rows':len(e['residuals']),'degree':max(map(len,out)), 'height':max(map(abs,out.values())),'monomials':len(out),'row_height':max(abs(c) for row in e['residuals'] for c,v in row['terms'])}
 need(a==m,'direct metrics differ')
 return dict(a,equation_sha256=sha(p/'equation.json'),expanded_sha256=sha(p/'expanded_polynomial.json'))
def circuit(p):
 e=load(p);nodes=e.get('nodes');counts=collections.Counter()
 if nodes is not None:
  alive=set();stack=[e['output']]
  while stack:
   k=stack.pop()
   if k in alive: continue
   alive.add(k);n=nodes[k]
   if n[0] in ('add','sub','mul'):
    need(0<=n[1]<k and 0<=n[2]<k,'invalid DAG');stack.extend(n[1:])
  for i,n in enumerate(nodes):
   if n[0] in ('add','sub','mul'):
    need(i in alive,'dead operation');counts[n[0]]+=1
  variables=[n[1] for i,n in enumerate(nodes) if n[0]=='variable' and i in alive]
  need(variables==e['variables'],'variables differ')
  need(dict(counts)==e['operation_counts'],'op splits differ')
 else:
  rows=e['source'];idx={r[0]:r for r in rows};alive=set();stack=[e['output']]
  while stack:
   v=stack.pop()
   if isinstance(v,int) or v in alive:continue
   alive.add(v)
   if v in idx: stack.extend(idx[v][2:])
  defined=set(e['witnesses'])|set(e['fixed_numerals'])
  for name,op,a,b in rows:
   need(name not in defined and name in alive,'dead or duplicate gate')
   need(all(isinstance(x,int) or x in defined for x in [a,b]),'forward/invalid port')
   defined.add(name);counts[op]+=1
  variables=e['witnesses'];need(all(x in alive for x in variables),'dead input')
  need(dict(counts)==e['operation_breakdown'],'op splits differ')
 need(sum(counts.values())==e['operations'],'op count differs')
 return {'variables':len(variables),'operations':sum(counts.values()),'operation_counts':dict(counts),'reported_exact_degree':e['exact_degree'],'sha256':sha(p)}
def payload(p):
 raw=gzip.decompress(p.read_bytes());return {'bits':int.from_bytes(raw,'little').bit_length(),'bytes':len(raw),'gzip_sha256':sha(p),'raw_sha256':hashlib.sha256(raw).hexdigest()}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);a=ap.parse_args();r=a.root
 out={'status':'PASS','scope':'Independent exact quartic expansions, gate liveness/counts, and coefficient bytes. Reported compact degrees are separately proved by mathematical audits.','direct':{},'circuits':{},'coefficients':{}}
 for name in ['centered307','centered308','centered310']:out['direct'][name]=direct(r/'direct'/name)
 for rel in ['positive/equation_81.json','positive/equation_82.json','integer/weak_product11_none.json','integer/weak_product11_simple.json','integer/free_product11_none.json','integer/free_product11_simple.json','lowdegree/equation.json','lowdegree/thirteen/equation.json']:out['circuits'][rel]=circuit(r/rel)
 out['historical_comparisons']={}
 prior=r/'prior/wave16'
 if not prior.is_dir():prior=r/'prior/ConZFC_Signed_Caps_Free_Scales'
 for name,digest in [('fourteen','dfee47f9bb5c9a4b699c50f5e7240224adcc027b5e968a72ed7e14d4fe5e9d90'),('thirteen','d8d5f295b25846a4ab46db6e91e0c16a10b36c550d71212b5abcffa80c2485d2')]:
  rel='prior/wave15/prior/ZFC_Diophantine_Coprime_Projection/lowdegree/'+name+'/equation.json'
  row=circuit(prior/rel);need(row['sha256']==digest,'historical equation pin '+name)
  out['historical_comparisons']['prior/wave16/'+rel]=row
 for branch in ['positive','integer','lowdegree']:
  for p in sorted((r/branch/'coefficients').glob('*.gz')):out['coefficients'][p.relative_to(r).as_posix()]=payload(p)
 print(json.dumps(out,indent=2))
if __name__=='__main__':main()
