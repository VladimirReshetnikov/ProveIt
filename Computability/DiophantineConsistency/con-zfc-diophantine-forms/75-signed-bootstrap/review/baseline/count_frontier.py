from pathlib import Path
from collections import Counter
import json,hashlib
R=Path(__file__).resolve().parents[2]/'sources';O=Path(__file__).resolve().parent
selection={
'ConZFC_Gap_Congruence_2026-10-23':['nine/generated/*.json','integer/generated/integer10.json','integer/alternative_low_cost/generated/integer10.json','algebra/p15*.json'],
'ConZFC_Positive_Gap_2026-10-23':['research_nine/compact_candidate/generated/gap_100_positive.json','research_low_degree/supplement15/circuits/p15_degree24_transport89.json'],
'ZFC_Diophantine_Oriented_Guards_2026-10-23':['nine/generated/*positive.json','signed/generated/sun10.json','signed108trim/generated/sun10.json','signed13/generated/*.json','positive/fourteen_positive_degree30.json'],
'con-zfc-congruence-carriers':['positive/p*.json'],
'con-zfc-sign-and-norm':['positive13/polynomial.json','nine/generated/*global.json'],
'con-zfc-sign-recovery-2026-10-23':['positive14/pell14_degree34.json','nine/generated/order7_positive.json'],
'con-zfc-structural-reductions-2026-10-23':['positive14/polynomial.json','nine-positive-111/generated/split_111_positive.json'],
'con_zfc_shared_taps_carriers_2026-10-23':['nine/generated/*positive.json','sun/generated/sun10.json','pell/circuits/*.json']}
def req(b,s):
 if not b:raise ValueError(s)
out=[]
for fam,patterns in selection.items():
 root=next(p for p in (R/fam).iterdir() if p.is_dir())
 for p in sorted({p for g in patterns for p in root.glob(g)}):
  d=json.loads(p.read_text());where=fam+'/'+str(p.relative_to(root))
  if not isinstance(d,dict) or ('nodes'not in d and 'source'not in d and 'gates'not in d):continue
  if 'gates'in d:
   vs=d['variables'];known=set(vs)|set(d['fixed_ports']);counts=Counter();defs={}
   for row in d['gates']:
    n,op,args=row['id'],row['op'],row['args'];req(n not in known,where+' duplicate');req(op in ['add','sub','mul'],where+' op');req(len(args)==2 and all(type(v)is int or v in known for v in args),where+' topology');known.add(n);counts[op]+=1;defs[n]=args
   live=set()
   def visit(x):
    if type(x)is int or x not in defs or x in live:return
    live.add(x)
    for a in defs[x]:visit(a)
   visit(d['output']);req(len(live)==len(defs),where+' dead gates')
  elif 'nodes'in d:
   nodes=d['nodes'];req(isinstance(nodes,list),where);counts=Counter(n['kind'] for n in nodes if n['kind']in['add','sub','mul']);live=set()
   def visit(i):
    if i in live:return
    req(type(i)is int and 0<=i<len(nodes),where+' pointer');live.add(i);n=nodes[i]
    if n['kind']in['add','sub','mul']:
     req(n['left']<i and n['right']<i,where+' topology');visit(n['left']);visit(n['right'])
    else:req(n['kind']in['variable','fixed','literal'],where+' nodekind')
   visit(d['output']);req(len(live)==len(nodes),where+' dead nodes');vs=[n['name']for n in nodes if n['kind']=='variable'];req(len(set(vs))==len(vs),where+' duplicate variable')
  else:
   rows=d['source']
   if not isinstance(rows,list):continue
   vs=d.get('witnesses',d.get('variables'));req(isinstance(vs,list),where+' variables');defs={x[0]:x for x in rows};req(len(defs)==len(rows),where+' duplicate gate');known=set(vs)|set(d.get('fixed_numerals',[]));counts=Counter()
   for n,op,a,b in rows:
    req(op in ['+','-','*'],where+' op');req(all(type(v)is int or v in known for v in [a,b]),where+' topology');known.add(n);counts[op]+=1
   live=set()
   def visit(x):
    if type(x)is int or x not in defs or x in live:return
    live.add(x);_,_,a,b=defs[x];visit(a);visit(b)
   if not isinstance(d.get('output'),str):continue
   visit(d['output']);req(len(live)==len(rows),where+' dead gates')
  degree=d.get('exact_degree',d.get('degree',d.get('degree_upper_bound')))
  if degree is None and p.name=='split_116_positive.json':degree=json.loads((p.parent/'split_116_positive_certificate_degree.json').read_text())['exact_degree']
  if degree is None and 'short/circuits/' in str(p.relative_to(root)):
   degree=next(c['exact_degree'] for c in json.loads((root/'short/audit_optimized_stdout.json').read_text())['circuits'] if c['name']==d['name'])
  if degree is None and '/pell/circuits/' in str(p):degree=int(p.stem.split('degree')[1])
  if degree is None:
   cert=p.with_name(p.stem+'_certificate_degree.json')
   if not cert.exists() and '_global' in p.stem:cert=p.with_name(p.stem.replace('_global','')+'_certificate_degree.json')
   if cert.exists():degree=json.loads(cert.read_text()).get('exact_degree')
   ver=p.parent/'VERIFICATION.json'
   if degree is None and ver.exists():
    obj=json.loads(ver.read_text())
    for v in obj.values() if isinstance(obj,dict) else []:
     if isinstance(v,list):
      for rec in v:
       if isinstance(rec,dict) and rec.get('file')==p.name:degree=rec.get('exact_degree')
  out.append({'archive':fam+'.zip','path':str(p.relative_to(root)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'variables':len(vs),'domain':d.get('domain',d.get('witness_domain')),'operations':sum(counts.values()),'counts':dict(counts),'reported_degree':degree,'degree_status':'Reported metadata; exact-degree certificates replayed separately.','all_gates_live':True})
(O/'FRONTIER_COUNTS.json').write_text(json.dumps({'status':'PASS','count':len(out),'circuits':out},indent=2)+'\n');print('PASS',len(out),'circuits')
for x in out:print(x['archive'],x['path'],x['variables'],x['operations'],x['reported_degree'])
