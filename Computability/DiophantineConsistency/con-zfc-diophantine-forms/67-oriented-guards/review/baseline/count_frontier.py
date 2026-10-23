from pathlib import Path
from collections import Counter
import json,hashlib
R=Path(__file__).resolve().parents[2]/'sources';O=Path(__file__).resolve().parent
selection={
'ConZFC_Free_Coordinate_2026-10-23':['nine/generated/calibrated_absorbed_positive.json','short/generated/*.json','short/upstream/gap_minima75.json'],
'ConZFC_Integral_Root_2026-10-23':['circuits/p15_degree24.json','circuits/p15_degree26.json','circuits/p15_degree30.json','twelve/p12_desaturated_product.json'],
'ConZFC_Separated_Degrees_2026-10-23':['generated/nine_positive.json','generated/ten_integer.json','low_degree/thirteen_positive_degree132.json','low_degree/twelve_positive_degree242.json','low_degree/twelve_positive_degree258.json'],
'ZFC_Diophantine_Degree_Separated_2026-10-23':['nine_free_adjunct/generated/split_116_positive.json','sun/generated/sun10.json','signed/generated/signed_coprime_compact_split_crt.json','positive13_adjunct/thirteen_positive_degree126.json','short/circuits/*.json'],
'con-zfc-calibrated-carry-4b4349064a':['nine/generated/*positive.json','integer/generated/sun10*.json','positive/p*.json'],
'con_zfc_congruence_norms_2026-10-23':['ten/generated/signed10_b2.json','nine_majorant/generated/calibrated_positive.json','nine_fast/generated/calibrated_positive.json','fourteen/polynomial.json']}
def req(b,s):
 if not b:raise ValueError(s)
out=[]
for fam,patterns in selection.items():
 root=next(p for p in (R/fam).iterdir() if p.is_dir())
 for p in sorted({p for g in patterns for p in root.glob(g)}):
  d=json.loads(p.read_text());where=fam+'/'+str(p.relative_to(root))
  if not isinstance(d,dict) or ('nodes'not in d and 'source'not in d):continue
  if 'nodes'in d:
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
  out.append({'archive':fam+'.zip','path':str(p.relative_to(root)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'variables':len(vs),'domain':d.get('domain',d.get('witness_domain')),'operations':sum(counts.values()),'counts':dict(counts),'reported_degree':degree,'degree_status':'Reported metadata; exact-degree certificates replayed separately.','all_gates_live':True})
(O/'FRONTIER_COUNTS.json').write_text(json.dumps({'status':'PASS','count':len(out),'circuits':out},indent=2)+'\n');print('PASS',len(out),'circuits')
for x in out:print(x['archive'],x['path'],x['variables'],x['operations'],x['reported_degree'])
