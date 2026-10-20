#!/usr/bin/env python3
"""Exact-table unbounded symbolic primitive checking, with bounded proof search.

Adapts the reviewed K219 check_runtime219.py argument binding to an explicit
candidate. Does not certify source equivalence or blank initialization.
"""
from pathlib import Path
import argparse,hashlib,json,sys,time
HERE=Path(__file__).resolve().parent
PINS={
 'symbolic_runtime.py':'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145',
 'independent_runtime.py':'0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346',
 'legacy_mapping.json':'26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf',
}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for k in ('table','sites','baseline','out'):ap.add_argument('--'+k,type=Path,required=True)
 for k in ('table-sha','sites-sha'):ap.add_argument('--'+k,required=True)
 ap.add_argument('--max-seconds',type=float,default=480)
 a=ap.parse_args();need(__debug__ and not sys.flags.optimize,'Assertions disabled');need(not a.out.exists(),'Output exists')
 need(sha(a.table)==a.table_sha and sha(a.sites)==a.sites_sha,'Input pins')
 vendor=a.baseline/'portable/runtime/vendor';mp=a.baseline/'portable/runtime/reference_results/legacy_mapping.json'
 deps={str(vendor/n):h for n,h in PINS.items() if n.endswith('.py')};deps[str(mp)]=PINS['legacy_mapping.json']
 need(all(sha(Path(p))==h for p,h in deps.items()),'Dependency drift')
 sys.dont_write_bytecode=True;sys.path.insert(0,str(HERE/'code'));sys.path.insert(0,str(vendor))
 import build221 as b,source_language as s,symbolic_runtime as runtime
 table=b.read_table(a.table.read_bytes());sites=json.loads(a.sites.read_text());tree=s.tree(sites)
 need(s.sites(tree)==sites and s.graph_arithmetic(sites)[0]==s.graph_intervals(sites),'Source CFG/ordinal binding')
 Q={q for q,bit in table};need(0 in Q and 84 in Q and 254 not in Q,'Conventions')
 mapping={int(q):int(z) for q,z in json.loads(mp.read_text()).items()}
 for q in Q|{254}:
  if q not in mapping:mapping[q]=q+1000
 need(len(set(mapping.values()))==len(mapping),'Relabelling collision');need(mapping[84]==96 and mapping[254]==254,'Dispatch')
 legacy={(mapping[q],bit):(w,d,mapping[z]) for (q,bit),(w,d,z) in table.items()}
 a.out.mkdir(parents=True);(a.out/'driver.py').write_bytes(Path(__file__).read_bytes())
 started=time.monotonic();cases=[];used=set();expected=sum(2 if op=='CD' else 1 for pc,op,arg in sites)
 result=dict(table_sha256=a.table_sha,source_sha256=a.sites_sha,working_states=len(Q),source_metrics=s.metrics(tree),dependencies=deps,expected_cases=expected,scope='Exact symbolic primitive contracts with arbitrary natural registers/gap/first spare and arbitrary finite remaining spare list. No source theorem/startup claim.')
 try:
  lemmas,blocks=runtime.prove_blocks(legacy);result['blocks']=blocks
  for index,site in enumerate(sites):
   for positive in ((False,True) if site[1]=='CD' else (False,)):
    need(time.monotonic()-started<a.max_seconds,'Whole candidate proof-search deadline')
    ans=runtime.case(legacy,lemmas,site,positive);used.update(ans.pop('rows'));ans.pop('trace')
    cases.append(dict(index=index,positive=positive,**ans))
  result['status']='ALL_PRIMITIVE_INTERFACES_PROVED'
 except (AssertionError,KeyError,ValueError) as e:
  result.update(status='NOT_PROVED',index=locals().get('index'),site=locals().get('site'),positive=locals().get('positive'),reason=repr(e))
 result.update(cases=len(cases),symbolic_steps=sum(x['symbolic_steps'] for x in cases),seconds=time.monotonic()-started,used_rows=sorted(used))
 need(sha(a.table)==a.table_sha and sha(a.sites)==a.sites_sha,'Post input drift')
 need(all(sha(Path(p))==h for p,h in deps.items()),'Post dependencies drift')
 dump(a.out/'cases.json',cases);dump(a.out/'result.json',result)
 print(json.dumps({k:v for k,v in result.items() if k not in ('blocks','used_rows')},indent=2),flush=True)
if __name__=='__main__':main()
