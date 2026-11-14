#!/usr/bin/env python3
"""Audit stored evidence; optionally rerun the explicitly bounded C++ searches."""
from pathlib import Path
from collections import Counter
import argparse,itertools,json,math,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'code'))
from check_qn6_quotient import check as qncheck,parse
from check_blank_ray import check as raycheck

def done(path):
 line=next(x for x in reversed(path.read_text().splitlines())if x.startswith('DONE '))
 xs=line.split();return{xs[i]:int(xs[i+1])for i in range(1,len(xs),2)if xs[i]!='seconds'}
def run(args):
 p=subprocess.run(list(map(str,args)),capture_output=True,text=True)
 if p.returncode:raise RuntimeError(p.stdout+p.stderr)
 return p

def audit():
 table=parse(ROOT/'inputs/runtime193.native.tm');assert len(table)==386
 states={q for q,b in table};assert len(states)==193
 assert {n for w,d,n in table.values()}-states=={254}
 edits=[list(map(int,line.split()))for line in(ROOT/'inputs/edits.tsv').read_text().splitlines()]
 pool=[json.loads(line)for line in(ROOT/'recorded/runtime193_corrected_neutral_k6.jsonl').read_text().splitlines()]
 assert len(edits)==len(pool)==346
 assert edits==[[i,x['state'],x['read'],*x['new']]for i,x in enumerate(pool)]
 pairs=sum((a[1],a[2])!=(b[1],b[2])for a,b in itertools.combinations(edits,2));assert pairs==58485
 templates=[line.split()for line in(ROOT/'inputs/startup_any_frame_templates.tsv').read_text().splitlines()]
 sites=json.loads((ROOT/'inputs/primary.sites.json').read_text())
 assert [int(x[0])for x in templates]==list(range(25,45))
 assert all(int(mask)==511 and path==sites[int(pc)][0]for pc,path,mask in templates)
 recorded={name:done(ROOT/'recorded'/f'{name}.log')for name in ['two_startup','two_startup_all','permutation_startup','runtime192_merge']}
 a=recorded['two_startup_all'];assert a['pairs']==pairs and a['simulations']==pairs*193 and a['successes']==0
 assert(a['ticks'],a['halts'],a['rays'],a['limits'])==(2676983463,117274,11159792,10539)
 a=recorded['permutation_startup'];assert a['permutations']==math.factorial(9)==a['simulations']==a['rays'] and a['ticks']==32296320 and not a['successes']and not a['limits']
 a=recorded['runtime192_merge'];assert a==dict(pairs=18528,trials=25115136,combos=195563,hits=0)
 variants=Counter()
 for p in sorted((ROOT/'variant193').glob('*_startup.log')):
  d=done(p);assert not d['successes']and not d['limits'];variants.update(d)
 assert variants==dict(edits=49,successes=0,simulations=9457,ticks=81042,halts=100,rays=9357,limits=0)
 for p in(ROOT/'variant193').glob('variant*.tm'):assert len(parse(p))==386
 rows,qn=qncheck(ROOT/'inputs/qn6.native.tm');old=json.loads((ROOT/'recorded/qn6_runtime193_blank.json').read_text())
 for key,value in qn.items():assert old[key]==value,key
 relay=raycheck(ROOT/'inputs/relay193.native.tm');assert relay==json.loads((ROOT/'recorded/relay193_blank_ray.json').read_text())
 for name in ['two_startup','two_startup_all','permutation_startup','runtime192_merge']:assert not(ROOT/'recorded'/f'{name}_hits.jsonl').read_text()
 return {'status':'PASS','scope':'Stored finite evidence and short literal ray checks; bounded searches are not rerun by default. No sub-194 consistency machine claimed.','recorded_searches':recorded,'variant_totals':dict(variants),'qn6_ray':{k:qn[k]for k in ['status','steps','final_state','final_head','one_cells']},'relay_ray':{k:relay[k]for k in ['status','steps','final_state','final_head','one_cells']}}

def searches(out):
 out.mkdir(parents=True,exist_ok=True)
 names=['search_two_startup','search_two_startup_all','search_permutation_startup','joint_return_merge']
 for name in names:run(['g++','-O3','-std=c++17',ROOT/'code'/(name+'.cpp'),'-o',out/name])
 table=ROOT/'inputs/runtime193.native.tm';templates=ROOT/'inputs/startup_any_frame_templates.tsv'
 jobs=[('two_startup','search_two_startup',[table,ROOT/'inputs/edits.tsv',250000,0,100000,templates]),('two_startup_all','search_two_startup_all',[table,ROOT/'inputs/edits.tsv',250000,0,100000,templates]),('permutation_startup','search_permutation_startup',[table,ROOT/'inputs/noedit.tsv',250000,0,100000,templates]),('runtime192_merge','joint_return_merge',[table,6,250,ROOT/'inputs/runtime193_corrected_patterns_k6.txt'])]
 results={}
 for name,program,args in jobs:
  p=run([out/program,*args]);(out/(name+'.log')).write_text(p.stderr);(out/(name+'_hits.jsonl')).write_text(p.stdout)
  assert not p.stdout;actual=done(out/(name+'.log'));assert actual==done(ROOT/'recorded'/(name+'.log')),(name,actual)
  results[name]=actual
 return results

def variants(out):
 out.mkdir(parents=True,exist_ok=True)
 program=out/'search_startup'
 run(['g++','-O3','-std=c++17',ROOT/'code/search_startup.cpp','-o',program])
 totals=Counter()
 for table in sorted((ROOT/'variant193').glob('variant*.tm')):
  p=run([program,table,ROOT/'inputs/noedit.tsv',250000,0,100000,ROOT/'inputs/startup_any_frame_templates.tsv'])
  log=out/(table.stem+'_startup.log');log.write_text(p.stderr)
  (out/(table.stem+'_startup.jsonl')).write_text(p.stdout)
  assert not p.stdout
  actual=done(log);assert actual==done(ROOT/'variant193'/log.name),(table.name,actual)
  totals.update(actual)
 return dict(totals)

if __name__=='__main__':
 if not __debug__:raise SystemExit('Run without Python -O; assertions check evidence.')
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--run-searches',action='store_true');ap.add_argument('--run-variants',action='store_true');ap.add_argument('--output',type=Path);a=ap.parse_args();receipt=audit()
 if a.run_searches:
  if a.output:receipt['fresh_searches']=searches(a.output)
  else:
   with tempfile.TemporaryDirectory(prefix='physical-replay-')as td:receipt['fresh_searches']=searches(Path(td))
 if a.run_variants:
  if a.output:receipt['fresh_variants']=variants(a.output)
  else:
   with tempfile.TemporaryDirectory(prefix='physical-variants-')as td:receipt['fresh_variants']=variants(Path(td))
 if a.output:a.output.mkdir(parents=True,exist_ok=True);(a.output/'audit_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2))
