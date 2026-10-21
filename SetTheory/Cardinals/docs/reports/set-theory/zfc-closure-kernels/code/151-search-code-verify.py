#!/usr/bin/env python3
"""Fast, portable identity, source, runtime-receipt and counterexample checks.

This audit does not rerun symbolic induction. Use replay_runtime.py for that.
The generated report states separately what is a proof, measurement, or open gap.
"""
import argparse, hashlib, json, subprocess, sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'vendor/portable'),str(Path(__file__).resolve().parent)]
import source_language as source
from replay_runtime import VARIANTS,DEPENDENCIES,require,digest
from block_audit import exact_blocks

def table(path):
 t={}
 for line in path.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
  require((q,b)not in t and b in(0,1)and w in(0,1)and d in('L','R'),'Table syntax')
  t[q,b]=(w,1 if d=='R'else-1,z)
 return t

def census(rows):
 ids={};paths={};parents=set()
 def intern(x):
  if x not in ids:ids[x]=len(ids)
  return ids[x]
 for p,op,arg in rows:
  require(p and set(p)<={'0','1'}and p not in paths,'Distinct binary source addresses')
  paths[p]=intern(('L',op,arg));parents.update(p[:i]for i in range(len(p)))
 require(not parents.intersection(paths),'Prefix-free leaves')
 for p in sorted(parents,key=len,reverse=True):paths[p]=intern(('N',paths[p+'0'],paths[p+'1']))
 require(len(parents)==len(rows)-1,'Full binary source tree')
 return len(ids)

def audit(name):
 cfg=VARIANTS[name];d=ROOT/'variants'/name;T=table(d/'machine.native.tm')
 S=json.loads((d/'source.sites.json').read_text());Q={q for q,b in T}
 require(digest(d/'machine.native.tm')==cfg['table'],'Native table hash')
 require(digest(d/'source.sites.json')==cfg['source'],'Source hash')
 require(len(Q)==218 and set(T)=={(q,b)for q in Q for b in(0,1)},'218 total working states')
 require({z for w,m,z in T.values()}-Q=={254},'Unique terminal label')
 reached={0};todo=[0]
 for q in todo:
  for b in(0,1):
   z=T[q,b][2]
   if z!=254 and z not in reached:reached.add(z);todo.append(z)
 require(reached==Q,'All working states graph reachable')
 mp={int(k):v for k,v in json.loads((d/'canonical-map.json').read_text()).items()}
 require(set(mp)==Q|{254}and set(mp.values())==set(range(219))and mp[0]==0 and mp[254]==218,'Canonical bijection')
 require(table(d/'machine.tm')=={(mp[q],b):(w,m,mp[z])for(q,b),(w,m,z)in T.items()},'Exact canonical relabeling')
 require(census(S)==205,'Independent source DAG census')
 require(source.graph_arithmetic(S)[0]==source.graph_intervals(S),'Independent CFG resolvers')
 e=ROOT/'evidence'/('runtime-'+name)
 rec=json.loads((e/'runtime.json').read_text());cases=json.loads((e/'cases.json').read_text())
 require(rec['status']=='ALL_PRIMITIVE_INTERFACES_PROVED'and rec['debug_enabled']is True,'Runtime success')
 require(rec['table_sha256']==cfg['table']and rec['sites_sha256']==cfg['source'],'Receipt input identity')
 require(rec['driver_sha256']==digest(ROOT/'code/replay_runtime.py'),'Receipt driver identity')
 require(rec['dependencies']==DEPENDENCIES,'Receipt engine identities')
 expected=[(i,p)for i,(_,op,arg)in enumerate(S)for p in((False,True)if op=='CD'else(False,))]
 require([(x['index'],x['positive'])for x in cases]==expected,'Complete ordered guard coverage')
 require(len(cases)==cfg['cases']==rec['cases']==rec['expected_cases'],'Case census')
 for x in cases:
  require(type(x['index'])is int and type(x['positive'])is bool,'Guard types')
  require(type(x['symbolic_steps'])is int and 0<x['symbolic_steps']<4000,'Proof construction bound')
  require(len(x['duration'])==13 and all(type(v)is int and v>=0 for v in x['duration'])and x['duration'][0]>0,'Positive affine duration')
  require(len(x['motion'])==13 and all(type(v)is int for v in x['motion']),'Affine displacement')
  require(set(x['kinds'])<={'literal','unary','list'}and all(type(v)is int and v>0 for v in x['kinds'].values())and sum(x['kinds'].values())==x['symbolic_steps'],'Rule census')
 require(sum(x['symbolic_steps']for x in cases)==cfg['rules']==rec['symbolic_steps'],'Total proof rules')
 require(min(x['duration'][0]for x in cases)==12==rec['minimum_actual_steps'],'Positive minimum duration')
 require(rec['directly_used_native_rows']==[list(k)for k in sorted(T)],'All literal rows covered')
 legacy_map={int(k):int(v)for k,v in json.loads((ROOT/'vendor/portable/runtime/reference_results/legacy_mapping.json').read_text()).items()}
 for q in Q|{254}:legacy_map.setdefault(q,q+1000)
 blocks=exact_blocks({(legacy_map[q],b):(w,m,legacy_map[z])for(q,b),(w,m,z)in T.items()},rec['block_schemas'])
 return {'variant':name,'working_states':218,'guards':len(cases),'rules':cfg['rules'],'minimum_duration':12,'independent_unary_blocks':len(blocks),'canonical_sha256':digest(d/'machine.tm')}

def source_edits():
 raw=(ROOT/'baseline/sites218.json').read_bytes();T=source.tree(json.loads(raw))
 old=source.subtree(T,'11111')
 require(len(source.sites(old[0]))==19 and len(source.sites(old[1]))==7,'PUSH19/COPY7 split')
 U=source.replace(T,'11111',old[1])
 require(source.compact(source.sites(U))==(ROOT/'variants/omit-zero/source.sites.json').read_bytes(),'Literal dummy-push deletion')
 p={'M':'111','D':'110101','N':'110100101'}
 b={k:source.subtree(T,v)for k,v in p.items()}
 require([source.boundary(b[k])for k in 'MDN']==[(0,0,False),(0,0,False),(0,0,True)],'Closed command bodies')
 U=T
 for dest,src in zip('MDN','DMN'):U=source.replace(U,p[dest],b[src])
 require(source.compact(source.sites(U))==(ROOT/'variants/dmn/source.sites.json').read_bytes(),'Literal command permutation')
 base=table(ROOT/'baseline/k218.native.tm');answer={}
 for name in VARIANTS:
  new=table(ROOT/'variants'/name/'machine.native.tm')
  require(set(new)==set(base),'Same state labels and row keys')
  answer[name]=[{'row':list(k),'old':list(base[k]),'new':list(new[k])}for k in sorted(base)if base[k]!=new[k]]
 require([x['row']for x in answer['omit-zero']]==[[164,1]],'Single changed omit row')
 require([x['row']for x in answer['dmn']]==[[135,1],[185,1]],'Two changed DMN rows')
 return answer

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);ap.add_argument('--skip-subchecks',action='store_true');a=ap.parse_args()
 require(__debug__ and not sys.flags.optimize,'Python assertions must be enabled')
 for p,h in DEPENDENCIES.items():require(digest(ROOT/'vendor'/p)==h,'Pinned dependency '+p)
 require(digest(ROOT/'baseline/k218.native.tm')=='2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f','Baseline table')
 require(digest(ROOT/'baseline/sites218.json')=='b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9','Baseline source')
 result={'status':'PASS','scope':'Identity, source transforms, exact state counts, ordered receipt coverage, four independently rederived block schemas, and separately invoked finite exact startup/counterexample checks. This audit is not a new proof-assistant theorem.','variants':[audit(n)for n in VARIANTS],'literal_row_changes':source_edits()}
 if not a.skip_subchecks:
  for relative in ['experiments/machine_compression/check_blank_endpoints_dense.py','experiments/machine_compression/check_runtime_obstructions.py','experiments/formalism/code/verify_checkpoint.py']:
   p=ROOT/relative;require(p.is_file(),'Missing subcheck '+relative)
   r=subprocess.run([sys.executable,str(p)],cwd=p.parent,text=True,capture_output=True)
   require(r.returncode==0,relative+' failed: '+r.stdout+r.stderr)
   print(relative+': PASS',flush=True)
 result['hash_manifest_checked']=False
 manifest=ROOT/'MANIFEST.json'
 if manifest.exists():
  files=json.loads(manifest.read_text())['files']
  for p,h in files.items():require(digest(ROOT/p)==h,'Manifest file '+p)
  result['hash_manifest_checked']=True;result['manifest_files']=len(files)
 out=a.output or ROOT/'reproduced/verification.json';out.parent.mkdir(parents=True,exist_ok=True)
 out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
 print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
