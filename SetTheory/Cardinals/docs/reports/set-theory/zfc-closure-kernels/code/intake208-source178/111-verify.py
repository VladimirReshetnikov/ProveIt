#!/usr/bin/env python3
"""Audit or reproduce the coordinated-marker search supplement."""
import argparse,gzip,hashlib,importlib.util,json,re,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent

def need(ok,msg):
 if not ok:raise ValueError(msg)
def digest(raw):return hashlib.sha256(raw).hexdigest()
def module(name,path):
 s=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(s);s.loader.exec_module(m);return m

def fields(log):
 m=re.search(r'END radius (\d+) cap (\d+) families (\d+) attempts (\d+) first (\d+) hits (\d+) seconds (\S+)',log)
 need(m is not None,'missing completed search record')
 return dict(zip(['radius','cap','families','attempts','first_case_passes','hits'],map(int,m.groups()[:6])))

def main():
 p=argparse.ArgumentParser();p.add_argument('--work',type=Path,required=True);p.add_argument('--search',action='store_true');p.add_argument('--regenerate',action='store_true');p.add_argument('--cxx',default='g++');a=p.parse_args();need(not a.work.exists(),'choose a fresh --work directory');a.work.mkdir(parents=True)
 meta=json.loads((ROOT/'inputs.json').read_text());auditor=module('independent_audit',ROOT/'code/audit_blank_invariant.py');gen=module('invariant_generator',ROOT/'code/local_invariants.py');reports={}
 for name,item in meta.items():
  table=ROOT/'inputs'/(name+'.tm');need(digest(table.read_bytes())==item['table_sha256'],'table hash')
  raw=gzip.decompress((ROOT/'inputs'/(name+'.invariant.json.gz')).read_bytes());need(digest(raw)==item['invariant_sha256'],'invariant hash');inv_path=a.work/(name+'.invariant.json');inv_path.write_bytes(raw);inv=json.loads(raw)
  result=auditor.audit(table,inv_path);need(result==json.loads((ROOT/'results'/(name+'.invariant-audit.json')).read_text()),'independent audit mismatch')
  T,start=gen.read(table);states=sorted({q for q,b in T});need(len(states)==215,'working-state count');need(len(T)==430,'row count');need(999 not in states,'fresh helper label');need({q for w,d,q in T.values()}-set(states)=={254},'separate halt')
  lines=[f"{inv['radius']} {start} {len(states)}"]
  for q in states:
   masks=inv['masks'][str(q)];lines.append(' '.join(map(str,[q,*T[q,0],*T[q,1],len(masks),*masks])))
  cpp_input=a.work/(name+'.input.txt');cpp_input.write_text('\n'.join(lines)+'\n')
  pairs=a.work/(name+'.pairs.txt');pairs.write_text('\n'.join(' '.join(str(pp[k])for k in ['p','q','branch','side','pmarker','qmarker'])for pp in inv['distinguishable_pairs'])+'\n')
  expected={k:item[k]for k in ['radius','cap','families','attempts','first_case_passes','hits']};need(fields((ROOT/'results'/(name+'.search.log')).read_text())==expected,'saved receipt mismatch');need(item['attempts']==item['families']*213**2,'count arithmetic');need(item['hits']==0,'unexpected accepted candidate')
  if a.regenerate:need(json.dumps(gen.analyze(T,start,5,True)).encode()==raw,'regenerated invariant mismatch')
  reports[name]=result
 pc=subprocess.run([sys.executable,str(ROOT/'code/verify_positive_control.py')],check=True,capture_output=True,text=True);control=json.loads(pc.stdout);need(control==json.loads((ROOT/'results/positive-control.audit.json').read_text()),'independent control mismatch')
 if a.search:
  exe=a.work/'coordinated_marker';build=subprocess.run([a.cxx,'-O3','-std=c++17',str(ROOT/'code/coordinated_marker.cpp'),'-o',str(exe)],check=True,capture_output=True,text=True);(a.work/'compiler.log').write_text(build.stdout+build.stderr)
  test=subprocess.run([str(exe),str(ROOT/'inputs/positive-control.txt'),str(ROOT/'inputs/positive-control.pairs.txt'),'8'],check=True,capture_output=True,text=True);(a.work/'positive-control.log').write_text(test.stdout);need('HIT 1 2 0 -1 3 4 0 0 5 6 cases 32' in test.stdout,'synthetic discovery control');need(fields(test.stdout)==fields((ROOT/'results/positive-control.log').read_text()),'synthetic count mismatch')
  for name,item in meta.items():
   run=subprocess.run([str(exe),str(a.work/(name+'.input.txt')),str(a.work/(name+'.pairs.txt')),str(item['cap'])],check=True,capture_output=True,text=True);(a.work/(name+'.search.log')).write_text(run.stdout);need(fields(run.stdout)=={k:item[k]for k in ['radius','cap','families','attempts','first_case_passes','hits']},'replayed search mismatch');print(name,fields(run.stdout),flush=True)
 receipt=dict(status='PASS',independent_invariants=reports,positive_control=control,regenerated=a.regenerate,search_replayed=a.search,total_complete_assignments=sum(v['attempts']for v in meta.values()),search_source_sha256=digest((ROOT/'code/coordinated_marker.cpp').read_bytes()))
 (a.work/'result.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items()if k!='independent_invariants'},indent=2))
if __name__=='__main__':main()
