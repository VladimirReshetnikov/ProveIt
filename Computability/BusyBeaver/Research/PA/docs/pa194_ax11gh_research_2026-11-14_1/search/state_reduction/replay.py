#!/usr/bin/env python3
"""Reproduce the bounded physical reduction searches offline (C++17 required).

Default: the three primary-table quotient screens. Long suites are explicit.
No search result is a lower bound on arbitrary consistency machines.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse,json,subprocess,shutil
HERE=Path(__file__).resolve().parent

def table(path):
 r={}
 for line in path.read_text().splitlines():
  f=line.split()
  if len(f)!=5 or not f[0].isdigit():continue
  q,b,w,d,n=f;r[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(n))
 return r
def save(path,rows):path.write_text(''.join(f"{q} {b} {w} {'R'if d==1 else'L'} {n}\n"for(q,b),(w,d,n)in sorted(rows.items())))

if __name__=='__main__':
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--suite',choices=['primary','frontier','accelerated-frontier','neutral','bootstrap','new','fast','all'],default='primary')
 ap.add_argument('--out',type=Path,default=HERE/'replayed');ap.add_argument('--workers',type=int,default=4)
 a=ap.parse_args();assert __debug__;a.out.mkdir(parents=True,exist_ok=True)
 binaries={}
 for name in('stutter_merge','stutter_merge_original','stutter_neutral','search_startup'):
  b=a.out/name;subprocess.run(['g++','-O3','-std=c++17',str(HERE/'code'/f'{name}.cpp'),'-o',str(b)],check=True);binaries[name]=b
 ref=HERE/'inputs/reference';tasks=[];notes=[]
 def call(program,args,label):
  out=a.out/(label+'.jsonl');log=a.out/(label+'.log')
  with out.open('w')as f,log.open('w')as g:subprocess.run([str(binaries[program])]+list(map(str,args)),stdout=f,stderr=g,check=True)
  return out,log
 selected={a.suite}if a.suite!='all'else{'primary','frontier','accelerated-frontier','neutral','bootstrap','new','fast'}
 if 'primary'in selected:
  tasks += [('primary_global_k4','stutter_merge_original',[ref/'primary.native.tm',4,20,100,74]),
    ('primary_source_k4','stutter_merge_original',[ref/'primary.native.tm',4,100,100,74,ref/'primary_contexts_k4.txt']),
    ('primary_source_k6','stutter_merge_original',[ref/'primary.native.tm',6,100,200,74,ref/'primary_contexts_k6.txt'])]
 frontier=json.loads((HERE/'inputs/frontier_manifest.json').read_text())
 if 'frontier'in selected:
  for x in frontier:tasks.append((f"frontier_{x['index']:03d}",'stutter_merge',[HERE/x['table'],4,100,100,x['search_start']]))
 if 'accelerated-frontier'in selected:
  for x in frontier:
   label=f"accelerated_{x['index']:03d}";out,_=call('stutter_neutral',[HERE/x['table'],4,100,1,x['search_start']],label+'_edits')
   edits={}
   for line in out.read_text().splitlines():
    e=json.loads(line);key=e['state'],e['read']
    if key not in edits or edits[key]['max_old_steps']<e['max_old_steps']:edits[key]=e
   rows=table(HERE/x['table'])
   for key,e in edits.items():rows[key]=tuple(e['new'])
   generated=a.out/(label+'.tm');save(generated,rows)
   tasks.append((label,'stutter_merge',[generated,4,100,100,x['search_start']]))
 if 'neutral'in selected:
  edits=json.loads((ref/'primary_novel_edits.json').read_text())
  out,_=call('stutter_neutral',[ref/'primary.native.tm',4,100,100,74,ref/'primary_contexts_k4.txt'],'primary_neutral_pool')
  key=lambda x:(x['state'],x['read'],tuple(x['new']))
  present={key(json.loads(s))for s in out.read_text().splitlines()}
  assert all(key(x)in present for x in edits)
  for i,e in enumerate(edits):
   rows=table(ref/'primary.native.tm');rows[e['state'],e['read']]=tuple(e['new'])
   path=a.out/f'neutral_{i:03d}.tm';save(path,rows)
   tasks.append((f'neutral_{i:03d}','stutter_merge_original',[path,4,100,100,74]))
 if 'bootstrap'in selected:
  tasks.append(('runtime193_novel_startups','search_startup',[ref/'runtime193.native.tm',ref/'stutter_novel_neutral193.tsv',200000,0,1000,ref/'startup_any_frame_templates.tsv']))
 if 'new'in selected:
  for name in('PA194AX11GH','PA194AX11GHS'):
   p=HERE/'inputs/new';tasks.append((name+'_global_k4','stutter_merge',[p/f'{name}.native.tm',4,100,100,74]))
   tasks.append((name+'_source_k6','stutter_merge',[p/f'{name}.native.tm',6,100,200,74,p/f'{name}_contexts_k6.txt']))
 if 'fast'in selected:
  for name in('PA194AX11GH','PA194AX11GHS'):
   p=HERE/'inputs/new';tasks.append((name+'F_source_k6','stutter_merge_original',[p/f'{name}F.native.tm',6,100,200,74,p/f'{name}_contexts_k6.txt']))
 def run(x):
  label,program,args=x;out,log=call(program,args,label)
  assert out.read_text().strip()=='',f'New hit in {label}; inspect it instead of accepting the negative ledger.'
  assert 'UNREACHABLE_CONTROL'not in log.read_text(),f'New unreachable-state finding in {label}'
  result=dict(case=label,status='PASS',hits=0,last_log_line=log.read_text().strip().splitlines()[-1])
  print(json.dumps(result),flush=True);return result
 with ThreadPoolExecutor(max_workers=a.workers)as pool:results=list(pool.map(run,tasks))
 (a.out/'receipt.json').write_text(json.dumps(dict(suite=a.suite,searches=len(results),results=results),indent=2)+'\n')
