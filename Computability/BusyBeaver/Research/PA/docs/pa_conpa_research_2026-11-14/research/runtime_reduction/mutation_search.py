#!/usr/bin/env python3
"""Heuristic neutral-row plus quotient search. Hits require fresh proof."""
import argparse,concurrent.futures,json,pathlib,re,subprocess,time,tempfile
p=argparse.ArgumentParser();p.add_argument('candidate');p.add_argument('--candidate-root',type=pathlib.Path);p.add_argument('--output-directory',type=pathlib.Path);p.add_argument('--workers',type=int,default=4);a=p.parse_args()
root=pathlib.Path(__file__).resolve().parent
src=(a.candidate_root or root.parents[1]/'machines')/a.candidate
out=a.output_directory or root/'replay'/(a.candidate+'_neutral_quotient4');out.mkdir(parents=True,exist_ok=True)
temporary=tempfile.TemporaryDirectory(prefix='pa194-neutral-quotient-');merger=pathlib.Path(temporary.name)/'joint_return_merge'
subprocess.run(['g++','-std=c++17','-O3',str(root/'inherited/src/joint_return_merge.cpp'),'-o',str(merger)],check=True)
base={}
for line in (src/'machine.native.tm').read_text().splitlines():
 if not line.strip() or line.startswith('#'):continue
 q,b,w,d,n=line.split();base[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
edits=[json.loads(l) for l in (root/(a.candidate+'_neutral4.jsonl')).read_text().splitlines() if l.strip()]
start=time.monotonic()
def run(item):
 i,e=item;t=dict(base);t[e['state'],e['read']]=tuple(e['new'])
 table=out/f'mutant_{i}.tm';table.write_text(''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {n}\n' for (q,b),(w,d,n) in sorted(t.items())))
 r=subprocess.run([str(merger),str(table),'4','100',str(root/(a.candidate+'_frozen_contexts4.txt'))],capture_output=True,text=True,check=True,timeout=300)
 hits=[json.loads(l) for l in r.stdout.splitlines() if l.strip()]
 (out/f'mutant_{i}.log').write_text(r.stderr)
 if hits:(out/f'mutant_{i}_hits.json').write_text(json.dumps(hits,indent=2)+'\n')
 else:table.unlink()
 m=re.search(r'DONE pairs (\d+) trials (\d+) combos (\d+) hits (\d+) seconds (.+)',r.stderr);assert m
 return {'edit_index':i,'edit':e,'pairs':int(m[1]),'trials':int(m[2]),'combinations':int(m[3]),'hits':hits,'seconds':float(m[5])}
results=[]
with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as pool:
 for r in pool.map(run,enumerate(edits)):
  results.append(r)
  if r['hits']:print('HIT',json.dumps(r),flush=True)
  if len(results)%20==0:print('progress',len(results),'/',len(edits),round(time.monotonic()-start,1),flush=True)
receipt={'candidate':a.candidate,'radius':4,'detour_bound':100,'edits':len(edits),'tested_pairs':sum(r['pairs'] for r in results),'trials':sum(r['trials'] for r in results),'combinations':sum(r['combinations'] for r in results),'hit_count':sum(len(r['hits']) for r in results),'seconds':time.monotonic()-start,'results':results,'scope':'Heuristic screening with original contexts reused after neutral rewrite; no independent simultaneous correctness claim. Every hit needs fresh source verification and full blank startup.'}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k!='results'}),flush=True)

temporary.cleanup()
