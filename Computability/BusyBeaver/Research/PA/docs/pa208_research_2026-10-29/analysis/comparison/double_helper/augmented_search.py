"""Construct dedicated-helper 208-state tables and search fresh contextual folds."""
from pathlib import Path
import concurrent.futures, importlib.util, json, subprocess, sys, time
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[3];OUT=Path(__file__).resolve().parent
BASE=ROOT/'upstream/U208_ConPA_History_2026-10-29/U208_ConPA_History_2026-10-29/machine'
spec=importlib.util.spec_from_file_location('fold_checker',ROOT/'analysis/reduction_search/discover_folds.py');D=importlib.util.module_from_spec(spec);spec.loader.exec_module(D)

def encode(t):return '#! start 0\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))

def prepare(label):
 base=BASE/('compatibility_variant'if label=='B'else'');old=D.read_table(base/'u208.native.tm')
 cp=ROOT/'analysis/reduction_search'/('window7b_contexts.json'if label=='B'else'window7_contexts.json')
 contexts=json.loads(cp.read_text())
 if label=='B':contexts['172']=contexts.pop('211')
 helpers=[list(map(int,s.split()))for s in(OUT/f'helpers_extended_{label}.txt').read_text().splitlines()]
 selected=[];seen=set()
 for row in helpers:
  drop,keep,bit,x0,x1,w0,w1=row;k=(tuple(sorted((drop,keep))),bit,x0,x1,w0,w1)
  if k not in seen:seen.add(k);selected.append(row)
 sites=json.loads((base/'sites.json').read_text());tasks=[]
 for drop,keep,bit,x0,x1,w0,w1 in selected:
  d=OUT/f'augmented_{label}_{drop}_{keep}_{x0}_{x1}';d.mkdir(exist_ok=True)
  augmented={**old,(500,0):(w0,1,x0),(500,1):(w1,1,x1)};replacement=bit,bit,-1,500
  cases=[];exact=True;maxsteps=0;reason=None
  for q in(drop,keep):
   for ctx in contexts[str(q)]:
    for read in(0,1):
     branches=D.exact_case(augmented,q,read,dict(ctx),drop,keep,replacement,127,254)
     if branches is None:exact=False;reason={'state':q,'read':read,'context':ctx};break
     maxsteps=max(maxsteps,max((len(b['trace'])for b in branches),default=0))
     cases.append({'state':q,'read':read,'context':ctx,'branches':branches})
    if not exact:break
   if not exact:break
  pi=lambda q:keep if q==drop else q
  nt={(q,b):(w,m,pi(z))for(q,b),(w,m,z)in augmented.items()if q!=drop};nt[keep,bit]=bit,-1,500
  (d/'machine.native.tm').write_text(encode(nt));(d/'sites.tsv').write_text(''.join(f'{p}\t{o}\t{-1 if a is None else a}\n'for p,o,a in sites))
  (d/'local_certificate.json').write_text(json.dumps({'old_table':str(base/'u208.native.tm'),'parameters':[drop,keep,bit,x0,x1,w0,w1],'exact_pass':exact,'maximum_block_steps':maxsteps,'failure':reason,'cases':cases},separators=(',',':'))+'\n')
  rec={'label':label,'directory':str(d.relative_to(ROOT)),'parameters':[drop,keep,bit,x0,x1,w0,w1],'states':len(nt)//2,'exact_local_pass':exact,'maximum_block_steps':maxsteps,'local_failure':reason}
  tasks.append((d,rec))
 return tasks

def run(task):
 d,rec=task
 finite=subprocess.run([str(ROOT/'analysis/comparison/finite_fast'),str(d/'machine.native.tm'),str(d/'sites.tsv')],capture_output=True,text=True)
 rec['finite_runtime_pass']=finite.returncode==0;rec['finite_runtime_output']=finite.stdout+finite.stderr
 if rec['exact_local_pass'] and rec['finite_runtime_pass']:
  window=subprocess.run([str(ROOT/'analysis/reduction_search/window'),str(d/'machine.native.tm'),str(d/'window7.bin'),'7','0'],capture_output=True,text=True)
  (d/'window7.log').write_text(window.stdout+window.stderr);assert window.returncode==0
  folds=subprocess.run([str(ROOT/'analysis/reduction_search/variant_folds'),str(d/'machine.native.tm'),str(d/'window7.bin'),'7'],capture_output=True,text=True)
  (d/'folds.txt').write_text(folds.stdout);(d/'folds.log').write_text(folds.stderr);assert folds.returncode==0
  rec['fresh_fold_survivors']=[list(map(int,s.split()))for s in folds.stdout.splitlines()]
 (d/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec),flush=True);return rec

if __name__=='__main__':
 labels=sys.argv[1:]or['A','B'];tasks=[]
 for label in labels:tasks.extend(prepare(label))
 with concurrent.futures.ThreadPoolExecutor(max_workers=3)as pool:results=list(pool.map(run,tasks))
 (OUT/('augmented_results_'+'_'.join(labels)+'.json')).write_text(json.dumps(results,indent=2)+'\n')
