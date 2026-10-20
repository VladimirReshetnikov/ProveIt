from pathlib import Path
import json,sys
sys.path.insert(0,str(Path(__file__).parent))
from inv_fold import load,invariant
from sim_fold import run
# Set PYTHONPATH to the pinned K221 portable directory; see README.md.
import source_language as s,build221 as b
ROOT=Path('/workspace/scratch/32bd1523fdcd/baseline219/K219_Construction_2026-10-20/machine')
T,st=load(ROOT/'k219.native.tm');rr=json.loads((ROOT/'sites219.json').read_text());tree=s.tree(rr)
gg,pp=b.decoder_map({k:(w,1 if d=='R'else -1,z)for k,(w,d,z)in T.items()},tree)
inv=invariant(T,st,10)
for q,paths in pp.items():
 bits={}
 for p in paths:
  for code,op,arg in rr:
   if not code.startswith(p):continue
   tape={j:int((code+'0'*20)[len(p)+j])if len(p)+j>=0 else int(len(p)+j==-1)for j in range(-10,11)}
   bits=tape if not bits else{o:v for o,v in bits.items()if tape[o]==v}
 inv[q]=bits
Q=sorted({q for q,c in T});hits=[]
for a in Q:
 if a not in inv:continue
 for d in Q:
  if a==d or d not in inv:continue
  same=[c for c in(0,1)if T[a,c]==T[d,c]]
  if len(same)!=1:continue
  if not any(o in inv[d]and inv[d][o]!=v for o,v in inv[a].items()):continue
  c=1-same[0];M={k:(w,m,a if z==d else z)for k,(w,m,z)in T.items()if k[0]!=d};goals=[]
  for q in(a,d):
   tape={**inv[q],0:c};w,m,z=T[q,c]
   goals.append((tape,(a if z==d else z,1 if m=='R'else -1,{**tape,0:w})))
  for w in(0,1):
   for m in('L','R'):
    for z in Q:
     if z==d:continue
     M[a,c]=(w,m,z)
     times=[run(M,a,t,0,17,g)for t,g in goals]
     if all(x is not None and x>0 for x in times):
      hit=dict(keep=a,drop=d,read=c,row=[w,m,z],times=times,contexts=[inv[a],inv[d]])
      print('HIT',json.dumps(hit),flush=True);hits.append(hit)
      out=Path('rotations/context_results');out.mkdir(exist_ok=True)
      (out/f'hit{len(hits):03}.tm').write_text('#! start 0\n'+''.join(f'{q} {bit} {ww} {dd} {zz}\n'for(q,bit),(ww,dd,zz)in sorted(M.items())))
      (out/f'hit{len(hits):03}.json').write_text(json.dumps(hit,indent=2))
print('DONE',len(hits))
