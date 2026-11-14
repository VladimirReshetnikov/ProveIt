#!/usr/bin/env python3
"""Replay bounded reduction searches on PA194NS; no minimality claim."""
from pathlib import Path
from collections import defaultdict
from functools import lru_cache
import argparse, hashlib, importlib.util, itertools, json, subprocess, tempfile

HERE=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read_table(p):
 result={}
 for line in p.read_text().splitlines():
  q,b,w,d,n=line.split();result[int(q),int(b)]=int(w),d=='R',int(n)
 return result

def load():
 spec=importlib.util.spec_from_file_location('reduction_runtime',HERE/'reference/symbolic_runtime.py')
 r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)
 rows=read_table(HERE/'inputs/ncs.native.tm')
 sites=json.loads((HERE/'inputs/sites.json').read_text())
 instructions=json.loads((HERE/'inputs/instructions.json').read_text())
 paths=[tuple(map(int,s[0])) for s in sites];contracts=[]
 for i,code in enumerate(instructions):
  start=r.frame(paths[i]);op=code[0]
  if op=='inc':
   _,reg,n=code;contracts.append((i,None,start,r.canonical(r.frame(paths[n],0,('x','inc',r.PHYSICAL[reg])))))
  elif op=='dec':
   _,reg,z,p=code
   contracts.append((i,(r.PHYSICAL[reg],True),start,r.canonical(r.frame(paths[z]))))
   contracts.append((i,(r.PHYSICAL[reg],False),start,r.canonical(r.frame(paths[p],1,('x','dec',r.PHYSICAL[reg])))))
  elif op=='jump':contracts.append((i,None,start,r.canonical(r.frame(paths[code[1]]))))
  else:assert op=='halt';contracts.append((i,None,start,None))
 return r,rows,sites,contracts

def contexts(out):
 r,rows,sites,contracts=load();K=5;patterns=defaultdict(set);seen=set()
 @lru_cache(maxsize=200000)
 def prefixes(s,k):
  if k==0:return ((),)
  if not s:return ((0,)*k,)
  x,*tail=s;tail=tuple(tail)
  if x[0]=='b':return tuple((x[1],)+p for p in prefixes(tail,k-1))
  if x[0]=='x':return tuple(itertools.product((0,1),repeat=k))
  assert x[0]=='r'
  _,b,a,d=x;assert a>=0 and d>=0
  if a==0:
   if d>=k:return ((b,)*k,)
   return tuple((b,)*d+p for p in prefixes(tail,k-d))
  result=set()
  for n in range(k+1):
   size=a*n+d
   if size>=k:result.add((b,)*k);break
   for p in prefixes(tail,k-size):result.add((b,)*size+p)
  return tuple(result)
 def observe(s):
  q,onl,left,right=s
  if q in r.BOXSTATES:return
  lp=prefixes(left,K+1 if onl else K);rp=prefixes(right,K if onl else K+1)
  key=q,onl,lp,rp
  if key in seen:return
  seen.add(key)
  for a,b in itertools.product(lp,rp):
   tape=tuple(reversed(a[1:]))+(a[0],)+b if onl else tuple(reversed(a))+b
   assert len(tape)==2*K+1
   patterns[q].add(sum(bit<<i for i,bit in enumerate(tape)))
 result=r.validate(rows,contracts,observe=observe);assert result['ok']
 ones=set();q=74;head=0
 for _ in range(57768):
  if q not in r.BOXSTATES:
   patterns[q].add(sum(int(head+i-K in ones)<<i for i in range(2*K+1)))
  w,d,q=rows[q,int(head in ones)];(ones.add if w else ones.discard)(head);head+=1 if d else -1
 assert q==84 and head==-2
 target=out/'contexts-k5.txt'
 target.write_text(''.join(f'{q} {p}\n' for q in sorted(patterns) for p in sorted(patterns[q])))
 assert target.read_bytes()==(HERE/'recorded/contexts-k5.txt').read_bytes()
 receipt={'contracts':result,'symbolic_frame_observations':len(seen),'states':len(patterns),'patterns':sum(map(len,patterns.values())),'radius':5,'startup_steps':57768,'context_sha256':sha(target)}
 (out/'contexts-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 return receipt

def scanner_audit(out):
 r,rows,sites,contracts=load()
 child={(q,b):(w,d,75 if n==34 else n) for (q,b),(w,d,n) in rows.items() if q!=34}
 receipt=r.validate(child,contracts)
 assert not receipt['ok'] and receipt['failed']==(0,(7,True))
 result={'rejected_optimization':'Delete native state 34 and redirect every former target 34 to 75','removed_state_rows':[list(rows[34,b]) for b in(0,1)],'candidate_controls':len(child)//2,'source_contract_check':receipt,'reason':'The seven-zero reset scanner cannot simply be shortened: source site 0 already has address 000000. The modified scanner returns into that address while the register file is still marked.','scope':'Failure of the inherited universal source contract, not a proof that every conceivable 193-state redesign fails.'}
 (out/'scanner-rejection.json').write_text(json.dumps(result,indent=2)+'\n')
 return result

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--output',type=Path)
 ap.add_argument('--derive-contexts',action='store_true',help='Rebuild the conservative windows from all generic source contracts and startup.')
 args=ap.parse_args();out=args.output or Path(tempfile.mkdtemp(prefix='pa194ns-reduction-'))
 out.mkdir(parents=True,exist_ok=True)
 context_result=contexts(out) if args.derive_contexts else None
 runs=[]
 for name in ['action_merge_future','eliminate']:
  binary=out/name
  subprocess.run(['g++','-O3','-std=c++17',str(HERE/f'{name}.cpp'),'-o',str(binary)],check=True)
  specs=[(5,150,HERE/'recorded/contexts-k5.txt')]
  if name=='action_merge_future':specs.insert(0,(4,100,None))
  for radius,bound,ctx in specs:
   tag=f'{name}-r{radius}-b{bound}';cmd=[str(binary),str(HERE/'inputs/ncs.native.tm'),str(radius),str(bound)]
   if ctx is not None:cmd.append(str(ctx))
   with (out/f'{tag}.jsonl').open('w') as log,(out/f'{tag}.log').open('w') as err:
    subprocess.run(cmd,stdout=log,stderr=err,check=True)
   hits=(out/f'{tag}.jsonl').read_text().splitlines();assert not hits
   runs.append({'search':name,'radius':radius,'step_bound':bound,'source_contexts':ctx is not None,'hits':len(hits)})
 result={'native_table_sha256':sha(HERE/'inputs/ncs.native.tm'),'contexts_sha256':sha(HERE/'recorded/contexts-k5.txt'),'runs':runs,'derived_contexts':context_result,'scanner_audit':scanner_audit(out),'interpretation':'No reduction was obtained in these finite search classes. No lower bound on state count is established.'}
 (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));print('Output:',out)

if __name__=='__main__':
 if not __debug__:raise SystemExit('Assertions must be enabled.')
 main()
