#!/usr/bin/env python3
"""Replay the delivered bounded searches; --full can take many minutes."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile
BASE=Path(__file__).resolve().parent

def need(ok,msg):
 if not ok:raise RuntimeError(msg)
def command(cmd):
 print('+',' '.join(map(str,cmd)),flush=True)
 return subprocess.run(list(map(str,cmd)),cwd=BASE,text=True,stdout=subprocess.PIPE,check=True).stdout

def independent_control():
 parent={}
 for line in(BASE/'controls/offset_control.tm').read_text().splitlines():
  q,b,w,d,t=line.split();parent[int(q),int(b)]=(int(w),1 if d=='R'else -1,int(t))
 child={k:((w,-d,4)if t==3 else(w,d,t))for k,(w,d,t)in parent.items()if k[0]!=3}
 checked=0
 for q in range(6):
  for mask in range(512):
   tape={i-4 for i in range(9)if(mask>>i)&1};original=set(tape)
   w,d,t=parent[q,int(0 in tape)];(tape.add if w else tape.discard)(0)
   goal=(4 if t==3 else t,d+(-2 if t==3 else 0),tape)
   cq,ch,ct=(4 if q==3 else q),(-2 if q==3 else 0),original
   ok=False
   for _ in range(64):
    if cq==6 or not -4<=ch<=4:break
    ww,dd,nn=child[cq,int(ch in ct)];(ct.add if ww else ct.discard)(ch);ch+=dd;cq=nn
    if(cq,ch,ct)==goal:ok=True;break
   need(ok,f'Offset control fails state {q}, window {mask}')
   checked+=1
 def blank(table):
  q=h=n=0;tape=set()
  while q!=6:
   need(n<100,'Control failed to halt')
   w,d,q=table[q,int(h in tape)];(tape.add if w else tape.discard)(h);h+=d;n+=1
  return n,h,sorted(tape)
 p,c=blank(parent),blank(child);need(p==(2,2,[])and c==(4,2,[]),'Blank control mismatch')
 return {'local_obligations':checked,'parent_blank_steps':p[0],'child_blank_steps':c[0],'known_fold':[3,4,-2]}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--full',action='store_true');args=ap.parse_args()
 need(__debug__,'Do not run Python with -O')
 manifest=json.loads((BASE/'manifest.json').read_text())
 for path,digest in manifest.items():
  need(hashlib.sha256((BASE/path).read_bytes()).hexdigest()==digest,'Digest mismatch: '+path)
 print('Input and artifact hashes:',len(manifest))
 with tempfile.TemporaryDirectory(prefix='pa196-replay-')as tmp:
  tmp=Path(tmp)
  for stem,extra in [('offset_folds',[]),('offset_two',[6])]:
   exe=tmp/stem
   command(['g++','-O3','-std=c++17',BASE/'controls'/f'{stem}.cpp','-o',exe])
   data=tmp/f'{stem}.txt'
   receipt=command([exe,BASE/'controls/offset_control.tm',BASE/'controls/offset_control_contexts.txt',data,*extra])
   lines=data.read_text().splitlines()
   need(('3 4 -2'if stem=='offset_folds'else'PLAIN 3 4')in lines,'Expected positive control absent')
   print(receipt.strip())
  print(json.dumps(independent_control(),indent=2))
  if not args.full:return
  source=BASE/'inputs/original.json';original=BASE/'inputs/pa196.tm'
  context_jobs=[
   ['collect_wide_contexts.py',original,58154,tmp/'wide',source,4],
   ['collect_alternative_contexts.py',BASE/'variants/rotated/data/machine.tm',58294,tmp/'rotated'],
   ['collect_alternative_contexts.py',BASE/'variants/macro62/data/machine.tm',58294,tmp/'macro62'],
   ['fast_contexts.py',BASE/'variants/scanner15/machine.tm',BASE/'variants/scanner15/sites.json',58294,tmp/'scanner15']]
  for row in context_jobs:print(command([sys.executable,BASE/row[0],*row[1:]]))
  jobs=[
   ('two_wide_rows.cpp',original,tmp/'wide/source_contexts.txt','wide_two',196),
   ('three_near_misses.cpp',original,BASE/'inputs/source_contexts.txt','three',196),
   ('two_arbitrary_rows.cpp',BASE/'variants/rotated/data/machine.tm',tmp/'rotated/source_contexts.txt','rotated_two',196),
   ('two_arbitrary_rows.cpp',BASE/'variants/macro62/data/machine.tm',tmp/'macro62/source_contexts.txt','macro62_two',196),
   ('offset_folds.cpp',original,tmp/'wide/source_contexts.txt','offset',None),
   ('offset_helper.cpp',original,tmp/'wide/source_contexts.txt','offset_helper',None),
   ('offset_mixed_helper.cpp',original,tmp/'wide/source_contexts.txt','offset_mixed',None),
   ('two_arbitrary_rows.cpp',BASE/'variants/scanner15/machine.tm',tmp/'scanner15/source_contexts.txt','scanner15_two',196)]
  if(BASE/'offset_two_counts.txt').exists():jobs.append(('offset_two.cpp',original,tmp/'wide/source_contexts.txt','offset_two',196))
  executables={}
  for cpp,table,contexts,tag,limit in jobs:
   if cpp not in executables:
    exe=tmp/Path(cpp).stem;command(['g++','-O3','-std=c++17',BASE/cpp,'-o',exe]);executables[cpp]=exe
   out=tmp/f'{tag}_results.txt';argv=[executables[cpp],table,contexts,out]
   if limit is not None:argv.append(limit)
   receipt=command(argv)
   need(receipt==(BASE/f'{tag}_counts.txt').read_text(),'Count mismatch: '+tag)
   need(out.read_bytes()==(BASE/f'{tag}_results.txt').read_bytes(),'Result mismatch: '+tag)
   print(receipt.strip())
 print('All requested reproductions passed.')
if __name__=='__main__':main()
