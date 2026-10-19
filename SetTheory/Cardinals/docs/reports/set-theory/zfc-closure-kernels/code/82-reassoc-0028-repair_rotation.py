from pathlib import Path
import sys,json,time,itertools
sys.path.insert(0,str(Path(__file__).resolve().parent));import rotation_candidate as m
HERE=m.HERE
nn={int(k):tuple(v) for k,v in json.loads((HERE/'rotation_candidates/rotation178_source.json').read_text()).items()}
tt={}
for line in (HERE/'rotation_candidates/rotation178.tm').read_text().splitlines():
 if not line or line[0]=='#':continue
 q,b,w,d,t=line.split();tt[int(q),int(b)]=(int(w),d,int(t))

def case_args(p,op,r,zero):
 physical=m.PHYSICAL[r] if op in ('EInc','EDecnz') else r
 branch=(physical,zero) if op=='EDecnz' else None
 if op=='EInc' or op=='EDecnz' and not zero:succ=m.inc(p)
 elif op=='EDecnz':succ=m.inc(m.strip(p,'0',1))
 elif op=='EBreak':succ=m.inc(m.strip(p,'0',r))
 elif op=='EContinue':succ=m.strip(p,'1',r)
 else:succ=''
 effect=('inc',physical) if op=='EInc' else ('dec',physical) if op=='EDecnz' and not zero else None
 gapadd=1 if op=='EDecnz' and not zero else 0
 right=([('r',0,1,41+gapadd),('b',1),('box',('plain',effect))] if succ is None else [('b',int(b)) for b in succ]+[('r',0,1,40+gapadd-len(succ)),('b',1),('box',('plain',effect))])
 return p,branch,m.strict.canon([('b',1)],right),op=='EHalt'

def one(st,c):
 p,branch,target,halt=c
 try:m.strict.run(st,p,branch,target,halt=halt,fuel=2000);return True
 except (AssertionError,KeyError):return False
if __name__=='__main__':
 case=('11101001001010100111000000','EDecnz',1,True)
 cc=case_args(*case)
 st={(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in tt.items()}
 begin=time.monotonic();results=[]
 for entry in [(218,0),(237,0),(154,0),(154,1),(231,0),(23,0)]:
  survivors=[];tested=0
  for act in itertools.product((0,1),('L','R'),sorted({q for q,b in tt}|{254})):
   tested+=1;key=(str(entry[0]),entry[1]);old=st[key];st[key]=(act[0],act[1],str(act[2]))
   ok=one(st,cc);st[key]=old
   if ok:survivors.append(act)
  print('FIRST GATE',entry,'tested',tested,'survivors',len(survivors),survivors,flush=True)
  branches=[]
  for act in survivors:
   cand=dict(tt);cand[entry]=act;r=m.check(cand,nn);branches.append((act,r));print('FULL',entry,act,r,flush=True)
   if r['status']=='PASS':
    fname=HERE/'rotation_candidates'/f'repaired178_{entry[0]}_{entry[1]}_{act[0]}{act[1]}{act[2]}.tm'
    fname.write_text('#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n' for (q,b),(w,d,t) in sorted(cand.items())))
  results.append(dict(entry=entry,tested=tested,survivors=branches,seconds=time.monotonic()-begin))
  (HERE/'rotation_candidates/repair178_results.json').write_text(json.dumps(results,indent=2)+'\n')
