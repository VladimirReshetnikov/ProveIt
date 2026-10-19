from pathlib import Path
import sys,json,time,itertools
sys.path.insert(0,str(Path(__file__).resolve().parent));import repair_rotation as r
m=r.m
base=dict(r.tt);base[218,0]=(0,'L',245)
entries=[(245,1),(243,1),(244,0),(187,1),(220,1)]
fails=[('11101001001010100111000000','EDecnz',1,True),('11101001001010100010110000','EDecnz',2,True)]
case0=r.case_args(*fails[0]);case1=r.case_args(*fails[1]);results=[];start=time.monotonic()
st={(str(q),b):(w,d,str(t))for(q,b),(w,d,t)in base.items()}
for entry in entries:
 survivors=[];n=0
 for act in itertools.product((0,1),('L','R'),sorted({q for q,b in base}|{254})):
  n+=1;key=str(entry[0]),entry[1];old=st[key];st[key]=(act[0],act[1],str(act[2]))
  ok=r.one(st,case0) and r.one(st,case1);st[key]=old
  if ok:survivors.append(act)
 print('FIRST GATES',entry,n,len(survivors),survivors,flush=True)
 full=[]
 for act in survivors:
  cand=dict(base);cand[entry]=act;ev=m.check(cand,r.nn);full.append([act,ev]);print('FULL',entry,act,ev,flush=True)
  if ev['status']=='PASS':
   p=m.HERE/'rotation_candidates'/f'repaired_two_218L245_{entry[0]}_{entry[1]}_{act[0]}{act[1]}{act[2]}.tm'
   p.write_text('#! start 95\n'+''.join(f'{q} {b} {w} {d} {t}\n'for(q,b),(w,d,t)in sorted(cand.items())))
 results.append(dict(fixed_entry=[218,0],fixed_action=[0,'L',245],entry=entry,tested=n,survivors=full,seconds=time.monotonic()-start))
 (m.HERE/'rotation_candidates/repair_two_rows_results.json').write_text(json.dumps(results,indent=2)+'\n')
