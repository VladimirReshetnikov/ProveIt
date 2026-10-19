from pathlib import Path
import json,sys,time,hashlib
BASE=Path('/workspace/scratch/f8ea30957848/baseline_archives/241_Companion/busybeaver241-companion/runtime')
OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(BASE));import symbolic_runtime as s
sites=json.loads((BASE/'sites_logical.json').read_text())
roots=['11101001001011000011','1110100100101110011','1110100101100011','111110011']
new=[]
for p,op,r in sites:
 if not any(p.startswith(root)for root in roots):new.append([p,op,r])
for p in roots:new.extend([[p+'0','CI',5],[p+'10','CD',6],[p+'11','CC',2]])
new.sort()
T=s.r.table(BASE/'candidate_1_old.tm');T[142,0]=(0,1,72);T[142,1]=(1,1,17)
(OUT/'rotated142_old.tm').write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {t}\n'for(q,b),(w,d,t)in sorted(T.items())))
(OUT/'rotated142_sites.json').write_text(json.dumps(new,indent=2)+'\n')
lem,blocks=s.prove_blocks(T)
modified=[site for site in new if any(site[0].startswith(r)for r in roots)]
for site in modified:
 for pos in([False,True]if site[1]=='CD' else[False]):
  ans=s.case(T,lem,site,pos)
  print('LOCAL_CASE_PASS',site,pos,ans['symbolic_steps'],flush=True)
print('modified pass',len(modified),flush=True)
if '--full' in sys.argv:
 t=time.monotonic();count=0
 for i,site in enumerate(new):
  for pos in([False,True]if site[1]=='CD' else[False]):
   try:ans=s.case(T,lem,site,pos)
   except Exception as e:
    print('FAIL',i,site,pos,str(e));raise
   count+=1
  if i%1000==0:print('FULL',i,count,round(time.monotonic()-t,1),flush=True)
 print('FULL_PASS',count,round(time.monotonic()-t,1),flush=True)
