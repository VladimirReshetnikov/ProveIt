from pathlib import Path
import sys,json
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'verification'));import symbolic as S
out=Path(__file__).parent;m=S.load_machine();m[125,0]=(0,-1,39);S.check_engine=lambda n:all(n.get(k)==m[k]for k in S.ENGINE_ROWS)
print('contracts',S.verify(m)[0],flush=True);(out/'append_zero196.tm').write_text(''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(m.items())))
q=0;head=0;ones=set();frames=[]
for step in range(1000000):
 if q==75 and head-1 in ones and all(x>=head-1 for x in ones) and head in ones:
  more=sorted(x-head for x in ones if x>head)
  if more and more[0]>=48:
   p=more[0]+1;vs=[]
   while head+p+1 in ones and head+p not in ones:
    p+=1;v=0
    while head+p in ones:v+=1;p+=1
    vs.append(v-1)
   if vs and max(ones)<head+p and len(vs)>=10:
    frames.append({'step':step,'head':head,'gap':more[0]-48,'file':vs})
    if len(frames)<8:print('frame',frames[-1],flush=True)
    if vs[:9]==[0,0,0,0,0,0,2,0,0]:print('STARTUP',frames[-1],flush=True);break
 row=m.get((q,int(head in ones)))
 if row is None:print('HALT',step,q,flush=True);break
 w,d,q=row
 if w:ones.add(head)
 else:ones.discard(head)
 head+=d
else:print('no startup by1m',q,head,len(frames),flush=True)
(out/'append_zero_frames.json').write_text(json.dumps(frames,indent=2))
