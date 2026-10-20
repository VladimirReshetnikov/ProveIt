"""Own literal sparse simulation; bounded observations are not inductive invariants."""
from pathlib import Path
import argparse,json,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();a.output.mkdir()
P=a.repo/'Computability/BusyBeaver/Research/ZFC/candidate-k218'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def table(p):
 t={}
 for line in p.read_text().splitlines():
  if line and not line.startswith('#'):
   q,b,w,d,z=line.split();t[int(q),int(b)]=(int(w),1 if d=='R'else -1,int(z))
 assert len(t)==436
 return t
def simulate(t,q,h,ones,steps,selected):
 ones=set(ones);events=[];firsts={};last=[];ray=None
 for tick in range(steps):
  b=int(h in ones)
  if(q,b)in selected:
   event={'tick':tick,'state':q,'read':b,'head':h,'window':''.join(str(int(h+j in ones))for j in range(-16,17)),'left':int(h-1 in ones),'right':int(h+1 in ones),'last_steps':last[-5:]}
   key=f'{q}/{b}/{event["left"]}{event["right"]}'
   if key not in firsts:
    firsts[key]=dict(event,relative_support=sorted(x-h for x in ones))
   events.append({k:v for k,v in event.items()if k!='last_steps'})
  w,d,z=t[q,b]
  if b==0 and z==q and (not ones or (d==1 and h>max(ones))or(d==-1 and h<min(ones))):
   ray={'tick':tick,'state':q,'head':h,'direction':d,'relative_support':sorted(x-h for x in ones)};break
  last.append([tick,q,h,b,w,d,z]);last=last[-5:]
  if w:ones.add(h)
  else:ones.discard(h)
  q,h=z,h+d
  if q==254:break
 return {'steps_executed':tick+1,'end_state':q,'end_head':h,'end_support':sorted(ones),'events':events,'first_contexts':firsts,'zero_ray':ray}
inputs={};results={}
for name,tp,bp in [
 ('primary',P/'k218.native.tm',P/'evidence/blank-startup.json'),
 ('contextual',P/'alternatives/contextual/machine/k218.native.tm',P/'alternatives/contextual/evidence/startup.json')]:
 if not tp.exists():
  print('missing',tp);continue
 t=table(tp);inputs[str(tp)]=sha(tp)
 core={k:v for k,v in t.items()if k[0]!=301};core.update({(87,0):(0,1,88),(88,0):(0,-1,51),(51,0):(0,1,122)})
 results[name+'_core_blank']=simulate(core,0,0,[],1000,{(36,0),(51,0),(122,0)})
 # Record only the complete maintained initialization witness and first source interface.
 if bp.exists():
  boot=json.loads(bp.read_text());inputs[str(bp)]=sha(bp)
  results[name+'_accepted_blank']=simulate(t,0,0,[],boot.get('verified_steps',boot.get('startup',{}).get('steps')),{(36,0),(51,0),(122,0)})
  results[name+'_core_first_interface']=simulate(core,84,-5,boot.get('final_one_cells',boot.get('startup',{}).get('ones')),1242,{(36,0),(51,0),(122,0)})
inputs[str(Path(__file__))]=sha(Path(__file__))
(a.output/'contexts.json').write_text(json.dumps({'scope':'Exact bounded contexts only; no runtime-wide invariant inferred.','inputs':inputs,'results':results},indent=2)+'\n')
for name,r in results.items():
 counts={}
 for e in r['events']:
  k=f'{e["state"]}/{e["read"]}/{e["left"]}{e["right"]}';counts[k]=counts.get(k,0)+1
 print(name,r['steps_executed'],counts,'ray',r['zero_ray'] is not None)
