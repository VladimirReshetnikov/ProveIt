"""Eight structurally justified old-state51 clones; exact reached-frame diagnostics."""
from pathlib import Path
import argparse,json,hashlib,gzip,time
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args();a.output.mkdir()
P=a.repo/'Computability/BusyBeaver/Research/ZFC/candidate-k218'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
T={}
for line in (P/'k218.native.tm').read_text().splitlines():
 if line and not line.startswith('#'):
  q,b,w,d,z=line.split();T[int(q),int(b)]=(int(w),1 if d=='R'else -1,int(z))
C={k:v for k,v in T.items()if k[0]!=301};C.update({(87,0):(0,1,88),(88,0):(0,-1,51),(51,0):(0,1,122)})
S=json.loads((P/'sites218.json').read_text());by_pc={row[0]:(j,row)for j,row in enumerate(S)}
B=json.loads((P/'evidence/blank-startup.json').read_text());seed=B['final_one_cells'];PHY=[6,2,0,4,3,7,8,5,1]
def frame(h,ones):
 if not ones or min(ones)!=h-1:return None
 headers=[x for x in ones if x>=h+64]
 if not headers:return None
 header=min(headers)
 if any(h+38<=x<header for x in ones):return None
 vals=[];p=header+1;last=max(ones)
 while p<=last:
  if p in ones or p+1 not in ones:return None
  p+=1;n=0
  while p in ones:n+=1;p+=1
  vals.append(n-1)
 if len(vals)<10:return None
 bits=''.join(str(int(h+i in ones))for i in range(38));site=None
 for n in range(1,39):
  if bits[:n]in by_pc:
   site=by_pc[bits[:n]];break
 if site is None or '1'in bits[n:]:return None
 j,row=site
 return {'head':h,'header':header,'gap':header-h-64,'ordinal':j,'site':row,'registers':[vals[x]for x in PHY],'spares':vals[9:],'support':sorted(ones)}
def run(t,label,expected=None):
 q,h,ones=84,-5,set(seed);trace=[];frames=[];changed=[];status='STEP_BOUND'
 for tick in range(30000):
  b=int(h in ones);w,d,z=t[q,b]
  if t[q,b]!=T[q,b]:changed.append({'tick':tick,'state':q,'read':b,'head':h,'action':[w,d,z]})
  trace.append([q,h,b,w,d,z]);ones.add(h)if w else ones.discard(h);q,h=z,h+d
  if q==254:status='HALTED';break
  if q!=84:continue
  f=frame(h,ones)
  if f is None:continue
  f['steps']=tick+1;frames.append(f)
  if expected is not None:
   ref=expected[len(frames)-1]
   if (f['head'],f['support'])!=(ref['head'],ref['support']):status='WRONG_FULL_FRAME';break
  if len(frames)==20:status='TWENTY_MATCHED_FRAMES'if expected is not None else 'BASELINE_TWENTY_FRAMES';break
 with gzip.open(a.output/(label+'.trace.json.gz'),'wt')as out:json.dump(trace,out,separators=(',',':'))
 return {'status':status,'steps':len(trace),'frames':frames,'changed_row_uses':changed,'final_state':q,'final_head':h,'final_support':sorted(ones)}
started=time.monotonic();baseline=run(T,'baseline')
assert len(baseline['frames'])==20
candidates=[q for q,b in sorted(C)if b==1 and C[q,1]==(1,1,q)and q not in(0,36,51)]
assert candidates==[22,25,32,33,48,55,60,64]
results={}
for x in candidates:
 t=dict(C);t[36,0]=(0,1,x);t[x,0]=(0,1,16)
 r=run(t,'clone'+str(x),baseline['frames']);results[str(x)]=r
 print(x,r['status'],r['steps'],len(r['frames']),r['frames'][-1]['ordinal']if r['frames']else None,flush=True)
record={'status':'EIGHT_STRUCTURAL_SCAN_CLONE_DIAGNOSTICS_COMPLETE','scope':'Each replacement X has an exact unary scan contract by its two literal rows. These finite initialized traces test the effect of repurposing X in its preexisting roles; no global runtime or alternative calibration claim.','candidate_states':candidates,'step_cap':30000,'frame_cap':20,'seconds':time.monotonic()-started,'inputs':{str(p):sha(p)for p in [P/'k218.native.tm',P/'sites218.json',P/'evidence/blank-startup.json',Path(__file__)]},'baseline':baseline,'results':results}
(a.output/'results.json').write_text(json.dumps(record,indent=2)+'\n')
