"""One frozen marker-relay table; finite diagnostics, not a calibration."""
from pathlib import Path
import argparse,json,gzip,hashlib,time
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--mode',choices=('blank','initialized'),required=True);ap.add_argument('--step-bound',type=int,default=2000000);a=ap.parse_args();assert a.step_bound>0;a.output.mkdir()
P=a.repo/'Computability/BusyBeaver/Research/ZFC/candidate-k218'
if not __debug__:raise RuntimeError("Run without -O")
for rel,expected in {'k218.native.tm': '2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f', 'sites218.json': 'b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9', 'evidence/blank-startup.json': 'f12c06d6c252f0a0597d4dae7243e4ff881f76ad7fd740a7230dc3641f54c63f'}.items():
 if hashlib.sha256((P/rel).read_bytes()).hexdigest()!=expected:raise ValueError("Input changed: "+rel)
T={}
for l in(P/'k218.native.tm').read_text().splitlines():
 if l and not l.startswith('#'):
  q,b,w,d,z=l.split();T[int(q),int(b)]=(int(w),1 if d=='R'else-1,int(z))
S=json.loads((P/'sites218.json').read_text());by_pc={r[0]:(i,r)for i,r in enumerate(S)}
B=json.loads((P/'evidence/blank-startup.json').read_text())
BASELINE=Path(__file__).resolve().parent.parent/'row36-repairs/scan-clones/evidence/results.json.gz'
if hashlib.sha256(BASELINE.read_bytes()).hexdigest()!='aa45408940e58227e6787701736bfbbae98161eff970bdf235239356c7b714bd':raise ValueError('Baseline frame evidence changed')
E=json.loads(gzip.decompress(BASELINE.read_bytes()))['baseline']['frames'];PHY=[6,2,0,4,3,7,8,5,1]
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
  if bits[:n]in by_pc:site=by_pc[bits[:n]];break
 if site is None or '1'in bits[n:]:return None
 j,row=site
 return {'head':h,'header':header,'gap':header-h-64,'ordinal':j,'site':row,'registers':[vals[x]for x in PHY],'spares':vals[9:],'support':sorted(ones)}
C={k:v for k,v in T.items()if k[0]!=301};C.update({(87,0):(0,1,88),(88,0):(0,-1,51),(51,0):(0,1,122),(36,0):(1,1,16),(16,1):(1,-1,56)})
D=dict(C)
for x in(42,47,57,126,139,141):
 assert D[x,1]==(0,-1,16);D[x,1]=(0,-1,122)
def run(t,label,blank):
 q,h,O=(0,0,set())if blank else(84,-5,set(B['final_one_cells']));trace=[];frames=[];modified=[];end='STEP_BOUND';bound=a.step_bound
 for tick in range(bound):
  b=int(h in O);w,d,z=t[q,b]
  if t[q,b]!=T[q,b]:modified.append({'tick':tick,'state':q,'read':b,'head':h,'neighbors':[int(h-1 in O),int(h+1 in O)],'action':[w,d,z]})
  trace.append([q,h,b,w,d,z]);O.add(h)if w else O.discard(h);q,h=z,h+d
  if q==254:end='HALT';break
  if q==84:
   f=frame(h,O)
   if f:
    f['steps']=tick+1;frames.append(f)
    if blank:
     if f['ordinal']==0 and all(f['registers'][j]==0 for j in (1,2,3,5,6,7)):
      end='ROOT_SHAPED_FRAME';break
     continue
    e=E[len(frames)-1]
    if f['head']!=e['head']or f['support']!=e['support']:end='WRONG_FULL_FRAME';break
    if len(frames)==20:end='TWENTY_MATCHED_FRAMES';break
 with gzip.open(a.output/(label+'.trace.json.gz'),'wt')as out:json.dump(trace,out,separators=(',',':'))
 return {'status':end,'step_bound':bound,'steps':len(trace),'frames':frames,'modified_uses':modified,'final_state':q,'final_head':h,'final_support':sorted(O)}
R={'scope':'Frozen relay finite diagnostic; no global runtime, bootstrap or calibration theorem.','inputs':{str(p):hashlib.sha256(p.read_bytes()).hexdigest()for p in[P/'k218.native.tm',P/'sites218.json',P/'evidence/blank-startup.json',BASELINE,Path(__file__)]},'tables':{},'results':{}}
for label,t in[('relay16_six_returns',D)]:
 R['tables'][label]={'working_states':len(t)//2,'changes':[[q,b,*z]for(q,b),z in sorted(t.items())if z!=T[q,b]],'deleted_state':301}
 for blank in(a.mode=='blank',):
  name=label+('_blank'if blank else'_initialized');r=run(t,name,blank);R['results'][name]=r
  print(name,r['status'],r['steps'],len(r['frames']),flush=True)
(a.output/'result.json').write_text(json.dumps(R,indent=2)+'\n')
