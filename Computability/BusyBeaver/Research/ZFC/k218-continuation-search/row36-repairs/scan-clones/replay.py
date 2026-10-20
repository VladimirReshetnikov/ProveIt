"""Independent literal replay and source-effect check for eight scan-clone diagnostics."""
import argparse,gzip,hashlib,json
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--repo',type=Path,required=True);ap.add_argument('--evidence',type=Path,default=Path(__file__).resolve().parent/'evidence');ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
assert not a.output.exists()
P=a.repo/'Computability/BusyBeaver/Research/ZFC/candidate-k218';E=a.evidence
raw=(P/'k218.native.tm').read_bytes();assert hashlib.sha256(raw).hexdigest()=='2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f'
T={}
for line in raw.decode().splitlines():
 if line and not line.startswith('#'):
  q,b,w,d,z=line.split();T[int(q),int(b)]=(int(w),1 if d=='R'else -1,int(z))
D=json.loads(gzip.decompress((E/'results.json.gz').read_bytes()));B=json.loads((P/'evidence/blank-startup.json').read_text());S=json.loads((P/'sites218.json').read_text());PHY=[6,2,0,4,3,7,8,5,1]
assert D['candidate_states']==[22,25,32,33,48,55,60,64]
assert D['step_cap']==30000 and D['frame_cap']==20

def encode(pc,regs,spares,h,gap):
 out={h-1,h+64+gap}|{h+j for j,b in enumerate(pc)if b=='1'};physical=[None]*9
 for r,pos in enumerate(PHY):physical[pos]=regs[r]
 at=h+65+gap
 for v in physical+spares:
  assert v>=0;out.update(range(at+1,at+v+2));at+=v+2
 return out

def inc(pc):
 n=len(pc);v=(int(pc,2)if pc else 0)+1
 return (format(v%(1<<n),f'0{n}b')if n else ''),int(v==(1<<n))
def strip(pc,bit,k):
 for j in range(len(pc)-1,-1,-1):
  if pc[j]==bit:
   k-=1
   if k==0:return pc[:j]
 return ''

def effect(previous):
 pc,op,r=previous['site'];regs=previous['registers'].copy();spares=previous['spares'].copy();gap=previous['gap'];h=previous['head'];overflow=0
 if op=='CI':regs[r]+=1;spares.append(1);pc,overflow=inc(pc)
 elif op=='CD'and regs[r]>0:regs[r]-=1;gap+=1;pc,overflow=inc(pc)
 elif op in('CD','CB'):pc,overflow=inc(strip(pc,'0',1 if op=='CD'else r))
 elif op=='CC':pc=strip(pc,'1',r)
 else:raise AssertionError('Unexpected early halt')
 return h-overflow,encode(pc,regs,spares,h-overflow,gap+overflow)

initial=B['first_well_formed_root_pc_frame'];prev={'site':S[0],'head':B['final_head'],'registers':initial['logical_registers'],'spares':initial['spare_values'],'gap':initial['gap']}
for frame in D['baseline']['frames']:
 eh,eo=effect(prev);assert frame['head']==eh and set(frame['support'])==eo
 assert S[frame['ordinal']]==frame['site'];prev=frame
checks=[];context={};clone33_existing_role=None;bootstrap_endpoints=[]
def prefix(t,n):
 q=h=0;ones=set()
 for _ in range(n):
  w,d,z=t[q,int(h in ones)];ones.add(h)if w else ones.discard(h);q,h=z,h+d
 return q,h,ones
original80=prefix(T,80)
assert original80==(16,6,{-3,-2})
for label,record in [('baseline',D['baseline'])]+[(f'clone{x}',D['results'][str(x)])for x in D['candidate_states']]:
 t=dict(T)
 if label!='baseline':
  x=int(label[5:]);t={k:v for k,v in t.items()if k[0]!=301};t.update({(87,0):(0,1,88),(88,0):(0,-1,51),(51,0):(0,1,122),(36,0):(0,1,x),(x,0):(0,1,16)})
  assert len(t)==434 and t[x,1]==(1,1,x)
  assert prefix(t,80)==original80;bootstrap_endpoints.append(x)
 trace=json.loads(gzip.decompress((E/(label+'.trace.json.gz')).read_bytes()));ones=set(B['final_one_cells']);q,h=84,-5;events=[];frames={f['steps']:f for f in record['frames']}
 for n,row in enumerate(trace):
  assert row[:3]==[q,h,int(h in ones)];w,d,z=t[q,row[2]];assert row[3:]==[w,d,z]
  if t[q,row[2]]!=T[q,row[2]]:events.append({'tick':n,'state':q,'read':row[2],'head':h,'action':[w,d,z]})
  if row[2]==0 and q in D['candidate_states'] and (label,q)not in context:context[label,q]=(n,h,set(ones))
  if label=='clone33'and n==1703:clone33_existing_role=(q,h,set(ones))
  ones.add(h)if w else ones.discard(h);q,h=z,h+d
  if n+1 in frames:
   f=frames[n+1];assert q==84 and h==f['head']and sorted(ones)==f['support']
 assert len(trace)==record['steps']and q==record['final_state']and h==record['final_head']and sorted(ones)==record['final_support']and events==record['changed_row_uses']
 if label!='baseline':
  matches=[(f['head'],f['support'])==(g['head'],g['support'])for f,g in zip(record['frames'],D['baseline']['frames'])]
  if label=='clone64':assert record['status']=='STEP_BOUND'and len(trace)==30000 and all(matches)and len(matches)==2
  else:assert record['status']=='WRONG_FULL_FRAME'and all(matches[:-1])and matches[-1]is False
 checks.append({'name':label,'transitions':len(trace),'complete_frames':len(frames),'status':record['status']})
old=context['baseline',33];new=context['clone33',33]
assert old[:2]==(1703,142)and new[:2]==(461,142)
assert clone33_existing_role==(33,142,old[2])
assert old[2]-new[2]=={-4}and new[2]-old[2]=={-1}
assert {j for j in old[2]if j>=142}=={j for j in new[2]if j>=142}
result={'status':'ALL_LITERAL_TRACES_AND_TWENTY_BASELINE_SOURCE_EFFECTS_PASS','scope':'Independent code, same author; exact finite initialized-source counterexamples, no lower bound or blank behavior theorem for modified clones.','records':checks,'total_transitions':sum(x['transitions']for x in checks),'additional_blank_prefix_transitions':9*80,'all_eight_first_bootstrap_corners_repaired':bootstrap_endpoints,'distant_prefix33':{'old_tick':1703,'new_tick':461,'head':142,'old_only_cells':[-4],'new_only_cells':[-1],'identical_window_radius':142,'entire_right_half_equal':True},'inputs':{str(p):hashlib.sha256(p.read_bytes()).hexdigest()for p in[P/'k218.native.tm',P/'sites218.json',P/'evidence/blank-startup.json',E/'results.json.gz',Path(__file__)]}}
a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in('inputs','records')},indent=2))
