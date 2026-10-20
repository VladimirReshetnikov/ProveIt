"""Own finite replay of seven explicit interface obstructions on the six new layouts; no supplied imports."""
from pathlib import Path
import hashlib,json
HERE=Path(__file__).resolve().parent
PKT=Path('/tmp/zfc-intake187/K219_Alternatives_2026-10-20/K219_Alternatives_2026-10-20')
FAIL=Path('/tmp/zfc-intake187/research218_encoding_supplement_latex/replay/research218_encoding')
PHY=(6,2,0,4,3,7,8,5,1)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
 t={}
 for line in p.read_text().splitlines():
  if line and not line.startswith('#'):
   q,b,w,d,z=line.split();key=int(q),int(b);assert key not in t;t[key]=int(w),1 if d=='R'else -1,int(z)
 return t

def frame(pc,regs,spares,gap):
 physical=[0]*9
 for i,j in enumerate(PHY):physical[j]=regs[i]
 ones={-1,64+gap}|{i for i,b in enumerate(pc)if b=='1'};pos=65+gap
 for n in physical+spares:
  pos+=1;ones.update(range(pos,pos+n+1));pos+=n+1
 return ones

def clean(q,h,ones):
 if q!=84 or h-1 not in ones or any(x<h-1 for x in ones):return False
 candidates=[x for x in ones if x>=h+52]
 if not candidates or min(candidates)<h+64:return False
 pos=min(candidates)+1;last=max(ones);blocks=0
 while pos<=last:
  if pos in ones or pos+1 not in ones:return False
  pos+=1
  while pos in ones:pos+=1
  blocks+=1
 return pos==last+1 and blocks>=10

def step(t,q,h,ones):
 b=int(h in ones);w,d,z=t[q,b]
 if w:ones.add(h)
 else:ones.discard(h)
 return z,h+d,[q,h,b,w,d,z]

def patched(t,action):
 u={k:v for k,v in t.items()if k[0]!=120};u[103,1]=(0,-1,162);u[113,0]=(0,-1,27);u[27,0]=tuple(action)
 assert len(u)==436 and all(z in{q for q,b in u}|{254}for w,d,z in u.values())
 return u

def main():
 wrong=json.loads((FAIL/'COOPERATIVE27_CONCRETE_DIAGNOSIS.json').read_text())['results']
 divergence=[r for r in json.loads((FAIL/'COOPERATIVE27_CAP_CERTIFICATES.json').read_text())['cases']if r['certificate']]
 variants={}
 for n in('zero_terminal','retagged','composed'):
  variants[n]=PKT/f'machine/{n}/k219.native.tm';variants[n+'-row157']=HERE/(n+'-row157')/'table.native.tm'
 out=[];count=0
 for name,p in variants.items():
  t=read(p);rr=[]
  for r in wrong:
   u=patched(t,r['action']);initial=frame('000',[0]*8+[1],[0],0);required=frame('001',[0]*9,[0],1);ones=set(initial);q=84;h=0;trace=[]
   for tick in range(r['steps']):
    assert not(tick and clean(q,h,ones))
    q,h,row=step(u,q,h,ones);trace.append([tick,*row]);count+=1
   assert trace==r['trace'] and q==84 and h==0 and clean(q,h,ones)
   assert ones==set(r['actual']['ones']) and ones!=required
   rr.append({'action':r['action'],'status':'SAME_EXACT_WRONG_FIRST_CLEAN_ENDPOINT','steps':len(trace),'all_trace_rows_identical':True,'initial_ones':sorted(initial),'required_ones':sorted(required),'actual_ones':sorted(ones),'used_rows':sorted({(a[1],a[3])for a in trace})})
  dd=[]
  for r in divergence:
   u=patched(t,r['action']);ones=frame('000',[0]*9,[0],0);q=84;h=0;used=set()
   for tick in range(r['prefix_steps']):
    q,h,row=step(u,q,h,ones);used.add((row[0],row[2]));count+=1;assert not clean(q,h,ones)
   ep=r['prefix_endpoint'];assert(q,h,ones)==(ep['state'],ep['head'],set(ep['ones']))
   assert q==27 and h<0 and all(x>h for x in ones)
   initial_h=h;initial=set(ones);period=2 if r['certificate']['kind']=='ONE_WAY_FRESH_BLANK_SWEEP'else 6;trace=[]
   for _ in range(period):q,h,row=step(u,q,h,ones);trace.append(row);count+=1
   assert q==27 and h==initial_h-(2 if period==2 else 4)
   assert all(row[1]<=initial_h for row in trace)and all(x>h for x in ones)
   assert {x for x in ones if x>initial_h}=={x for x in initial if x>initial_h}
   if period==2:assert all(row[2]==0 and row[4]==-1 for row in trace)
   else:
    expected=[(27,0,0,1,-1,66),(66,-1,0,1,1,198),(198,0,1,1,-1,113),(113,-1,1,0,-1,97),(97,-2,0,1,-1,113),(113,-3,0,0,-1,27)]
    assert[(q,h-initial_h,b,w,d,z)for q,h,b,w,d,z in trace]==expected
   dd.append({'action':r['action'],'status':'SAME_EXACT_DIVERGENCE_CERTIFICATE','prefix_steps':r['prefix_steps'],'head':initial_h,'period':period,'shift':h-initial_h,'complete_left_half_blank':True,'period_trace':trace,'prefix_used_rows':sorted(used)})
  out.append({'variant':name,'table_sha256':sha(p),'incoming_return_rows':[[*k,list(v)]for k,v in t.items()if v[2]==120],'wrong_endpoints':rr,'divergence':dd})
 result={'status':'ALL_42_SPECIFIC_OBSTRUCTIONS_PERSIST','variants':out,'literal_steps':count,'inputs':{str(FAIL/n):sha(FAIL/n)for n in['COOPERATIVE27_CONCRETE_DIAGNOSIS.json','COOPERATIVE27_CAP_CERTIFICATES.json']},'source_sha256':sha(Path(__file__)),'scope':'Six 219 layouts, each modified by the fixed return-state120 deletion and caller rerouting. Four concrete invalid primitive endpoints plus three infinite leftward continuation certificates persist on each. No exhaustive 872-action replay or blank-run claim; remaining35 unknown actions remain unknown.'}
 (HERE/'failure-transfer.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k!='variants'},indent=2))
if __name__=='__main__':main()
