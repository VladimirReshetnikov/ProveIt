#!/usr/bin/env python3
"""Exact finite premises for the 240 -> 239 guarded block theorem.

The local proof quantifies arbitrary binary exterior tapes. The syntactic
invariant holds at old95 on arbitrary tapes. The additional old169/read1
next-one hypothesis is intentionally separate: it is certified over all
valid instruction frames by certify_guard169.py and checked here on
the complete prescribed old blank prefix. No finite run proves nonhalting.
"""
from pathlib import Path
from collections import Counter
import argparse,hashlib,itertools,json,re,sys
OLD_SHA='547dd69da66f66dd48238a53d34b52a3ce85bb6c7d01534dd1cfb815507f248f'
NEW_SHA='76a9574ac0385b96dbd558fa852a222e1d9025e48e34dc3590384146726d2a9b'

def require(c,m):
 if not c:raise AssertionError(m)

def parse(path):
 raw=path.read_bytes();table={};start=None
 for line in raw.decode('ascii').splitlines():
  if not line:continue
  if line.startswith('#! start '):
   require(start is None,'Duplicate start');start=int(line[9:]);continue
  if line.startswith('#'):continue
  m=re.fullmatch(r'(\d+) ([01]) ([01]) ([LR]) (\d+)',line)
  require(m is not None,('Malformed row',line))
  q,b,w,d,z=m.groups();q,b,w,z=map(int,(q,b,w,z));require((q,b)not in table,'Duplicate row');table[q,b]=(w,1 if d=='R'else-1,z)
 states={q for q,b in table};require(start in states,'Absent start')
 require(set(table)=={(q,b)for q in states for b in(0,1)},'Partial table')
 require({z for w,d,z in table.values()}-states=={254},'Wrong halt')
 return raw,table,start

def phi(q):return 80 if q==169 else q

def inv(q,h,t):
 return ((q!=67 or t[h-1]==0)and(q!=80 or(t[h-1]==1 and t[h-2]==0))and(q!=91 or(t[h-1]==1 and t[h-2]==1 and t[h-3]==0))and(q!=169 or t[h-1]==0))

def local(table,q,t,n):
 t=dict(t);h=0;trace=[]
 for _ in range(n):
  require(h in t,('Unrepresented exterior read',q,h));require(q!=254,'Interior halt')
  b=t[h];w,d,z=table[q,b];trace.append([q,h,b,w,d,z]);t[h]=w;q=z;h+=d
 return(q,h,t),trace

def sparse(table,q,h,t):
 b=int(h in t);w,d,z=table[q,b]
 if w:t.add(h)
 else:t.discard(h)
 return z,h+d

def serialize(table,start):return ('#! start '+str(start)+'\n'+''.join(f'{q} {b} {w} {"R"if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(table.items()))).encode()

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--old',type=Path,required=True);ap.add_argument('--new',type=Path,required=True);ap.add_argument('--output-dir',type=Path,required=True);a=ap.parse_args()
 require(__debug__ and not sys.flags.optimize,'Assertions must be enabled')
 oldraw,old,os=parse(a.old);newraw,new,ns=parse(a.new)
 require(hashlib.sha256(oldraw).hexdigest()==OLD_SHA,'Wrong old table bytes');require(hashlib.sha256(newraw).hexdigest()==NEW_SHA,'Wrong new table bytes')
 require((len(old),len(new),os,ns)==(480,478,95,95),'Convention mismatch')
 expected={(q,b):(w,d,phi(z))for(q,b),(w,d,z)in old.items()if q!=169};expected[80,0]=(0,-1,106);expected[91,1]=(1,-1,167)
 require(new==expected,'Construction mismatch')
 changed={key for key in new if new[key]!=old[key]};require(changed=={(80,0),(91,1),(147,0)},'Wrong changed rows')
 incoming={q:[[p,b,w,d]for(p,b),(w,d,z)in sorted(old.items())if z==q]for q in(67,80,91,169)}
 require(incoming=={67:[[52,0,0,1],[124,0,0,1]],80:[[67,1,1,1]],91:[[80,1,1,1]],169:[[147,0,0,1]]},'Predecessor inventory changed')
 states={q for q,b in old};invchecks=0
 for values in itertools.product((0,1),repeat=9):
  t=dict(zip(range(-4,5),values));require(inv(95,0,t),'Initial invariant')
  for q in states:
   if not inv(q,0,t):continue
   w,d,z=old[q,t[0]];u=dict(t);u[0]=w
   require(inv(z,d,u),('Invariant closure',q,t,z,d));invchecks+=1
 specs=[(80,0,{-1:1},5,[80,106,92,107,125,25]),(169,0,{-1:0},3,[80,106,93,57]),(169,1,{-1:0,1:1},5,[80,91,167,151,173,56]),(91,1,{-3:0,-2:1,-1:1},9,[91,167,151,24,36,54,71,82,94,50])]
 blockrecords=[]
 for q,b,guard,n,path in specs:
  admitted=0;sample=None
  for values in itertools.product((0,1),repeat=5):
   t=dict(zip(range(-3,2),values))
   if t[0]!=b or any(t[x]!=v for x,v in guard.items()):continue
   goal,ot=local(old,q,t,1);actual,nt=local(new,phi(q),t,n)
   mapped_goal=(phi(goal[0]),goal[1],goal[2]);require(actual==mapped_goal,('Block mismatch',q,b,t,ot,nt))
   require([r[0]for r in nt]+[actual[0]]==path,'Path mismatch');admitted+=1;sample={'old':ot,'new':nt}
  require(admitted>0,'Empty guard')
  blockrecords.append({'old_state':q,'read':b,'guard':guard,'old_steps':1,'new_steps':n,'path':path,'finite_assignments':admitted,'footprint':[-3,1],'sample_trace':sample})
 exceptional={(q,b)for q,b,guard,n,path in specs};ordinary=0
 for(q,b),(w,d,z)in old.items():
  if(q,b)in exceptional:continue
  require(new[phi(q),b]==(w,d,phi(z)),('Noncommuting ordinary row',q,b));ordinary+=1
 require(ordinary==476,'Ordinary row census')
 # Compare every checkpoint of the whole prescribed old blank prefix.
 qo=qn=95;ho=hn=0;to=set();tn=set();counts=Counter();newsteps=0;nextone=0
 costs={(q,b):n for q,b,g,n,path in specs}
 for tick in range(409691):
  require((phi(qo),ho,to)==(qn,hn,tn),('Before-block checkpoint',tick))
  key=qo,int(ho in to);n=costs.get(key,1);counts[key]+=1
  if key==(169,1):require(ho+1 in to,('Blank next-one guard',tick));nextone+=1
  qo,ho=sparse(old,qo,ho,to)
  for _ in range(n):qn,hn=sparse(new,qn,hn,tn)
  newsteps+=n
  require((phi(qo),ho,to)==(qn,hn,tn),('After-block checkpoint',tick))
 require((qo,ho,len(to))==(96,-5,351),'Wrong old endpoint');require(newsteps==409835,'Unexpected new clock')
 require(newsteps==409691+4*counts[80,0]+2*counts[169,0]+4*counts[169,1]+8*counts[91,1],'Clock formula')
 newstates={q for q,b in new};order=[95]+sorted(newstates-{95});ren={q:i for i,q in enumerate(order)}|{254:239}
 canonical={(ren[q],b):(w,d,ren[z])for(q,b),(w,d,z)in new.items()};canonraw=serialize(canonical,0)
 a.output_dir.mkdir(parents=True,exist_ok=True);(a.output_dir/'zfc239.tm').write_bytes(canonraw);(a.output_dir/'renumbering.json').write_text(json.dumps({'old_to_canonical':ren,'canonical_to_old':{v:k for k,v in ren.items()}},indent=2)+'\n')
 record={'status':'PASS_EXACT_GUARDED_POSITIVE_BLOCK_CERTIFICATE','old_sha256':OLD_SHA,'new_sha256':NEW_SHA,'canonical_sha256':hashlib.sha256(canonraw).hexdigest(),'working_states':239,'binary_rows':478,'start_old':95,'halt_old':254,'start_canonical':0,'halt_canonical':239,'dispatcher_canonical':ren[96],'deleted_state':169,'retained_rows_changed':[[q,b,list(old[q,b]),list(new[q,b])]for q,b in sorted(changed)],'unchanged_retained_rows':475,'ordinary_commuting_old_rows':ordinary,'syntactic_invariant':{'67':'left0','80':'left1,twoleft0','91':'left1,twoleft1,threeleft0','169':'left0'},'invariant_initial_tape':'arbitrary','invariant_boolean_cases':invchecks,'incoming':incoming,'additional_assumption':'Every old169/read1 configuration has a one immediately to the right. Certified independently over all old valid instruction frames and the exact blank prefix.','blocks':blockrecords,'block_clock_bounds':[1,9],'blank':{'old_steps':409691,'new_steps':newsteps,'exceptional_visits':{f'{q}/{b}':counts[q,b]for q,b in sorted(exceptional)},'next_one_visits':nextone,'all_checkpoints_compared':409692,'state_old':qo,'head':ho,'one_count':len(to),'all_one_positions':sorted(to),'all_other_cells_zero':True},'scope':'Universal finite-footprint local identities and syntactic invariant plus an exact finite initialization. The additional all-runtime next-one premise is supplied by a separate unbounded affine/list certificate; no kernel-checked Lean/Rocq endpoint is claimed.'}
 (a.output_dir/'guarded_fold239_certificate.json').write_text(json.dumps(record,indent=2)+'\n')
 print(json.dumps({k:v for k,v in record.items()if k not in('blocks','blank','incoming')},indent=2));print(json.dumps({k:v for k,v in record['blank'].items()if k!='all_one_positions'},indent=2))
if __name__=='__main__':main()
