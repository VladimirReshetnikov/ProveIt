"""Exact all-natural whole-frame return synthesis; no received code imports."""
import sys,json,time,signal
from collections import Counter
import direct_screen as D
sys.path.insert(0,str(D.D.parent/'k223_merged_runtime_audit/runtime'));import symbolic_runtime as S
CAP=1_000_000;LIMIT=512;counts=Counter();current=None
mp={int(q):v for q,v in json.load(open(D.D/'NATIVE_TO_LEGACY.json')).items()};iv={v:q for q,v in mp.items()};N=D.table(D.BASE/'k219.native.tm');T={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in N.items()};lemmas,blocks=S.prove_blocks(T)
frames=json.load(open(D.D/'RETURN_FULL_CONTRACTS.json'));pending={(mp[103],1),(mp[113],0)}
assert not any(tuple(e[1][:2])in pending for b in blocks for e in b['trace']if e[0]!='list')
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x

def target(f):
 pc,op,arg=f['site'][1];pos=f['site'][2];values=[S.var(2+i)for i in range(9)]
 if op=='CD':assert not pos;values[arg]=S.ZERO
 phy=[None]*9
 for i,j in enumerate(S.r.PHY):phy[j]=values[i]
 successor,overflow=S.r.inc(S.r.strip(pc,'0',arg if op=='CB' else 1))
 return S.State(96,[S.bit(1),S.BLANK],[S.bit(int(b))for b in successor]+[S.run(0,S.add(S.var(1),S.num(64+overflow-len(successor)))),S.bit(1)]+S.file_bits(phy)).key()

def run(table,f,goal,other=None):
 state=S.State(f['state'],tup(f['left']),tup(f['right']),f['direction']);clock=motion=S.ZERO;trace=[];seen=set()
 for k in range(LIMIT):
  key=state.key()
  if k and key==goal:
   assert S.nonnegative(clock)and clock[0]>0
   return dict(clock=clock,motion=motion,steps=k,trace=trace)
  sk=repr(key)
  if sk in seen:raise RuntimeError('exact symbolic cycle')
  seen.add(sk)
  if state.q==mp[302]:raise RuntimeError('deleted302entered')
  src=state.right if state.direction==1 else state.left
  if other and state.q==other[0]and src and src[0][0]=='run'and src[0][1]==other[1]:raise RuntimeError('otherpendingrow')
  counts['symbolic_rules']+=1
  if counts['symbolic_rules']>CAP:raise TimeoutError('1m symbolicrules')
  clock,motion,event=state.step(table,lemmas,clock,motion);trace.append(event)
 raise RuntimeError('percase512rulecap')

def old_run(f,g):
 state=S.State(f['state'],tup(f['left']),tup(f['right']),f['direction']);clock=motion=S.ZERO
 for k in range(LIMIT):
  if k and state.key()==g:return dict(clock=clock,motion=motion,steps=k)
  clock,motion,_=state.step(T,lemmas,clock,motion)
 raise AssertionError('Old continuation failed')

def main():
 global current
 start=time.monotonic();signal.signal(signal.SIGALRM,lambda*a:(_ for _ in()).throw(TimeoutError('90secondcap')));signal.alarm(90);out=[];status='COMPLETE_WHOLE_FRAME_RETURN_ACTION_SCREEN';cache={};Q=sorted({q for q,b in N}-{302})
 try:
  for nq,bit,priority in[(103,1,[4597,4717]),(113,0,[4571,0])]:
   row=mp[nq],bit;other=next(r for r in pending if r!=row);group=[f for f in frames if f['state']==row[0]];group.sort(key=lambda f:(priority.index(f['site'][0])if f['site'][0]in priority else len(priority),f['site'][0]));opts=[];reasons=Counter();maxpassed=0;near=[]
   for w,d in[(0,-1),(0,1),(1,-1),(1,1)]:
    for z in Q:
     counts['actions']+=1;current=dict(row=[nq,bit],action=[w,d,z]);U={r:a for r,a in T.items()if r[0]!=mp[302]};U[row]=(w,d,mp[z]);proof=[]
     try:
      for f in group:
       fi=f['first_case']
       if fi not in cache:g=target(f);cache[fi]=g,old_run(f,g)
       g,old=cache[fi];a=run(U,f,g,other);assert a['motion']==old['motion'],('motion',a['motion'],old['motion']);proof.append(dict(case=fi,index=f['site'][0],old=old,new=a))
     except (AssertionError,RuntimeError,KeyError)as e:
      reasons[str(e).split('(')[0][:80]]+=1
      if len(proof)>maxpassed:maxpassed=len(proof);near=[dict(action=current,passed=maxpassed,error=repr(e))]
      elif len(proof)==maxpassed and len(near)<10:near.append(dict(action=current,passed=maxpassed,error=repr(e)))
     else:opts.append(dict(action=[w,d,z],proof=proof));print('OPTION',current,'fullcases',len(proof),flush=True)
   out.append(dict(row=[nq,bit],cases=len(group),options=opts,rejections=dict(reasons),max_passed=maxpassed,near=near));print('ROW',nq,'options',len(opts),'maxpassed',maxpassed,'rules',counts['symbolic_rules'],flush=True)
 except TimeoutError as e:status='INCOMPLETE_CAP';current=dict(current=current,error=str(e))
 finally:
  signal.alarm(0);r=dict(status=status,outcomes=out,counts=dict(counts),current=current,seconds=time.monotonic()-start,per_case_cap=LIMIT,total_rule_cap=CAP);D.dump('FULL_RETURN_SYNTHESIS_RESULT.json',r);print(status,dict(counts),time.monotonic()-start,flush=True)
if __name__=='__main__':main()
