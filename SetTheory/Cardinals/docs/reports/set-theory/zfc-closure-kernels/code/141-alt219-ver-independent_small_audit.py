#!/usr/bin/env python3
"""Independent release audit: no imports from candidate or certificate code."""
from pathlib import Path
import argparse, hashlib, json

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,v): p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
def read_table(p):
 rows={};starts=[]
 for line in p.read_text().splitlines():
  if line.startswith('#! start '): starts.append(int(line.split()[-1]));continue
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z));assert(q,b)not in rows and b in(0,1)and w in(0,1)and d in('L','R');rows[q,b]=(w,-1 if d=='L'else 1,z)
 assert starts==[0]
 return rows

def cfg(source):
 # Independently use prefix leaf intervals, not a packet tree compiler.
 paths=[r[0]for r in source];assert paths==sorted(paths)and len(set(paths))==len(paths)
 leaves=set(paths);internal={p[:j]for p in paths for j in range(len(p))};assert not leaves&internal
 domain=internal|leaves;assert all(p+c in domain for p in internal for c in'01')
 spans={p:[len(source),-1]for p in internal|leaves}
 for i,p in enumerate(paths):
  for j in range(len(p)+1):
   s=spans[p[:j]];s[0]=min(s[0],i);s[1]=max(s[1],i+1)
 def jump(p,edge,n):
  branches=[p[:j]for j,b in enumerate(p)if b==edge]
  if len(branches)<n:return 0
  s=spans[branches[-n]]
  return s[1]%len(source) if edge=='0'else s[0]
 out=[]
 for i,(p,o,a)in enumerate(source):
  assert o in('CI','CD','CB','CC','CH')
  assert (a is None if o=='CH' else type(a)is int and(a>=1 if o in('CB','CC')else 0<=a<=8))
  out.append([]if o=='CH'else[jump(p,'0',1),(i+1)%len(source)]if o=='CD'else[jump(p,'0',a)]if o=='CB'else[jump(p,'1',a)]if o=='CC'else[(i+1)%len(source)])
 return out

def recover(source):
 nodes={p:(o,a)for p,o,a in source}
 for p in sorted({p[:j]for p,_,_ in source for j in range(len(p))},key=len,reverse=True):nodes[p]=(nodes[p+'0'],nodes[p+'1'])
 return nodes

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--release',type=Path,required=True);ap.add_argument('--baseline',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();a.out.mkdir(parents=True,exist_ok=True)
 old=json.loads((a.baseline/'machine/sites219.json').read_text());assert len(old)==4744
 oldg=cfg(old);oldt=recover(old);baset=read_table(a.baseline/'machine/k219.native.tm');ren={301:102,302:120};base={(ren.get(q,q),b):(w,d,ren.get(z,z))for(q,b),(w,d,z)in baset.items()}
 sources={n:json.loads((a.release/'machine'/n/'sites.json').read_text())for n in('zero_terminal','retagged','composed')};graphs={n:cfg(s)for n,s in sources.items()};tables={};results={}
 for n,s in sources.items():
  p=a.release/'machine'/n/'k219.native.tm';t=read_table(p);tables[n]=t;states={q for q,b in t};assert len(states)==219 and len(t)==438
  assert set(t)=={(q,b)for q in states for b in(0,1)};assert{z for w,d,z in t.values()}-states=={254};assert 254 not in states
  order=[0];mp={0:0}
  for q in order:
   for b in(0,1):
    z=t[q,b][2]
    if z!=254 and z not in mp:mp[z]=len(mp);order.append(z)
  assert set(mp)==states;mp[254]=219
  dense={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in t.items()};raw='#! start 0\n'+''.join(f'{q} {b} {w} {"L"if d==-1 else"R"} {z}\n'for(q,b),(w,d,z)in sorted(dense.items()));(a.out/(n+'.canonical.tm')).write_text(raw)
  steps={'zero_terminal':313845,'retagged':312707,'composed':314043}[n]
  # Whole blank tape: set implementation, independently checked dict implementation.
  ones=set();q=h=0
  for _ in range(steps):
   b=int(h in ones);w,d,q=t[q,b]
   if w:ones.add(h)
   else:ones.discard(h)
   h+=d
  expected={-6,139};pos=140
  for v in[0,0,0,3,0,0,3,0,0]+[1]*130:pos+=1;expected.update(range(pos,pos+v+1));pos+=v+1
  assert(q,h,ones)==(84,-5,expected)
  tape={};state=head=0
  for _ in range(steps):
   w,d,state=dense[state,tape.get(head,0)];tape[head]=w;head+=d
  assert(state,head,{k for k,v in tape.items()if v})==(mp[84],-5,expected)
  assert len(s)==4744
  result=dict(table_sha256=sha(p),source_sha256=sha(a.release/'machine'/n/'sites.json'),states=219,rows=438,all_states_reachable=True,canonical_sha256=hashlib.sha256(raw.encode()).hexdigest(),native_to_canonical=mp,startup_steps=steps,startup_state=q,startup_head=h,startup_one_cells=sorted(ones),all_other_cells_zero=True,independent_tape_simulators_agree=True,source_leaves=len(s),generic_cases=sum(2 if o=='CD'else 1 for p,o,v in s),changed_transition_rows=[[*k,*t[k]]for k in sorted(t)if t[k]!=base[k]])
  results[n]=result
 # All-natural zero-terminal lockstep proof by unique predecessor zero guards.
 zero=sources['zero_terminal'];zg=graphs['zero_terminal'];changed=[]
 for i,(o,n)in enumerate(zip(old,zero)):
  assert o[0]==n[0]
  if o==n:assert oldg[i]==zg[i];continue
  assert o[1:]==['CB',1]and n[1:]==['CD',6]and oldg[i]==zg[i][:1]
  pred=[(j,b)for j,es in enumerate(zg)for b,t in enumerate(es)if t==i]
  assert i!=0 and pred==[(i-2,0)]and zero[i-2][1:]==['CD',6]
  changed.append(i)
 assert changed==[4570,4576,4588,4594,4602,4608,4711,4717]
 # Exact retag ordinal CFG equivalence; same register actions, control tags adjust.
 for left,right in[(old,sources['retagged']),(zero,sources['composed'])]:
  assert cfg(left)==cfg(right)
  differences=[]
  for i,(x,y)in enumerate(zip(left,right)):
   if x[1:]!=y[1:]:assert x[1:]==['CC',2]and y[1:]==['CC',3];differences.append(i)
  assert len(differences)==81
  lt=recover(left);rt=recover(right);A=(('CI',1),('CI',1));before=((A,A),('CC',2));after=(A,(A,('CC',3)));paths=[p for p,n in lt.items()if n==before]
  assert len(paths)==81 and all(rt[p]==after for p in paths)
  # Check the replacement algorithm constructs exactly the right tree.
  def replace(t):return after if t==before else t if isinstance(t[0],str)else(replace(t[0]),replace(t[1]))
  assert replace(lt[''])==rt['']
 # Decomposition of composed into nine zero patches plus three other retag patches.
 zpatch={k:v for k,v in tables['zero_terminal'].items()if v!=base[k]};rpatch={k:v for k,v in tables['retagged'].items()if v!=base[k]};cpatch={k:v for k,v in tables['composed'].items()if v!=base[k]}
 assert len(zpatch)==9 and len(rpatch)==3 and len(cpatch)==12 and not zpatch.keys()&rpatch.keys()
 assert all(cpatch[k]==v for k,v in zpatch.items());assert set(cpatch)-set(zpatch)==set(rpatch)
 assert[(k,rpatch[k],cpatch[k])for k in rpatch if rpatch[k]!=cpatch[k]]==[((139,0),(0,1,99),(0,-1,139))]
 out=dict(status='INDEPENDENT_SMALL_FACTS_PASS',proof_scope='Direct table parse, two whole-blank-tape startup interpreters, independent ordinal source CFG, all-natural zero-guard lockstep, exact retagged source tree replacement, table patch composition. No imports of packet code.',baseline_table_sha256=sha(a.baseline/'machine/k219.native.tm'),baseline_source_sha256=sha(a.baseline/'machine/sites219.json'),zero_guard_ordinals=changed,retag_rotation_count=81,retag_control_ordinals=differences,composed_retag139_zero_row_differs_from_standalone=True,variants=results)
 dump(a.out/'independent_small_facts.json',out);print(json.dumps({k:v for k,v in out.items()if k!='variants'},indent=2));print('VARIANTS',[(n,v['canonical_sha256'],v['startup_steps'])for n,v in results.items()])
if __name__=='__main__':main()
