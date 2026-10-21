#!/usr/bin/env python3
"""Owned independent verifier of a guarded 180-role decoder contract graph.
Parses literal Lean data, does not execute the incoming decoder checker.
"""
from pathlib import Path
import collections,hashlib,itertools,json,copy
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import symbolic_owned as a
ROOT=Path(__file__).resolve().parent
if not __debug__:raise SystemExit('Assertions must be enabled')
T=a.table_def(a.read('KTable215.lean'),'table215','\ndef tm215')
def M(q,b):return T[q][b] if q<len(T) else None
def mapq(q):return {301:102,302:120,254:230}.get(q,q)
def local(q,suffix,b,limit=8):
 tape={i-len(suffix):int(v) for i,v in enumerate(suffix)};tape[0]=b
 old=tape.copy();head=0;trace=[]
 for _ in range(limit):
  if head==1:
   assert tape==old
   return q,trace
  assert head in tape
  row=M(q,tape[head]);assert row is not None
  w,right,n=row;trace.append([q,head,tape[head],int(w),1 if right else -1,n])
  tape[head]=int(w);head+=1 if right else -1;q=n
 raise AssertionError('local bound exhausted')
def gen():
 old=json.loads(a.read('decoder_context_certificate.json'))
 source=a.sites();aliases={'CI':'inc','CD':'decnz','CB':'brk','CC':'cont','CH':'halt'}
 raw=json.loads(a.read('sites215.json'))
 assert [(''.join(str(int(b))for b in p),k,r) for p,(k,r) in source]==[(p,aliases[k],r)for p,k,r in raw]
 keys=list(dict.fromkeys((r['node'],mapq(r['state']))for r in old['roles']));index={x:i for i,x in enumerate(keys)}
 roles=[{'node':n,'state':q,'guards':[],'edges':None}for n,q in keys]
 for r in old['roles']:
  dst=roles[index[r['node'],mapq(r['state'])]];dst['guards'].append(r['suffix']);edges=[]
  for b,e in enumerate(r['edges']):
   if e['kind']=='primitive':edges.append({'kind':'primitive','node':e['node'],'action':[e['action'][0],e['action'][1],mapq(e['action'][2])]})
   else:
    rr=old['roles'][e['role']];edges.append({'kind':'internal','role':index[rr['node'],mapq(rr['state'])]})
  if dst['edges'] is None:dst['edges']=edges
  else:assert dst['edges']==edges
 for r in roles:r['guards']=sorted(set(r['guards']))
 contracts=[];intern={}
 for r in roles:
  for b,e in enumerate(r['edges']):
   if e['kind']!='internal':continue
   e['contracts']={}
   for suffix in r['guards']:
    z,tr=local(r['state'],suffix,b);back=-min(t[1]for t in tr)
    guard=suffix[-back:] if back else ''
    key=(r['state'],b,guard,z,len(tr))
    if key not in intern:
     intern[key]=len(contracts);contracts.append({'state':r['state'],'bit':b,'guard':guard,'exit':z,'steps':len(tr)})
    e['contracts'][suffix]=intern[key]
 return {'format' :'guarded-decoder-v2','nodes':old['nodes'],'root_node':old['source_root'],'root_role':index[old['roles'][old['root_role']]['node'],84],'roles':roles,'contracts':contracts}
def check(c):
 assert c['format']=='guarded-decoder-v2'
 nodes=c['nodes'];roles=c['roles'];root=c['root_role']
 def idx(i,x):assert type(i)is int and 0<=i<len(x)
 idx(c['root_node'],nodes);idx(root,roles)
 for i,n in enumerate(nodes):
  assert type(n)is list and len(n)==2
  if type(n[0])is str:assert n[0]in ('CI','CD','CB','CC','CH') and (n[1]is None if n[0]=='CH' else type(n[1])is int and n[1]>=0)
  else:assert all(type(x)is int and 0<=x<i for x in n)
 aliases={'CI':'inc','CD':'decnz','CB':'brk','CC':'cont','CH':'halt'}
 expanded=[]
 def expand(i,p):
  n=nodes[i]
  if type(n[0])is str:expanded.append((p,(aliases[n[0]],n[1])))
  else:expand(n[0],p+(False,));expand(n[1],p+(True,))
 expand(c['root_node'],());assert expanded==a.sites()
 assert len({(r['node'],r['state'])for r in roles})==len(roles)
 assert (roles[root]['node'],roles[root]['state'],roles[root]['guards'])==(c['root_node'],84,['1'])
 contracts=c['contracts'];tracekeys=set();used_contracts=set()
 for lc in contracts:
  assert type(lc['state'])is int and type(lc['bit'])is int and lc['bit']in(0,1)
  assert type(lc['guard'])is str and len(lc['guard'])<=2 and set(lc['guard'])<={'0','1'}
  assert type(lc['exit'])is int and type(lc['steps'])is int and 1<=lc['steps']<=7
  q,tr=local(lc['state'],lc['guard'],lc['bit'])
  assert q==lc['exit'] and len(tr)==lc['steps']
  assert tuple(map(tuple,tr))not in tracekeys
  tracekeys.add(tuple(map(tuple,tr)))
 reach={root};todo=[root];nlocal=primitive=expandedlocal=0;simplekeys=set();occ=[]
 for ri in todo:
  r=roles[ri];idx(r['node'],nodes);n=nodes[r['node']]
  assert type(n[0])is int and type(r['state'])is int
  assert r['guards'] and len(set(r['guards']))==len(r['guards'])
  assert all(type(g)is str and 1<=len(g)<=2 and set(g)<={'0','1'} for g in r['guards'])
  assert len(r['edges'])==2
  for b,e in enumerate(r['edges']):
   child=nodes[n[b]]
   if e['kind']=='primitive':
    assert type(child[0])is str and e['node']==n[b]
    w,d,z=M(r['state'],b);assert e['action']==[int(w),1 if d else -1,z]
    primitive+=1;continue
   assert e['kind']=='internal' and type(child[0])is int;idx(e['role'],roles)
   dest=roles[e['role']];assert dest['node']==n[b]
   for suffix in r['guards']:
    assert type(suffix)is str and 1<=len(suffix)<=2 and set(suffix)<={'0','1'}
    assert set(e['contracts'])==set(r['guards'])
    ci=e['contracts'][suffix];idx(ci,contracts);lc=contracts[ci];used_contracts.add(ci)
    assert (lc['state'],lc['bit'],lc['exit'])==(r['state'],b,dest['state'])
    assert suffix.endswith(lc['guard']) and (suffix+str(b))[-2:] in dest['guards']
    expandedlocal+=1
   simplekeys.add((r['state'],b,dest['state']));nlocal+=1
   if e['role']not in reach:reach.add(e['role']);todo.append(e['role'])
 assert len(reach)==len(roles) and len(used_contracts)==len(contracts)
 def walk(ri,p):
  r=roles[ri];assert ('1'+p)[-2:]in r['guards'];occ.append(ri)
  for b,e in enumerate(r['edges']):
   if e['kind']=='internal':walk(e['role'],p+str(b))
 walk(root,'')
 # Literal internal traces share proof contracts by (q,b,required suffix) rather than source node.
 mini={}
 for trace in tracekeys:
  q,_,b,*_=trace[0];back=-min(t[1]for t in trace)
  facts={t[1]:t[2]for t in trace if t[1]<0}
  suffix=''.join(str(facts[i])for i in range(-back,0))
  key=(q,b,suffix);assert key not in mini or mini[key]==trace;mini[key]=trace
 return {'status':'PASS_DATA_ONLY_NOT_KERNEL_PROOF','roles':len(roles),'internal_bindings':nlocal,'primitive_bindings':primitive,'guarded_rule_references':expandedlocal,'local_contract_checks':len(contracts),'distinct_local_trace_contracts':len(tracekeys),'unique_state_bit_target':len(simplekeys),'internal_occurrences':len(occ),'local_contract_readback_histogram':dict(collections.Counter(len(k[2])for k in mini))}
def main():
 c=gen();result=check(c);tests={}
 for label,mut in [('root_state',lambda c:c['roles'][c['root_role']].update(state=85)),('root_guard',lambda c:c['roles'][c['root_role']].update(guards=['0'])),('false_index',lambda c:c.update(root_role=True)),('missing_role',lambda c:c['roles'].pop())]:
  d=copy.deepcopy(c);mut(d)
  try:check(d)
  except (AssertionError,IndexError,KeyError,TypeError):tests[label]='rejected'
  else:raise AssertionError(('mutation accepted',label))
 result['negative_controls']=tests
 (ROOT/'decoder_factored_certificate.json').write_text(json.dumps(c,separators=(',',':'))+'\n')
 (ROOT/'decoder_factored_result.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
