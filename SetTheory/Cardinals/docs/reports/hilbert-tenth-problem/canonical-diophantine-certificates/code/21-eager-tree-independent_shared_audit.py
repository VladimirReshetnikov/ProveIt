#!/usr/bin/env python3
"""Independent finite schematic proof verification and graph instantiation.
No generator, compiler, producer verifier, or evaluator is imported.
"""
import copy,hashlib,json
from pathlib import Path
HERE=Path(__file__).resolve().parent
class Arena:
 def __init__(self):self.nodes=[];self.ids={}
 def add(self,*n):
  if n not in self.ids:self.ids[n]=len(self.nodes);self.nodes.append(n)
  return self.ids[n]
 def load(self,nodes):
  out=[]
  for i,n in enumerate(nodes):
   assert n[0] in ('L','S','F','X')
   assert len(n)=={'L':1,'X':1,'S':2,'F':3}[n[0]]
   assert all(type(j)==int and 0<=j<i for j in n[1:])
   out.append(self.add(n[0],*(out[j] for j in n[1:])))
  return out

def proof(data):
 arena=Arena();ids=arena.load(data['nodes']);names={k:ids[v] for k,v in data['names'].items()}
 L=arena.add('L');I=arena.add('F',arena.add('S',L),arena.add('S',L));X=arena.add('X')
 assert names['L']==L and names['I']==I and names['X']==X
 assert names['SX']==arena.add('S',X) and names['SSX']==arena.add('S',names['SX'])
 literal=json.loads((HERE/'shared_compression_program.json').read_text());li=arena.load(literal['nodes'])
 assert li[literal['root']]==names['R']
 assert len(data['cases'])==3 and {c['name'] for c in data['cases']}=={'base0','base1','step'}
 results={};graphdata={}
 for case in data['cases']:
  rows=case['rows'];memo={};active=set();oracles=[]
  def visit(i):
   assert type(i)==int and 0<=i<len(rows)
   assert i not in active,'selected cycle'
   if i in memo:return memo[i]
   active.add(i);r=rows[i]
   assert type(r['oracle'])==bool
   assert all(type(r[k])==int and 0<=r[k]<len(ids) for k in ('x','y','z'))
   x,y,z=(ids[r[k]] for k in ('x','y','z'))
   assert type(r['premises'])==list
   if r['oracle']:
    oracles.append(i)
    assert case['name']=='step' and not r['premises'] and (x,y,z)==(names['R'],names['SX'],I)
    cost=(1,0)
   else:
    children=[visit(j) for j in r['premises']]
    n=arena.nodes[x]
    if n[0]=='L':assert not children and z==arena.add('S',y)
    elif n[0]=='S':assert not children and z==arena.add('F',n[1],y)
    else:
     assert n[0]=='F';left,right=n[1:];m=arena.nodes[left]
     if m[0]=='L':assert not children and z==right
     elif m[0]=='S':
      assert len(children)==3
      p,q,w=children
      assert (p[0],p[1])==(right,y) and (q[0],q[1])==(m[1],y) and w[:3]==(p[2],q[2],z)
     else:
      assert m[0]=='F' and len(children)==2
      p,q=children
      assert (p[0],p[1])==(y,m[1]) and q[:3]==(p[2],m[2],z)
    cost=(sum(c[3][0] for c in children),1+sum(c[3][1] for c in children))
   assert tuple(r['cost'])==cost
   active.remove(i);memo[i]=(x,y,z,cost);return memo[i]
  root=visit(0);reachable=len(memo)
  for i in range(len(rows)):visit(i)
  if case['name']=='step':assert len(oracles)==1 and root==(names['R'],names['SSX'],I,(2,468))
  elif case['name']=='base0':assert not oracles and root==(names['R'],L,I,(0,94))
  else:assert not oracles and root==(names['R'],arena.add('S',L),I,(0,656))
  results[case['name']]={'rows':len(rows),'root_reachable_rows':reachable,'unique_symbolic_input_pairs':len({m[:2] for m in memo.values()}),'computed_root_cost':root[3]}
  graphdata[case['name']]=(rows,memo)
 # Independent upper/lower bit coefficients, with no numeric scalar expansion.
 bds=[];lower=[]
 for n in arena.nodes:
  if n[0]=='L':ab=(0,0);lo=0
  elif n[0]=='X':ab=(1,0);lo=None
  elif n[0]=='S':
   a,b=bds[n[1]];ab=(a,b+1);lo=None if lower[n[1]] is None else lower[n[1]]+1
  else:
   ab=(2*max(bds[j][0] for j in n[1:]),2*max(bds[j][1] for j in n[1:])+3)
   lo=None if any(lower[j] is None for j in n[1:]) else max(2,2*max(lower[j] for j in n[1:])-1)
  bds.append(ab);lower.append(lo)
 for name,(_,memo) in graphdata.items():
  used=[j for m in memo.values() for j in m[:3]]
  results[name]['bit_bound_coefficients']=(max(bds[j][0] for j in used),max(bds[j][1] for j in used))
 return arena,names,results,graphdata,lower[names['R']],bds[names['R']][1]

def main():
 raw=(HERE/'shared_symbolic_proofs.json').read_bytes();data=json.loads(raw)
 arena,names,results,graphs,lo,hi=proof(data)
 assert results['base0']['root_reachable_rows']==44 and results['base0']['unique_symbolic_input_pairs']==44
 assert results['step']['computed_root_cost']==(2,468)
 assert results['step']['bit_bound_coefficients']==(64,4688954427625)
 # Check that independent symbolic instantiation/composition really aligns the
 # oracle with the preceding root, and recompute resulting ordinary graph costs.
 L=names['L'];I=names['I'];R=names['R'];value=L
 allrows=[];levels=[]
 for level in range(8):
  if level<2:case=data['cases'][next(i for i,c in enumerate(data['cases']) if c['name']==f'base{level}')];subst=None;allrows=[]
  else:case=next(c for c in data['cases'] if c['name']=='step');subst=L
  if level>=2:
   for _ in range(level-2):subst=arena.add('S',subst)
  ren=[]
  for n in data['nodes']:
   ren.append(subst if n[0]=='X' and subst is not None else arena.add(n[0],*(ren[j] for j in n[1:])))
  rootold=0 if allrows else None;maprow={};offset=len(allrows)
  if level>=2:
   oracle=next(i for i,r in enumerate(case['rows']) if r['oracle'])
   rr=case['rows'][oracle]
   assert (ren[rr['x']],ren[rr['y']],ren[rr['z']])==allrows[0][:3]
   maprow[oracle]=0
  for i,r in enumerate(case['rows']):
   if i not in maprow:maprow[i]=offset;offset+=1
  new=[None]*(offset-len(allrows))
  for i,r in enumerate(case['rows']):
   if r['oracle']:continue
   ix=maprow[i]-len(allrows)
   new[ix]=(ren[r['x']],ren[r['y']],ren[r['z']],[maprow[j] for j in r['premises']])
  allrows+=new
  root=maprow[0]
  # Move root to 0 for next composition, permuting every pointer consistently.
  perm=[root]+[i for i in range(len(allrows)) if i!=root];inverse={old:i for i,old in enumerate(perm)}
  allrows=[(*allrows[i][:3],[inverse[j] for j in allrows[i][3]]) for i in perm]
  memo={};active=set()
  def count(i):
   assert i not in active
   if i in memo:return memo[i]
   active.add(i);h=1+sum(count(j) for j in allrows[i][3]);active.remove(i);memo[i]=h;return h
  h=count(0)
  assert h==562*2**level-468
  assert len(allrows)==(44 if level==0 else 149*level+30)
  levels.append({'n':level,'composed_rows':len(allrows),'computed_unfolded_cost':h})
 # Adversarial edits against the independent checker.
 bad=copy.deepcopy(data);next(c for c in bad['cases'] if c['name']=='step')['rows'][0]['cost'][0]=1
 try:proof(bad)
 except AssertionError:pass
 else:raise AssertionError('missed multiplicity edit')
 bad=copy.deepcopy(data);step=next(c for c in bad['cases'] if c['name']=='step');ora=next(r for r in step['rows'] if r['oracle']);ora['y']=bad['names']['SSX']
 try:proof(bad)
 except AssertionError:pass
 else:raise AssertionError('missed wrong induction premise')
 result={'status':'independent symbolic-rule, DFS-acyclicity, affine-cost, template-bound and graph-composition checks passed','cases':results,'program_bits_lower':lo,'program_bits_upper':hi,'composed_levels':levels,'adversarial_mutations_rejected':2,'symbolic_sha256':hashlib.sha256(raw).hexdigest()}
 (HERE/'independent_shared_receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
