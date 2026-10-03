#!/usr/bin/env python3
"""Inverse-graph folds and one concrete subgroup core; no compiler imports."""
import argparse,hashlib,json
from pathlib import Path
from collections import deque
if not __debug__:raise RuntimeError('Run without -O')
PINS={
'group_projective_shared_macro_automaton.py':'2cbbc82d18e0e175d3c7f44707fdc16c2bf899aaad5deafa44c0975cf0b96bf7',
'group_projective_shared_macro_automaton.json':'284da792cce620169ebca9cae7ee77488b56fe0f68c47cf12059af5d0e980497',
'group_projective_shared_macro_automaton.md':'5933851785599c3c83bbddc28f1dbe2e43c7db17ed256a87a5dd293117bc9eb6',
'group_macro_automaton_sharing.md':'e253a396f999e8045bb1c4ee223602907f8ea003b7b7f3d93218cb425ffd5585',
'group_projective_zero_mortality6.md':'c0f3cb53d8a189dd7b98e0deb892a75e64426e8ac480ee049f945ed09e896bc2',
'group_projective_product_radix_scale.md':'f342dbc1da849a7c74cc7043becad6d218582adeefffa55dec558a28b1e47b39',
'group_projective_tail_quotient_shift.md':'a1e1e67df618f6f809c2e85a409509b288337f62cd1af35cfc6ca950e0efa92a',
}
R=(2,3,6,7);U=(1,5);B=U*5;A=R+B
REFERENCES=['https://arxiv.org/abs/math/0202285','https://web.stevens.edu/algebraic/alexeim/Teaching/GroupTheory626/graph5.pdf']
def need(x,m):
 if not x:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
def inv(a):need(type(a)is int and 1<=a<=8,'physical letter');return a+1 if a%2 else a-1
def inverse(w):return tuple(inv(a) for a in reversed(w))
def reduced(w):
 out=[]
 for a in w:
  if out and out[-1]==inv(a):out.pop()
  else:out.append(a)
 return tuple(out)
def reverse_edge(e):s,t,a=e;return(t,s,inv(a))
def bouquet(words):
 edges=[];nextstate=1
 for w in words:
  need(bool(w),'nonempty generators');v=0
  for i,a in enumerate(w):
   inv(a);target=0 if i==len(w)-1 else nextstate
   if target:nextstate+=1
   edges.append((v,target,a));v=target
 return tuple(edges)
def vertices(edges):return {0}|{v for s,t,a in edges for v in(s,t)}
def inverse_closure(edges):return tuple(sorted(set(edges)|{reverse_edge(e) for e in edges}))
def validate(edges,folded=False):
 need(len(edges)==len(set(edges)),'unique directed arcs');need(all(reverse_edge(e)in edges for e in edges),'inverse pairing')
 if folded:need(len({(s,a) for s,t,a in edges})==len(edges),'folded deterministic inverse graph')
 reached={0};q=deque([0])
 while q:
  v=q.popleft()
  for s,t,a in edges:
   if s==v and t not in reached:reached.add(t);q.append(t)
 need(reached==vertices(edges),'connected based graph')
def fold(edges):
 edges=inverse_closure(edges);validate(edges);trace=[]
 while True:
  choices={}
  for s,t,a in edges:choices.setdefault((s,a),set()).add(t)
  conflicts=[(s,a,sorted(ts)) for (s,a),ts in sorted(choices.items()) if len(ts)>1]
  if not conflicts:break
  s,a,ts=conflicts[0];u,v=ts[:2];keep,drop=min(u,v),max(u,v)
  quotient=lambda z:keep if z==drop else z
  out=tuple(sorted({(quotient(x),quotient(y),b) for x,y,b in edges}))
  connector=((u,s,inv(a)),(s,v,a))
  need(all(e in edges for e in connector) and reduced(e[2] for e in connector)==(),'null connector')
  need(len(out)<len(edges) and len(vertices(out))==len(vertices(edges))-1,'strict finite fold')
  need(all((quotient(x),quotient(y),b)in out for x,y,b in edges),'edge quotient preserves labels')
  trace.append(dict(before=[list(e)for e in edges],after=[list(e)for e in out],source=s,label=a,identified=[u,v],connector=[list(e)for e in connector]))
  validate(out);edges=out
 validate(edges,True);return edges,trace

def canonical(edges):
 validate(edges,True);mapping={0:0};q=deque([0])
 while q:
  v=q.popleft()
  for s,t,a in sorted(edges,key=lambda e:(e[0],e[2],e[1])):
   if s==v and t not in mapping:mapping[t]=len(mapping);q.append(t)
 return tuple(sorted((mapping[s],mapping[t],a)for s,t,a in edges)),mapping

def path(edges,word):
 here=0;walk=[]
 for a in word:
  targets=[e for e in edges if e[0]==here and e[2]==a]
  need(len(targets)==1,'unique requested path');walk.append(targets[0]);here=targets[0][1]
 need(here==0,'based closed path');return walk

def accepts_nfa(edges,word):
 states={0}
 for a in word:states={t for s,t,b in edges if s in states and b==a}
 return 0 in states

def check_walk(edges,walk):
 here=0
 for e in walk:need(e in edges and e[0]==here,'literal lifted walk');here=e[1]
 need(here==0,'lifted based endpoint')

def lift_one(step,walk):
 before=tuple(tuple(e)for e in step['before']);after=tuple(tuple(e)for e in step['after']);check_walk(after,walk)
 u,v=step['identified'];keep,drop=min(u,v),max(u,v);s,a=step['source'],step['label'];q=lambda z:keep if z==drop else z
 result=[];here=0
 def bridge(target):
  nonlocal here
  if here==target:return
  need({here,target}=={u,v},'only identified endpoints need connection')
  result.extend(((here,s,inv(a)),(s,target,a)));here=target
 for x,y,b in walk:
  options=[e for e in before if(q(e[0]),q(e[1]),e[2])==(x,y,b)]
  need(bool(options),'arc preimage');chosen=next((e for e in options if e[0]==here),options[0]);bridge(chosen[0]);result.append(chosen);here=chosen[1]
 bridge(0);check_walk(before,result)
 need(reduced(e[2]for e in result)==reduced(e[2]for e in walk),'exact freely reduced lifted label')
 return result

def spanning_basis(edges):
 validate(edges,True);words={0:()};tree=set();q=deque([0])
 while q:
  v=q.popleft()
  for e in sorted(edges,key=lambda e:(e[0],e[2],e[1])):
   if e[0]==v and e[1]not in words:
    words[e[1]]=words[v]+(e[2],);tree.add(min(e,reverse_edge(e)));q.append(e[1])
 pairs={min(e,reverse_edge(e))for e in edges};basis=[];edge_loops=[]
 for s,t,a in sorted(pairs):
  word=reduced(words[s]+(a,)+inverse(words[t]));edge_loops.append(dict(edge=[s,t,a],word=list(word),tree=(s,t,a)in tree))
  if(s,t,a)in tree:need(word==(),'tree-edge loop cancels')
  else:need(word!=(),'nontrivial chord loop');basis.append(word)
 need(len(tree)==len(vertices(edges))-1,'spanning tree edge count')
 return basis,edge_loops

def mm(a,b):return tuple(tuple(sum(a[i][k]*b[k][j]for k in range(2))for j in range(2))for i in range(2))
def matrix(word):
 I=((1,0),(0,1));blocks=[I,I]
 for a in word:
  block=(a-1)//4;kind=(a-1)%4
  g=(((1,1),(0,1)),((1,-1),(0,1)),((1,0),(1,1)),((1,0),(-1,1)))[kind]
  blocks[block]=mm(g,blocks[block])
 return tuple(blocks)
def typed(a,b):
 if type(a)is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys()and all(typed(a[k],b[k])for k in a)
 if isinstance(a,list):return len(a)==len(b)and all(typed(x,y)for x,y in zip(a,b))
 return a==b

def verify(root):
 for n,h in PINS.items():need(sha((root/n).read_bytes())==h,'pin '+n)
 predecessor=json.loads((root/'group_projective_shared_macro_automaton.json').read_text())
 need(predecessor['status']=='PASS'and predecessor['source_sha256']==PINS['group_projective_shared_macro_automaton.py'],'actual pinned graph predecessor receipt')
 matrices=dict(R=matrix(R),B=matrix(B),A=matrix(A));I=matrix(())
 need(reduced(A+inverse(B))==R and reduced(R+B)==A,'both exact Nielsen word identities')
 need(matrix(A+inverse(B))==matrices['R'],'chronological matrix Nielsen identity')
 need(all(mm(matrices['B'][i],matrices['R'][i])==matrices['A'][i]for i in range(2)),'M_A=M_B*M_R')
 need(matrix(R*6)==I,'matrix image has extra relations beyond the free core')
 cases={};expected=None;lifted=0;lifted_steps=0
 words_cases={'original_four':(A,B,inverse(A),inverse(B)), 'original_two':(A,B), 'nielsen_four':(R,B,inverse(R),inverse(B)), 'nielsen_two':(R,B)}
 for name,words in words_cases.items():
  initial=bouquet(words);closed=inverse_closure(initial);end,trace=fold(initial);canon,mapping=canonical(end)
  if expected is None:expected=canon
  need(canon==expected,'same canonical literal folded graph')
  basis,loops=spanning_basis(end);norm=lambda w:min(tuple(w),inverse(w))
  need({norm(w)for w in basis}=={norm(R),norm(B)},'independent spanning-tree subgroup basis R,B')
  # Lift generator loops, a nontrivial commutator and a backtracking loop
  # through every exact fold trace. All reductions are checked, not sampled.
  tests=(R,B,inverse(R),inverse(B),R+B+inverse(R)+inverse(B),R+inverse(R),A)
  for word in tests:
   walk=path(end,word)
   for step in reversed(trace):walk=lift_one(step,walk);lifted_steps+=1
   check_walk(closed,walk);need(reduced(e[2]for e in walk)==reduced(word),'whole trace label preservation');need(matrix(tuple(e[2]for e in walk))==matrix(word),'whole lifted matrix');lifted+=1
  cases[name]=dict(initial_macro_directed_edges=len(initial),initial_macro_states=len(vertices(initial)),inverse_augmented_directed_edges=len(closed),folds=len(trace),trace=trace,final_edges=[list(e)for e in end],canonical_edges=[list(e)for e in canon],final_states=len(vertices(end)),basis=[list(w)for w in basis],basis_edge_loops=loops)
 original=bouquet(words_cases['original_four']);need(not accepts_nfa(original,R)and accepts_nfa(expected,R),'strict formal language change')
 need(accepts_nfa(original,())and accepts_nfa(expected,()),'empty word convention')
 # Endpoint cannot be reached by an identity matrix, for any u, because the
 # initial first coordinate is1 and the terminal first coordinate is0.
 need(I==(((1,0),(0,1)),((1,0),(0,1))),'literal paired identity')
 need(len(expected)==28 and len(vertices(expected))==13,'exact core sizes')
 need(all(s<32 and t<32 for s,t,a in expected),'state codes fit paid m32')
 need(len({min(e,reverse_edge(e))for e in expected})==14,'undirected edge count')
 need(all(sum(s==v for s,t,a in expected)>=2 for v in vertices(expected)),'core has no leaves')
 return dict(status='PASS',source_sha256=sha(Path(__file__).read_bytes()),pins=PINS,references=REFERENCES,
  physical_inverse_pairs=[[1,2],[3,4],[5,6],[7,8]],codes=dict(R=list(R),U=list(U),B=list(B),A=list(A)),
  cases=cases,core=dict(edges=[list(e)for e in expected],directed_edges=28,undirected_edges=14,states=13,state_codes=list(range(13)),lane_capacity=32,free_rank=2),
  matrices={k:[[list(row)for row in m]for m in v]for k,v in matrices.items()},
  counts=dict(fold_runs=4,fold_steps=sum(c['folds']for c in cases.values()),lifted_loops=lifted,individual_lifts=lifted_steps,spanning_tree_basis_checks=4),
  language_witness=dict(word=list(R),original_macro_star=False,folded_graph=True),
  scope='General evaluated-subgroup theorem and concrete inverse graph only. No complete compiler source, arithmetic-operation improvement, unchanged witness tuple, formal word-language equivalence or numerical universal bound is claimed.')
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path);ap.add_argument('--expect',type=Path);a=ap.parse_args();r=verify(a.root)
 if a.output:a.output.write_text(json.dumps(r,sort_keys=True,indent=2)+'\n')
 if a.expect:need(typed(r,json.loads(a.expect.read_text())),'exact typed saved receipt')
 print(json.dumps(dict(status=r['status'],counts=r['counts'],core=r['core'])))
if __name__=='__main__':main()
