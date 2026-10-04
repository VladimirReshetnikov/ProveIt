#!/usr/bin/env python3
"""Independent data-only review of the finite-cover S193 recode.
The reviewer proposed the covering graph; root independently authored the packet.
This helper does not import or execute the author or predecessor source.
"""
import argparse
from collections import deque
import hashlib
import json
from pathlib import Path

AUTHOR={
 'matrix193_schreier_recode.py':'2b88eaa45feb7f7255b5d4b8fb5b994ec07c1610b69f2461894f1d74ba623847',
 'matrix193_schreier_recode.json':'e2a01632a9689aaf9ef5966b9f92772b59d71cd4d392d46346ebc890aa8dc9ea',
 'matrix193_schreier_recode.md':'17d67b09b8c05a453be7f23b66a3582fd90c776d57d6e32979b78425bd904f55'}
DATA={
 'group_directed_semigroup193.json':'c802f1ca0fde3cfcc856dd0f14ea2bf6270e1a9a924fe9743ee00c4336891639',
 'group_directed_semigroup193.md':'75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e',
 'u15_unary_block_interface.json':'a08e400d61ae5df0a25916f899d7e1e9e0225bc1d1d40052d4dc89ed435c30a0',
 'u15_unary_block_interface.md':'cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452'}
I=(1,0,0,1)
P=(1,2,0,1)
Q=(1,0,2,1)


def need(b,s):
 if not b:raise ValueError(s)
def sha(b):return hashlib.sha256(b).hexdigest()
def exact(a,b):
 if type(a)!=type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def serial(v):return json.dumps(v,sort_keys=True,separators=(',',':')).encode()
def mm(a,b):return (a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3])
def det(a):return a[0]*a[3]-a[1]*a[2]
def inv(a):
 need(det(a)==1,'SL2 inverse');return(a[3],-a[1],-a[2],a[0])
def matrix(a):return [list(a[:2]),list(a[2:])]
def diag(a,b):return [[a[0],a[1],0,0],[a[2],a[3],0,0],[0,0,b[0],b[1]],[0,0,b[2],b[3]]]
def mul4(a,b):return [[sum(a[i][k]*b[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
def negword(w):return [-x for x in reversed(w)]
def reduce(w):
 r=[]
 for x in w:
  if r and r[-1]==-x:r.pop()
  else:r.append(x)
 return r
def ambient(w):
 a=I
 for x in w:a=mm(a,{1:P,-1:inv(P),2:Q,-2:inv(Q)}[x])
 return a
def evalword(w,codes):
 a=I
 for x in w:a=mm(a,codes[x])
 return a

def graph_basis():
 # Independently enumerate the covering as a labeled directed graph.
 edges={}
 for v in range(19):
  edges[v,1]=0 if v==0 else v%18+1
  edges[v,2]=1-v if v<2 else v
 for label in (1,2):
  need(set(edges[v,label] for v in range(19))==set(range(19)),'permutation cover')
  for v in range(19):edges[edges[v,label],-label]=v
 todo=deque([0]); paths={0:[]}; tree=set()
 while todo:
  v=todo.popleft()
  for label in (1,2):
   target=edges[v,label]
   if target not in paths:
    paths[target]=paths[v]+[label];tree.add((v,label));todo.append(target)
 need(len(paths)==19 and len(tree)==18,'BFS spanning tree')
 loops={}
 for v in range(19):
  for label in (1,2):
   if (v,label) not in tree:
    loops[v,label]=reduce(paths[v]+[label]+negword(paths[edges[v,label]]))
 need(len(loops)==20,'all chord generators')
 basis=[loops[0,1],loops[1,2],loops[18,1]]+[loops[v,2] for v in range(2,19)]
 expected=[[1],[2,2],[2]+[1]*18+[-2]]+[[2]+[1]*r+[2]+[-1]*r+[-2] for r in range(1,18)]
 need(basis==expected,'explicit basis matches all BFS chords')
 new=[reduce(basis[0]+basis[1]),negword(basis[1])]+basis[2:]
 need(reduce(new[0]+new[1])==basis[0] and negword(new[1])==basis[1],'two-generator Nielsen inverse')
 return edges,paths,tree,loops,basis,new

def generators(parent,codes):
 rows=[]
 for t in parent['tiles']:
  i=t['id']; low=(1+4*i,2,-8*i*i,1-4*i)
  rows.append({'name':'A'+str(i),'tile_id':i,'matrix':diag(evalword(t['h'],codes),low)})
 for t in parent['tiles']:
  i=t['id']; low=(1+4*i,2,-8*i*i,1-4*i)
  rows.append({'name':'B'+str(i),'tile_id':i,'matrix':diag(inv(evalword(t['g'],codes)),mm(mm(inv(P),inv(low)),P))})
 rows.append({'name':'C','tile_id':None,'matrix':diag(inv(evalword(parent['terminal']+parent['separator'],codes)),P)})
 return rows

def statistics(rows):
 a=[v for row in rows for line in row['matrix'] for v in line]
 return {'generators':len(rows),'matrix_entry_slots':len(a),'nonzero_entries':sum(v!=0 for v in a),
 'maximum_absolute_entry':max(abs(v) for v in a),'maximum_entry_magnitude_bits':max(abs(v).bit_length() for v in a),
 'sum_entry_magnitude_bits':sum(abs(v).bit_length() for v in a)}

def verify(root,author_root):
 for folder,pins in [(root,DATA),(author_root,AUTHOR)]:
  for name,pin in pins.items():need(sha((folder/name).read_bytes())==pin,'pin '+name)
 saved=json.loads((author_root/'matrix193_schreier_recode.json').read_text())
 oldreceipt=json.loads((root/'group_directed_semigroup193.json').read_text());old=oldreceipt['packet'];new=saved['packet']
 edges,paths,tree,loops,basis,newbasis=graph_basis()
 graph=saved['cover']
 need(graph['old_basis']==basis and graph['new_basis']==newbasis,'author basis arrays')
 need(graph['tree_paths']==[paths[v] for v in range(19)] and graph['tree_edges']==[list(e) for e in sorted(tree)],'author full tree')
 need(graph['P_action']==[edges[v,1] for v in range(19)] and graph['Q_action']==[edges[v,2] for v in range(19)],'author cover actions')
 need(graph['chords']==[{'vertex':v,'letter':s,'word':loops[v,s]} for v,s in sorted(loops)],'author complete chord list')
 letters=list('01ABCDEFGHIJKLMNO[]')+['#']
 need(old['alphabet']+[old['separator']]==letters,'all active state/tape/separator letters')
 words=dict(zip(letters,newbasis));codes={s:ambient(w) for s,w in words.items()}
 need(new['top_words_in_PQ']==words and new['top_matrices']=={s:matrix(m) for s,m in codes.items()},'complete alphabet encoding')
 for m in codes.values():need(det(m)==1,'letter determinant')
 oldcodes={s:(1+4*i,2,-8*i*i,1-4*i) for s,i in old['top_codes'].items()}
 need(generators(old,oldcodes)==old['generators'],'independent original arrays')
 rows=generators(old,codes)
 need(rows==new['generators'],'independent full193 recoded arrays')
 need(len({tuple(v for row in r['matrix'] for v in row) for r in rows})==193,'distinct generators')
 for a,b in zip(old['generators'],rows):
  need(a['matrix'][2:]==b['matrix'][2:],'entire lower rows unchanged')
  for start in (0,2):need(det(tuple(b['matrix'][i][j] for i in range(start,start+2) for j in range(start,start+2)))==1,'full block determinant')
 fixed=['alphabet','deleted_old_tile_ids','rules','separator','terminal','tiles']
 for key in fixed:need(exact(old[key],new[key]),'unchanged metadata '+key)
 stats=statistics(rows);oldstats=statistics(old['generators'])
 need(stats==saved['new_statistics'] and oldstats==saved['old_statistics'],'full coefficient metrics')
 for key,val in stats.items():need(new['ledger'][key]==val,'packet metric '+key)
 excluded=set(stats)|{'largest_retained_top_code','changed_retained_generators','unchanged_retained_generators'}
 for key in set(old['ledger'])-excluded:need(old['ledger'][key]==new['ledger'][key],'unchanged resource '+key)
 need(new['ledger']['cover_vertices']==19 and new['ledger']['upper_blocks_equal_to_parent']==0,'recode resource counts')
 witness=oldreceipt['accepting_witness']; seq=witness['inner_tile_sequence']; tiles={t['id']:t for t in old['tiles']}
 w=witness['input']['configuration_word']; names=['A'+str(i) for i in seq]+['C']+['B'+str(i) for i in reversed(seq)]
 need(names==witness['generator_word'] and w=='[110A0]','unchanged complete witness recipe')
 need(w+'#'+''.join(tiles[i]['h'] for i in seq)==''.join(tiles[i]['g'] for i in seq)+old['terminal']+'#','literal full word equation')
 byname={r['name']:r['matrix'] for r in rows}; product=[[int(i==j) for j in range(4)] for i in range(4)]
 for n in names:product=mul4(product,byname[n])
 target=diag(inv(evalword(w+'#',codes)),P)
 need(product==target==saved['accepting_witness']['product']==saved['accepting_witness']['target'],'all16 accepting product entries')
 need(saved['accepting_witness']=={'input_word':w,'inner_tile_sequence':seq,'generator_word':names,'target':target,'product':product,'tile_count':83,'generator_word_length':167},'entire saved witness')
 W=evalword('01010111',codes);even=mm(W,W);a=(even[0]+even[3])//2;D=(even[0]-a,even[1],even[2],even[3]-a);delta=a*a-1
 need(W==(-47,6,-8,1) and a==1057 and delta==1117248 and mm(D,D)==(delta,0,0,delta),'exact new Pell interface')
 u=saved['universal_block'];need(u['matrix']==matrix(W) and u['square']==matrix(even) and u['D']==matrix(D),'saved full interface matrices')
 positive=negative=I;chi,psi=1,0
 for x in range(13):
  plus=(chi+psi*D[0],psi*D[1],psi*D[2],chi+psi*D[3]);minus=(chi-psi*D[0],-psi*D[1],-psi*D[2],chi-psi*D[3])
  need(positive==plus and negative==minus and chi*chi-delta*psi*psi==1,'independent sequential indexed powers')
  need(u['checked_powers'][x]=={'x':x,'chi':chi,'psi':psi,'positive_power':matrix(plus),'negative_power':matrix(minus)},'saved indexed power')
  positive=mm(positive,even);negative=mm(negative,inv(even));chi,psi=a*chi+delta*psi,chi+a*psi
 return {'status':'PASS','review_source_sha256':sha(Path(__file__).read_bytes()),'author_pins':AUTHOR,'dependency_pins':DATA,
  'disclosure':'Reviewer proposed the finite cover and checked root independent literal implementation; no claim of independent discovery of that design.',
  'checks':{'original_entries':3088,'recoded_entries':3088,'basis_loops':20,'cover_positive_edges':38,'unchanged_lower_blocks':193,
            'checked_block_determinants':386,'accepted_product_length':167,'accepted_product_entries':16,'signed_Pell_power_pairs':13},
  'independent_statistics':stats,'independent_target':target,'source_arrays_sha256':sha(serial(rows)),
  'Pell_base':a,'Delta':delta,'accepted_input':w,
  'mathematical_scope':'Cover injection plus full alphabet faithfulness preserves every finite-input word equation and semigroup membership target; parent universality is imported.',
  'arithmetic_bound_improvement':False,'index_relation_paid':False,'unbounded_membership_paid':False,'author_or_predecessor_code_executed':False}

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--author-root',type=Path)
 m=p.add_mutually_exclusive_group(required=True);m.add_argument('--output',type=Path);m.add_argument('--expect',type=Path)
 a=p.parse_args();out=verify(a.root.resolve(),(a.author_root or a.root).resolve());s=json.dumps(out,indent=2,sort_keys=True)+'\n'
 need(exact(out,json.loads(s)),'JSON typed roundtrip')
 if a.expect:need(exact(out,json.loads(a.expect.read_text())),'exact review receipt')
 else:a.output.write_text(s)
 print('PASS: independent cover, all193 arrays, 167-factor accepting product, costs and Pell1057.')
if __name__=='__main__':main()
