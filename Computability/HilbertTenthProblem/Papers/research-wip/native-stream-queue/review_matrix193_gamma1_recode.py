#!/usr/bin/env python3
"""Independent data-only audit of the Gamma1(5) full matrix recoding."""
import argparse
import hashlib
import itertools
import json
from collections import Counter, deque
from pathlib import Path

AUTHOR = {
 'matrix193_gamma1_recode.py':'ae24e64539b450fd9c4db0b3e04ce440d00562dcfe532a43002d7c52da34757c',
 'matrix193_gamma1_recode.json':'9cdd0274625c847aa77f5907ba6554ee16f37895f5c026b3d776595330676668',
 'matrix193_gamma1_recode.md':'6349644283548af96f4a9582ee32d959a123c81bf1c2f902c45874ae45c96742'}
PINS = {
 'group_directed_semigroup193.json':'c802f1ca0fde3cfcc856dd0f14ea2bf6270e1a9a924fe9743ee00c4336891639',
 'group_directed_semigroup193.md':'75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e',
 'matrix193_schreier_recode.json':'e2a01632a9689aaf9ef5966b9f92772b59d71cd4d392d46346ebc890aa8dc9ea',
 'matrix193_schreier_recode.md':'17d67b09b8c05a453be7f23b66a3582fd90c776d57d6e32979b78425bd904f55',
 'u15_unary_block_interface.md':'cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452'}
I=(1,0,0,1); S=(0,-1,1,0); R=(0,-1,1,1)
T=(1,1,0,1); U=(1,0,5,1); V0=(-14,-9,25,16); V=(-9,5,-20,11)
P=(1,2,0,1); Q=(1,0,2,1)
ASSIGN=(0,10,4,3,15,13,6,14,9,1,16,11,12,5,8,7,2,17)

def need(p,label):
 if not p: raise ValueError(label)
def sha(b): return hashlib.sha256(b).hexdigest()
def pairs(xs):
 out={}
 for k,v in xs:
  need(k not in out,'duplicate JSON key');out[k]=v
 return out
def read(b):return json.loads(b,object_pairs_hook=pairs,parse_constant=lambda z:(_ for _ in ()).throw(ValueError(z)))
def exact(a,b):
 if type(a) is not type(b):return False
 if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
 if isinstance(a,list):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
 return a==b
def compare(a,b,label):need(exact(a,b),label)
def digest_obj(a):return sha(json.dumps(a,sort_keys=True,separators=(',',':')).encode())
def authenticated(root,pins):
 out={}
 for n,h in pins.items():
  b=(root/n).read_bytes();need(sha(b)==h,'pin '+n);out[n]=b
 return out
def mul(a,b):return (a[0]*b[0]+a[1]*b[2],a[0]*b[1]+a[1]*b[3],a[2]*b[0]+a[3]*b[2],a[2]*b[1]+a[3]*b[3])
def det(a):return a[0]*a[3]-a[1]*a[2]
def inv(a):
 need(det(a)==1,'determinant');return a[3],-a[1],-a[2],a[0]
def prod(xs):
 a=I
 for b in xs:a=mul(a,b)
 return a
def power(a,n):
 if n<0:return power(inv(a),-n)
 out=I
 for _ in range(n):out=mul(out,a)
 return out
def word(w,code):return prod(code[c] for c in w)
def inverse_word(w):return ''.join(c.swapcase() for c in reversed(w))
def reduce_word(w):
 out=[]
 for c in w:
  if out and out[-1]==c.swapcase():out.pop()
  else:out.append(c)
 return ''.join(out)
def reduce_int(w):
 out=[]
 for c in w:
  if out and out[-1]==-c:out.pop()
  else:out.append(c)
 return out
def block(a,b):return [[a[0],a[1],0,0],[a[2],a[3],0,0],[0,0,b[0],b[1]],[0,0,b[2],b[3]]]
def m4(a,b):return [[sum(a[i][k]*b[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
def stats(gs):
 vals=[z for g in gs for row in g['matrix'] for z in row]
 return dict(generators=len(gs),entry_slots=len(vals),nonzero_entries=sum(z!=0 for z in vals),maximum_absolute_entry=max(map(abs,vals)),maximum_magnitude_bits=max(abs(z).bit_length() for z in vals),sum_magnitude_bits=sum(abs(z).bit_length() for z in vals))

def modular(a):
 # Enumerate the entire finite projective matrix group, not only the saved action.
 sl={z for z in itertools.product(range(5),repeat=4) if det(z)%5==1}
 norm=lambda z:min(z,tuple(-v%5 for v in z))
 psl={norm(z) for z in sl}
 need(len(sl)==120 and len(psl)==60,'finite SL/PSL orders')
 row=lambda z:norm(z[2:])
 classes=Counter(row(z) for z in psl);vs=sorted(classes)
 need(len(vs)==12 and set(classes.values())=={5},'twelve row cosets')
 stabilizer={z for z in psl if row(z)==(0,1)}
 expected={norm((1,b,0,1)) for b in range(5)}
 need(stabilizer==expected,'exact projective Gamma stabilizer')
 reached={norm(I)};todo=[norm(I)]
 while todo:
  z=todo.pop()
  for g in (S,R):
   y=norm(tuple(v%5 for v in mul(z,g)))
   if y not in reached:reached.add(y);todo.append(y)
 need(reached==psl,'whole finite group generated')
 def action(g):return [vs.index(norm(((x*g[0]+y*g[2])%5,(x*g[1]+y*g[3])%5))) for x,y in vs]
 sp,rp=action(S),action(R)
 compare([list(v) for v in vs],a['vectors'],'row classes');compare(sp,a['S_action'],'S action');compare(rp,a['R_action'],'R action')
 def orbit_partition(p):
  out=[];remaining=set(range(12))
  while remaining:
   z=min(remaining);cycle=[]
   while z not in cycle:cycle.append(z);remaining.remove(z);z=p[z]
   out.append(cycle)
  return out
 so,ro=orbit_partition(sp),orbit_partition(rp)
 need([len(z) for z in so]==[2]*6 and [len(z) for z in ro]==[3]*4,'trivial vertex stabilizers')
 ends=[[next(k for k,o in enumerate(so) if e in o),6+next(k for k,o in enumerate(ro) if e in o)] for e in range(12)]
 compare(ends,a['edges'],'orbit endpoints')
 tree=[0,1,3,4,5,6,8,9,10];compare(tree,a['tree_edges'],'specified tree')
 reached={6}
 while True:
  bigger=reached|{y for e in tree for x,y in (ends[e],ends[e][::-1]) if x in reached}
  if bigger==reached:break
  reached=bigger
 need(reached==set(range(10)) and len(tree)==9,'modular spanning tree')
 chords=set(range(12))-set(tree)
 # Subdivide all edges. All S-to-midpoint halves and the nine selected
 # midpoint-to-R halves form a 21-edge spanning tree on 22 vertices.
 # This independently fixes chord orientation opposite to the author.
 def coordinates(w):
  e=0;out=[]
  for c in w:
   j=(sp if c=='S' else rp)[e]
   if c=='R':out += ([e+1] if e in chords else [])+([-j-1] if j in chords else [])
   e=j
  need(e==0,'closed modular word');return reduce_int(out)
 def tw(n):return 'SR'*n if n>=0 else 'RRS'*(-n)
 def euclid_word(m):
  aa,b,c,d=m;w=''
  while c:
   q=aa//c;w+=tw(q)+'S';aa,b,c,d=-c,-d,aa-q*c,b-q*d
  need(abs(aa)==1 and c==0,'Euclid terminal');w+=tw(b//aa)
  z=word(w,{'S':S,'R':R});need(z==m or z==tuple(-x for x in m),'Euclid modular factorization');return w
 records=[]
 for name,m,expected_chord in [('T',T,[3]),('U',U,[3,-12]),('V0',V0,[-8])]:
  w=euclid_word(m);coords=coordinates(w);compare(coords,expected_chord,'independent chord basis '+name)
  records.append(dict(name=name,word=w,chords=coords))
 for item in a['chord_loops']:
  compare(list(word(item['word'],{'S':S,'R':R})),item['matrix'],'saved exact chord lift')
  compare(coordinates(item['word']),[-item['edge']-1],'saved chord coordinates')
 compare(a['T_chords'],[-3],'author T orientation');compare(a['U_chords'],[-3,12],'author U orientation')
 need(prod((T,V0,inv(T),U,inv(T)))==V and prod((inv(T),V,T,inv(U),T))==V0,'Nielsen matrices')
 need(all(m[0]%5==m[3]%5==1 and m[2]%5==0 for m in (T,U,V0,V)),'Gamma1 lifts')
 compare(a['free_basis'],[list(T),list(U),list(V)],'free basis metadata');need(a['rank']==3,'rank3')
 return dict(SL2_F5=120,PSL2_F5=60,cosets=12,stabilizer=5,vertices=10,edges=12,rank=3,independent_Euclidean_chords=records)

def immersed(a):
 actions={'t':[0,2,3,4,5,6,7,8,9,1],'u':[0,None,2,3,4,5,6,7,8,9],'v':[1,0,2,3,4,5,6,7,8,9]}
 compare(actions,a['actions'],'literal immersion')
 edges=[(c,i,j) for c,p in actions.items() for i,j in enumerate(p) if j is not None]
 compare([list(e) for e in edges],a['edges'],'all immersed edges')
 for c,p in actions.items():need(len([j for j in p if j is not None])==len({j for j in p if j is not None}),'incoming labels')
 tree={('v',0)}|{('t',i) for i in range(1,9)}
 compare([[c,i] for c,i in sorted(tree)],a['tree'],'immersed tree')
 adj={i:[] for i in range(10)}
 for c,i,j in edges:
  if (c,i) in tree:adj[i].append((j,c));adj[j].append((i,c.upper()))
 paths={0:''};todo=deque([0])
 while todo:
  i=todo.popleft()
  for j,c in adj[i]:
   if j not in paths:paths[j]=paths[i]+c;todo.append(j)
 need(len(paths)==10 and len(tree)==9,'immersed spanning tree')
 matrices={'t':T,'u':U,'v':V};matrices.update({k.upper():inv(v) for k,v in list(matrices.items())})
 loops=[]
 for c,i,j in edges:
  if (c,i) not in tree:
   w=reduce_word(paths[i]+c+inverse_word(paths[j]))
   loops.append(dict(label=c,origin=i,word=w,matrix=list(word(w,matrices))))
 compare(loops,a['basis_loops'],'all twenty actual fundamental loops')
 basis=['t','u','vv','v'+'t'*9+'V']+['v'+'t'*r+'u'+'T'*r+'V' for r in range(1,9)]+['v'+'t'*r+'v'+'T'*r+'V' for r in range(1,9)]
 need(sorted(z['word'] for z in loops)==sorted(basis),'free words, not merely equal matrices')
 newbasis=[reduce_word('V'+w+'v') for w in basis]
 extras=newbasis[2:]
 compare([list(word(w,matrices)) for w in extras],a['extra_matrices'],'all basepoint-transferred extras')
 compare(list(ASSIGN),a['extra_assignment'],'assignment');need(set(ASSIGN)==set(range(18)),'assignment permutation')
 tape0='Vtuv';tape1='VUv'
 need(reduce_word(tape0+tape1)==newbasis[0] and inverse_word(tape1)==newbasis[1],'formal invertible tape basis change')
 letter_words={'0':tape0,'1':tape1};letter_words.update({c:extras[j] for c,j in zip('ABCDEFGHIJKLMNO[]#',ASSIGN)})
 letters={c:word(w,matrices) for c,w in letter_words.items()}
 need(len(letters)==20 and len(set(letters.values()))==20,'twenty letters')
 for m in letters.values():need(det(m)==1 and m[0]%5==m[3]%5==1 and m[2]%5==0,'all Gamma1 matrices')
 need(actions['u'][1] is None and 1 not in actions['u'],'both U orientations absent at new base')
 need(a['rank']==20 and a['new_base_vertex']==1 and len(edges)-len(paths)+1==20,'immersed rank/base')
 return letters,dict(vertices=10,edges=29,tree_edges=9,free_basis_words=basis,basepoint_transferred_words=newbasis,rank=20,letter_words=letter_words,missing_both_U_directions=True)

def matrix_arrays(parent,author,letters,previous):
 p=parent['packet'];a=author['packet']
 for key in ('alphabet','separator','terminal','rules','tiles'):compare(a[key],p[key],'retained '+key)
 need(len(p['rules'])==91 and len(p['tiles'])==96 and p['terminal']=='[J1]','source inventory')
 compare({c:list(m) for c,m in letters.items()},a['letters'],'all active letter matrices')
 need(set(letters)==set(p['alphabet'])|{'#'},'complete alphabet')
 # Closed numerical E_i formula gives a separate lower-code reconstruction.
 E=lambda n:(1+4*n,2,-8*n*n,1-4*n)
 oldcode={c:E(n) for c,n in p['top_codes'].items()}
 def emit(code):
  out=[]
  for typ in ('A','B'):
   for tile in p['tiles']:
    j=tile['id'];lower=E(j)
    if typ=='A':upper=word(tile['h'],code)
    else:upper=inv(word(tile['g'],code));lower=prod((inv(P),inv(lower),P))
    out.append(dict(name=typ+str(j),tile_id=j,matrix=block(upper,lower)))
  out.append(dict(name='C',tile_id=None,matrix=block(inv(word('[J1]#',code)),P)))
  return out
 old=emit(oldcode);new=emit(letters)
 compare(old,p['generators'],'full old arrays');compare(new,a['generators'],'full new arrays')
 need(len(new)==193 and len({str(g['matrix']) for g in new})==193,'complete distinct matrix count')
 for g,h in zip(new,old):
  m=g['matrix'];compare([r[2:] for r in m[2:]],[r[2:] for r in h['matrix'][2:]],'lower block retained')
  for off in (0,2):need(det(tuple(m[i+off][j+off] for i in range(2) for j in range(2)))==1,'block determinant')
  need(all(m[i][j]==0 for i in range(4) for j in range(4) if (i<2)!=(j<2)),'block diagonality')
 compare(stats(new),author['statistics'],'new complete statistics');compare(stats(old),author['original_statistics'],'original complete statistics')
 ps=stats(previous['packet']['generators'])
 translated={({'entry_slots':'matrix_entry_slots','maximum_magnitude_bits':'maximum_entry_magnitude_bits','sum_magnitude_bits':'sum_entry_magnitude_bits'}.get(k,k)):v for k,v in ps.items()}
 compare(translated,author['previous_schreier_statistics'],'previous full array statistics')
 witness=parent['accepting_witness'];aw=author['accepting_witness'];gw=witness['generator_word']
 compare(gw,aw['generator_word'],'same complete witness word');need(len(gw)==167,'witness length')
 maps={g['name']:g['matrix'] for g in new};result=block(I,I)
 for g in gw:result=m4(result,maps[g])
 target=block(inv(word(witness['derivation'][0]+'#',letters)),P)
 compare(result,target,'whole accepting product');compare(result,aw['product'],'saved product');compare(target,aw['target'],'saved target')
 compare(aw['input'],witness['derivation'][0],'input');need(aw['generator_word_length']==167,'witness receipt length')
 # Recheck the inherited positive-word equation and every actual rewrite.
 tiles={t['id']:t for t in p['tiles']};seq=witness['inner_tile_sequence']
 gg=''.join(tiles[j]['g'] for j in seq);hh=''.join(tiles[j]['h'] for j in seq)
 need(witness['derivation'][0]+'#'+hh==gg+'[J1]#','whole correspondence equation')
 rules=[(r['lhs'],r['rhs']) for r in p['rules']]
 for x,y in zip(witness['derivation'],witness['derivation'][1:]):
  need(any(y==x[:i]+rhs+x[i+len(lhs):] for lhs,rhs in rules for i in range(len(x)-len(lhs)+1) if x[i:i+len(lhs)]==lhs),'literal rewrite step')
 return dict(old_entries=3088,new_entries=3088,distinct_new_generators=193,retained_lower_blocks=193,block_determinants=386,rules=91,tiles=96,witness_generators=167,witness_rewrites=len(witness['derivation'])-1,new_statistics=stats(new),old_statistics=stats(old),previous_statistics=stats(previous['packet']['generators']),array_digest=digest_obj(new),witness_product=result)

def pell_target(a,letters):
 wb=word('01010111',letters);bb=mul(wb,wb);d=tuple(x-(391 if i in (0,3) else 0) for i,x in enumerate(bb))
 need(wb==(1861,-1037,3390,-1889) and wb[0]+wb[3]==-28,'block W')
 need(bb==(-52109,29036,-94920,52891) and det(bb)==1,'even block')
 need(mul(d,d)==tuple(152880*x for x in I) and 391**2-152880==1,'formal quadratic algebra')
 ub=a['universal_block']
 for key,value in [('word','01010111'),('matrix',list(wb)),('trace',-28),('square',list(bb)),('a0',391),('Delta0',152880),('D',list(d))]:compare(value,ub[key],'universal block '+key)
 # Independent scalar recurrence via trace Cayley-Hamilton, not author's pair update.
 chi=[1,391];psi=[0,1]
 for n in range(2,21):chi.append(782*chi[-1]-chi[-2]);psi.append(782*psi[-1]-psi[-2])
 checks=[]
 left=inv(word('10]#',letters));right=inv(word('[A0',letters))
 ac=mul(left,right);cc=tuple(-z for z in prod((left,d,right)))
 for n in range(21):
  need(chi[n]**2-152880*psi[n]**2==1,'scalar Pell')
  for sign in (-1,1):need(power(bb,sign*n)==tuple(chi[n]*I[k]+sign*psi[n]*d[k] for k in range(4)),'full power identity sample')
  need(prod((left,power(bb,-n),right))==tuple(ac[k]*chi[n]+cc[k]*psi[n] for k in range(4)),'all four context coordinates')
  checks.append(dict(x=n,chi=chi[n],psi=psi[n]))
 compare(checks[:13],ub['pell_checks'],'saved scalar checks')
 # Sparse coefficient vectors in independent variables A11,C11,A12,C12,chi,psi.
 free=['A11','C11','A12','C12','chi','psi'];zero=(0,)*6
 env={v:{tuple(int(i==j) for i in range(6)):1} for j,v in enumerate(free)}
 source=a['projected_target']['generic_source'];counts=Counter();uses=Counter()
 for out,op,x,y in source:
  need(out not in env and x in env and y in env,'complete target graph')
  counts[op]+=1;uses[x]+=1;uses[y]+=1
  if op=='mul':
   q={}
   for u,c in env[x].items():
    for v,e in env[y].items():
     key=tuple(i+j for i,j in zip(u,v));q[key]=q.get(key,0)+c*e
  elif op=='add':
   q=dict(env[x])
   for v,c in env[y].items():q[v]=q.get(v,0)+c
  else:raise ValueError('target operation')
  env[out]={k:v for k,v in q.items() if v}
 for output,indices in [('target11',[(0,4),(1,5)]),('target12',[(2,4),(3,5)])]:
  expected={tuple(int(j in pair) for j in range(6)):1 for pair in indices}
  need(env[output]==expected,'exact generic target polynomial')
 live={'target11','target12'}
 for out,op,x,y in reversed(source):
  if out in live:live.update((x,y))
 need(live==set(env) and counts=={'mul':4,'add':2},'all target gates and inputs live')
 proj=a['projected_target'];compare(proj['varying_entries'],['upper11','upper12'],'projected entries');compare(proj['fixed_entries'],{'lower11':1,'lower12':2,'lower21':0},'fixed lower entries')
 need(proj['M']==4 and proj['A']==2 and proj['total']==6 and proj['index_relation_paid'] is False and proj['membership_certificate_paid'] is False,'paid scope')
 return dict(block=list(wb),square=list(bb),D=list(d),Pell_parameter=391,discriminant=152880,independent_scalar_recurrence_checks=21,full_signed_power_checks=42,full_context_checks=21,target_gates=6,target_M=4,target_A=2,formal_target_polynomials=2,index_and_membership_unpaid=True)

def verify(root,author_root):
 pb=authenticated(root,PINS);ab=authenticated(author_root,AUTHOR)
 a=read(ab['matrix193_gamma1_recode.json']);parent=read(pb['group_directed_semigroup193.json']);previous=read(pb['matrix193_schreier_recode.json'])
 compare(a['pins'],PINS,'all declared dependency pins');need(a['source_sha256']==AUTHOR['matrix193_gamma1_recode.py'],'bound author source')
 need(a['status']=='PASS' and a['new_universal_Diophantine_bound'] is False and a['predecessor_code_executed'] is False,'honest outcome flags')
 mod=modular(a['modular_graph']);letters,graph=immersed(a['upper_immersed_graph'])
 arrays=matrix_arrays(parent,a,letters,previous);pell=pell_target(a,letters)
 compare(a['checks'],dict(parent_entries_reconstructed=3088,new_entries_emitted=3088,lower_blocks=193,block_determinants=386,free_upper_letters=20,modular_graph_edges=12,upper_graph_edges=29,complete_accepting_products=1,positive_negative_power_pairs=13,context_projection_checks=13),'saved evidence counts')
 return dict(status='PASS',review_source_sha256=sha(Path(__file__).read_bytes()),author_pins=AUTHOR,dependency_pins=PINS,predecessor_or_author_code_executed=False,modular_graph=mod,immersed_graph=graph,full_arrays=arrays,Pell_and_target=pell,scope='Complete graph/source data audit plus companion mathematical review; inherited U15 compiler and S193 shape theorem are read and pinned, not rebuilt; no complete universal Diophantine operation bound.')

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--author-root',type=Path)
 group=ap.add_mutually_exclusive_group(required=True);group.add_argument('--output',type=Path);group.add_argument('--expect',type=Path)
 args=ap.parse_args();receipt=verify(args.root,args.author_root or args.root)
 if args.expect:compare(receipt,read(args.expect.read_bytes()),'type-exact receipt')
 else:args.output.write_text(json.dumps(receipt,sort_keys=True,indent=2,allow_nan=False)+'\n')
 print('PASS: full 193-matrix recoding, independent modular/free-basis graphs, first-row premises, and conditional six-gate target')
if __name__=='__main__':main()
