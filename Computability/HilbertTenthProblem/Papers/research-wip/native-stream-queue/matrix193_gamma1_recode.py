#!/usr/bin/env python3
"""Fresh bounded data-only recoding of the complete directed 193-generator packet."""
import argparse
import hashlib
import json
from collections import deque
from pathlib import Path

PINS = {
 'group_directed_semigroup193.json':'c802f1ca0fde3cfcc856dd0f14ea2bf6270e1a9a924fe9743ee00c4336891639',
 'group_directed_semigroup193.md':'75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e',
 'matrix193_schreier_recode.json':'e2a01632a9689aaf9ef5966b9f92772b59d71cd4d392d46346ebc890aa8dc9ea',
 'matrix193_schreier_recode.md':'17d67b09b8c05a453be7f23b66a3582fd90c776d57d6e32979b78425bd904f55',
 'u15_unary_block_interface.md':'cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452',
}
I=(1,0,0,1)
T=(1,1,0,1)
U=(1,0,5,1)
V0=(-14,-9,25,16)
V=(-9,5,-20,11)
LOW_P=(1,2,0,1)
LOW_Q=(1,0,2,1)
S=(0,-1,1,0)
R=(0,-1,1,1)
EXTRA_LETTERS='ABCDEFGHIJKLMNO[]#'
ASSIGNMENT=[0,10,4,3,15,13,6,14,9,1,16,11,12,5,8,7,2,17]

def require(p,msg):
 if not p: raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def mm(a,b):return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2)) for i in range(2) for j in range(2))
def inv(a):
 require(a[0]*a[3]-a[1]*a[2]==1,'inverse determinant')
 return (a[3],-a[1],-a[2],a[0])
def power(a,n):
 if n<0:return power(inv(a),-n)
 out=I
 while n:
  if n&1:out=mm(out,a)
  a=mm(a,a);n//=2
 return out
def product(xs):
 out=I
 for a in xs:out=mm(out,a)
 return out
def conjugate(a,g):return product([inv(g),a,g])
def block(a,b):return [[a[0],a[1],0,0],[a[2],a[3],0,0],[0,0,b[0],b[1]],[0,0,b[2],b[3]]]
def mul4(a,b):return [[sum(a[i][k]*b[k][j] for k in range(4)) for j in range(4)] for i in range(4)]
def word(w,letters):return product(letters[c] for c in w)
def pairs(xs):
 d={}
 for k,v in xs:
  require(k not in d,'duplicate JSON key');d[k]=v
 return d
def loads(b):return json.loads(b,object_pairs_hook=pairs,parse_constant=lambda s:(_ for _ in ()).throw(ValueError(s)))
def canonical(a):return json.dumps(a,sort_keys=True,separators=(',',':'),allow_nan=False)
def signed_equal(a,b):return a==b or a==tuple(-x for x in b)
def reduced(w):
 out=[]
 for x in w:
  if out and out[-1]==-x:out.pop()
  else:out.append(x)
 return out

def modular_graph():
 def canon(v):return min(v,tuple(-x%5 for x in v))
 vs=sorted({canon((a,b)) for a in range(5) for b in range(5) if (a,b)!=(0,0)})
 def action(m):return [vs.index(canon(((a*m[0]+b*m[2])%5,(a*m[1]+b*m[3])%5))) for a,b in vs]
 sp,rp=action(S),action(R)
 require(sorted(sp)==sorted(rp)==list(range(12)),'modular permutations')
 require(all(sp[sp[i]]==i and sp[i]!=i for i in range(12)),'free order two action')
 require(all(rp[rp[rp[i]]]==i and rp[i]!=i for i in range(12)),'free order three action')
 def orbits(p):
  out=[];todo=set(range(12))
  while todo:
   z=min(todo);orb=[]
   while z not in orb:orb.append(z);todo.remove(z);z=p[z]
   out.append(orb)
  return out
 so,ro=orbits(sp),orbits(rp)
 si={e:j for j,o in enumerate(so) for e in o};ri={e:j+6 for j,o in enumerate(ro) for e in o}
 edges=[(si[e],ri[e]) for e in range(12)]
 tree=[0,1,3,4,5,6,8,9,10];chords=[2,11,7]
 require(len(so)==6 and len(ro)==4 and len(edges)-10+1==3,'modular rank')
 adj={i:[] for i in range(10)}
 for e in tree:
  a,b=edges[e];adj[a].append((b,e));adj[b].append((a,e))
 def route(start,end):
  seen={start:[]};todo=deque([start])
  while todo:
   v=todo.popleft()
   if v==end:return seen[v]
   for z,e in adj[v]:
    if z not in seen:seen[z]=seen[v]+[(v,z,e)];todo.append(z)
  raise ValueError('disconnected modular tree')
 for i in range(10):route(6,i)
 loops=[]
 for e in chords:
  a,b=edges[e];rt=route(6,b)+[(b,a,e)]+route(a,6);prev=0;w=[]
  for z,_,j in rt:
   if z<6:require(sp[prev]==j,'S turn');w.append('S')
   else:
    k=0;x=prev
    while x!=j:x=rp[x];k+=1;require(k<3,'R turn')
    w+=['R']*k
   prev=j
  k=0
  while prev!=0:prev=rp[prev];k+=1;require(k<3,'terminal R turn')
  w+=['R']*k;m=product(S if z=='S' else R for z in w)
  loops.append({'edge':e,'word':''.join(w),'matrix':list(m)})
 require(signed_equal(tuple(loops[0]['matrix']),inv(T)),'T chord')
 require(signed_equal(tuple(loops[1]['matrix']),mm(inv(T),U)),'U chord')
 require(signed_equal(tuple(loops[2]['matrix']),V0),'V0 chord')
 def chordword(kind,count):
  z=0;out=[]
  for _ in range(count):
   out.extend([(z,1),(sp[z],-1)])
   z=rp[sp[z]] if kind=='T' else rp[rp[sp[z]]]
  require(z==0,'closed cusp word')
  return reduced([(e+1)*d for e,d in out if e in chords])
 require(chordword('T',1)==[-3] and chordword('U',5)==[-3,12],'cusp basis coordinates')
 require(product([T,V0,inv(T),U,inv(T)])==V,'Nielsen replacement')
 require(product([inv(T),V,T,inv(U),T])==V0,'inverse Nielsen replacement')
 return {'vectors':[list(x) for x in vs],'S_action':sp,'R_action':rp,'edges':[list(x) for x in edges],
         'tree_edges':tree,'chord_loops':loops,'T_chords':[-3],'U_chords':[-3,12],
         'free_basis':[list(T),list(U),list(V)],'rank':3}

def upper_graph():
 actions={'t':[0]+list(range(2,10))+[1],'u':[0,None]+list(range(2,10)), 'v':[1,0]+list(range(2,10))}
 edges=[(a,i,j) for a,p in actions.items() for i,j in enumerate(p) if j is not None]
 require(len(edges)==29,'immersed edges')
 for a,p in actions.items():
  im=[x for x in p if x is not None];require(len(im)==len(set(im)),'immersion incoming labels')
 paths=[[]]+[['v']+['t']*(i-1) for i in range(1,10)]
 def inverse_word(w):return [x.upper() if x.islower() else x.lower() for x in reversed(w)]
 tree={('v',0)}|{('t',i) for i in range(1,9)}
 mats={'t':T,'u':U,'v':V,'T':inv(T),'U':inv(U),'V':inv(V)}
 loops=[]
 for a,i,j in edges:
  if (a,i) in tree:continue
  w=paths[i]+[a]+inverse_word(paths[j]);loops.append((a,i,''.join(w),word(w,mats)))
 require(len(loops)==29-10+1==20,'rank twenty')
 expected=[T,U,power(V,2),product([V,power(T,9),inv(V)])]
 expected += [product([V,power(T,r),U,power(T,-r),inv(V)]) for r in range(1,9)]
 expected += [product([V,power(T,r),V,power(T,-r),inv(V)]) for r in range(1,9)]
 require(sorted(m for _,_,_,m in loops)==sorted(expected),'all twenty tree basis matrices')
 require(actions['u'][1] is None and 1 not in actions['u'],'missing U in both directions at new base')
 extras=[power(V,2),power(T,9)]
 extras += [product([power(T,r),U,power(T,-r)]) for r in range(1,9)]
 extras += [product([power(T,r),V,power(T,-r)]) for r in range(1,9)]
 require(sorted(ASSIGNMENT)==list(range(18)),'basis assignment')
 letters={'0':conjugate(mm(T,U),V),'1':conjugate(inv(U),V)}
 letters.update({c:extras[j] for c,j in zip(EXTRA_LETTERS,ASSIGNMENT)})
 for m in letters.values():
  inv(m);require(m[0]%5==m[3]%5==1 and m[2]%5==0,'Gamma1(5) condition')
 return letters, {'actions':actions,'edges':[list(x) for x in edges],'tree':[[a,i] for a,i in sorted(tree)],
   'basis_loops':[{'label':a,'origin':i,'word':w,'matrix':list(m)} for a,i,w,m in loops],
   'rank':20,'new_base_vertex':1,'extra_assignment':ASSIGNMENT,'extra_matrices':[list(m) for m in extras]}

def statistics(gens):
 vals=[x for g in gens for r in g['matrix'] for x in r]
 return {'generators':len(gens),'entry_slots':len(vals),'nonzero_entries':sum(x!=0 for x in vals),
  'maximum_absolute_entry':max(map(abs,vals)),'maximum_magnitude_bits':max(abs(x).bit_length() for x in vals),
  'sum_magnitude_bits':sum(abs(x).bit_length() for x in vals)}

def verify(root):
 raw={}
 for name,h in PINS.items():
  b=(root/name).read_bytes();require(sha(b)==h,'dependency pin: '+name);raw[name]=b
 parent=loads(raw['group_directed_semigroup193.json']);old=parent['packet']
 previous=loads(raw['matrix193_schreier_recode.json'])
 mg=modular_graph();letters,ug=upper_graph()
 require(set(letters)==set(old['alphabet'])|{old['separator']},'full active alphabet')
 tiles=old['tiles'];require(len(tiles)==96 and len(old['rules'])==91,'literal inventory')
 old_letters={c:product([power(LOW_Q,-i),LOW_P,power(LOW_Q,i)]) for c,i in old['top_codes'].items()}
 def emit(ls):
  gs=[]
  for typ in ['A','B']:
   for tile in tiles:
    n=tile['id'];lo=product([power(LOW_Q,-n),LOW_P,power(LOW_Q,n)])
    up=word(tile['h'] if typ=='A' else tile['g'],ls)
    if typ=='B':up=inv(up);lo=product([inv(LOW_P),inv(lo),LOW_P])
    gs.append({'name':typ+str(n),'tile_id':n,'matrix':block(up,lo)})
  gs.append({'name':'C','tile_id':None,'matrix':block(inv(word(old['terminal']+'#',ls)),LOW_P)})
  return gs
 reconstructed=emit(old_letters)
 old_by={g['name']:g['matrix'] for g in old['generators']}
 require({g['name']:g['matrix'] for g in reconstructed}==old_by,'all parent entries')
 gens=emit(letters)
 require(len({canonical(g['matrix']) for g in gens})==193,'distinct new generators')
 for g in gens:
  m=g['matrix'];inv(tuple(m[i][j] for i in range(2) for j in range(2)))
  inv(tuple(m[i][j] for i in range(2,4) for j in range(2,4)))
  require([r[2:] for r in m[2:]]==[r[2:] for r in old_by[g['name']][2:]],'unchanged lower block')
 gm={g['name']:g['matrix'] for g in gens};acc=block(I,I)
 witness=parent['accepting_witness'];gw=witness['generator_word']
 require(len(gw)==167,'accepting length')
 for z in gw:acc=mul4(acc,gm[z])
 inp=witness['derivation'][0];target=block(inv(word(inp+'#',letters)),LOW_P)
 require(acc==target,'complete accepting product')
 wb=word('01010111',letters);require(wb[0]+wb[3]==-28,'universal block trace')
 bb=mm(wb,wb);a0=(bb[0]+bb[3])//2;require(a0==391,'Pell parameter')
 d=tuple(bb[i]-(a0 if i in (0,3) else 0) for i in range(4));delta=a0*a0-1
 require(mm(d,d)==tuple(delta*x for x in I),'quadratic algebra')
 pell=[];chi,psi=1,0
 for x in range(13):
  pos=tuple(chi*I[i]+psi*d[i] for i in range(4));neg=tuple(chi*I[i]-psi*d[i] for i in range(4))
  require(pos==power(bb,x) and neg==power(bb,-x),'indexed powers')
  pell.append({'x':x,'chi':chi,'psi':psi});chi,psi=a0*chi+delta*psi,chi+a0*psi
 # One fixed nontrivial context check illustrates the generic all-x matrix identity.
 left=inv(word('10]#',letters));right=inv(word('[A0',letters));aa=mm(left,right);cc=tuple(-z for z in product([left,d,right]))
 for z in pell:
  chi,psi,x=z['chi'],z['psi'],z['x'];rows=[aa[i]*chi+cc[i]*psi for i in (0,1)]
  require(rows==list(product([left,power(bb,-x),right])[:2]),'two coordinate loader')
 slp=[['a','mul','A11','chi'],['b','mul','C11','psi'],['target11','add','a','b'],
      ['c','mul','A12','chi'],['d','mul','C12','psi'],['target12','add','c','d']]
 return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'pins':PINS,
  'scope':'Complete faithful 193-matrix recoding and conditional two-coordinate target interface; no complete Diophantine bound.',
  'predecessor_code_executed':False,'modular_graph':mg,'upper_immersed_graph':ug,
  'packet':{'schema':'matrix193-gamma1-five-recode-v1','alphabet':old['alphabet'],'separator':'#','terminal':old['terminal'],
            'rules':old['rules'],'tiles':tiles,'letters':{k:list(v) for k,v in letters.items()},'generators':gens},
  'statistics':statistics(gens),'original_statistics':statistics(old['generators']),
  'previous_schreier_statistics':previous['new_statistics'],
  'universal_block':{'word':'01010111','matrix':list(wb),'trace':-28,'square':list(bb),'a0':a0,'Delta0':delta,'D':list(d),'pell_checks':pell},
  'projected_target':{'varying_entries':['upper11','upper12'],'fixed_entries':{'lower11':1,'lower12':2,'lower21':0},
     'generic_source':slp,'M':4,'A':2,'total':6,'index_relation_paid':False,'membership_certificate_paid':False},
  'accepting_witness':{'input':inp,'generator_word':gw,'generator_word_length':len(gw),'product':acc,'target':target},
  'checks':{'parent_entries_reconstructed':3088,'new_entries_emitted':3088,'lower_blocks':193,'block_determinants':386,
    'free_upper_letters':20,'modular_graph_edges':12,'upper_graph_edges':29,'complete_accepting_products':1,
    'positive_negative_power_pairs':13,'context_projection_checks':13},'new_universal_Diophantine_bound':False}

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True)
 g=ap.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
 ns=ap.parse_args();out=verify(ns.root.resolve())
 require(canonical(loads(canonical(out)))==canonical(out),'typed JSON round trip')
 if ns.expect:require(canonical(loads(ns.expect.read_bytes()))==canonical(out),'exact saved receipt')
 else:ns.output.write_text(json.dumps(out,sort_keys=True,indent=2,allow_nan=False)+'\n')
 print('PASS: 193 matrices, faithful twenty-letter graph, Pell391, conditional six-gate target; no universal arithmetic bound')
if __name__=='__main__':main()
