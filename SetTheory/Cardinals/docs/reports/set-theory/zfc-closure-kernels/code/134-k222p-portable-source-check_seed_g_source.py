#!/usr/bin/env python3
"""Build and independently bind the seed-K + G source for the 222-state candidate.

The source construction is deterministic. Independent checks use symbolic formula
execution, finite all-register macro bisimulations, exact full primitive words,
and two complete guarded-control-flow resolvers. The checks do not assert binary
runtime or end-to-end proof-assistant verification; those are separate layers.

Python 3.10+, standard library, assertions enabled. Run from any directory.
"""
from pathlib import Path
from functools import cache
from collections import defaultdict
import argparse,hashlib,json,re,sys
import source_language as s
from local_bisimulation import check as bisimulation
from audit_native_decoding import check as decode_sides
ROOT=Path(__file__).resolve().parent
TARGET='11101001001110'
ROTATE='1110100100111000'
PINS={
 'inputs/seed223_sites.json':'df55079f114a6aa9ada970d7d857726e47e3a3dba2a721245ebbacfd4577c13c',
 'inputs/seed223_grammar.json':'8b8dd4e165d8a08f7def72eca7f345da231aa3f0c7e318f3e23fddfa8b368f6a',
 'inputs/parent225_sites.json':'309358206463f8e8d88d86304e7c9f2273e3cdde64984b6db20c412516010878',
 'inputs/parent225.k.tm':'4526bd8cf2160ac5dfce039add0550e9788095f60ecc6b4462afd4ebbfd42790',
 'inputs/macro_data.json':'e5b3a18866d5071cf0e2f96fee739fa90af972628e6e3afd6c7ba5050b8588e9',
 'inputs/Dag230.v':'7f44c6bc6cb2e5a7a30c1267738c8df7bfd8e036987721ac0bb6bdc326e54eaf',
 'inputs/ProgLib230.v':'6af4a13b2034b867054f5b74e7635a305172b6a45f58db91dffe63ae57d50dbb',
 'source_language.py':'4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f',
 'local_bisimulation.py':'392cd18655e027cd81b902070be6bb168bd28d565f28521708852b3df643d14e',
 'audit_native_decoding.py':'fa84223949e1cb196419c013ff22f342b59bdeb28d12c0522cbb44029ab8cc67',
}
SOURCE_SHA='cc1fbb3a16dd446af9c7cdb678317d31060082e6794b9c7074ce02b46584a75e'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def freeze(x):return tuple(map(freeze,x)) if isinstance(x,list) else x
@cache
def size(n):return 1 if s.leaf(n) else size(n[0])+size(n[1])
def flat(n):return tuple((op,arg) for p,op,arg in s.sites(n))
def seq(xs):
 assert xs
 t=xs[-1]
 for x in reversed(xs[:-1]):t=x,t
 return t

def read_table(path):
 table={}
 for line in path.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,n=line.split();table[int(q),int(b)]=(int(w),1 if d=='R' else -1,int(n))
 return table

def decoder_map(table,t):
 groups=defaultdict(set)
 def walk(n,p,q):
  if s.leaf(n):return
  groups[q].add(n)
  for bit in (0,1):
   if s.leaf(n[bit]):continue
   tape={i:int(x) for i,x in enumerate(p+str(bit))};tape[-1]=1
   before=tape.copy();h=len(p);state=q
   for tick in range(100):
    if h==len(p)+1:break
    assert h in tape
    w,d,state=table[state,tape[h]];tape[h]=w;h+=d
   assert h==len(p)+1 and tape==before
   walk(n[bit],p+str(bit),state)
 walk(t,'',84)
 return groups

def replace_intervals(root,replacements):
 replacements=sorted(replacements)
 def visit(n,start):
  end=start+size(n)
  overlaps=[x for x in replacements if x[0]<end and start<x[1]]
  if not overlaps:return n
  for lo,hi,replacement in overlaps:
   if lo<=start and end<=hi:return replacement if start==lo else None
  assert not s.leaf(n)
  left=visit(n[0],start);right=visit(n[1],start+size(n[0]))
  if left is None:return right
  if right is None:return left
  return left,right
 return visit(root,0)

def closed_chunks(t,lo,hi):
 result=[]
 def walk(n,offset):
  end=offset+size(n)
  if offset>=hi or end<=lo:return
  if lo<=offset and end<=hi:
   assert s.boundary(n)==(0,0,False)
   result.append(n);return
  assert not s.leaf(n)
  walk(n[0],offset);walk(n[1],offset+size(n[0]))
 walk(t,0)
 assert sum(map(size,result))==hi-lo
 return result

def I(x,y):return 'I',x,y
def R(x,y):return 'R',x,y
def Q(x,y):return 'Q',x,y
def E(x,y):return 'E',x,y
def N(x):return I(x,1)
def execute(word):
 top='old_top';stack=['arbitrary_old_stack']
 for macro in word:
  if macro in (166,121,168,177):
   stack.append(top);top={166:'a',121:'b',168:'c',177:1}[macro]
  elif macro==218:top=N(top)
  else:top={119:I,181:R,180:Q,182:E}[macro](stack.pop(),top)
 assert stack==['arbitrary_old_stack','old_top']
 return top

def formulas():
 a,b,c='a','b','c'
 rel=R(b,c)
 subset=Q(c,I(R(c,a),R(c,b)))
 request=Q(b,I(c,N(Q(b,I(c,N(rel))))))
 closure=Q(a,I(subset,request))
 hereditary=Q(b,I(rel,N(Q(a,I(c,N(closure))))))
 neg_core=Q(c,I(hereditary,N(request)))
 rv=I(R(a,b),Q(c,R(a,b)))
 helper=I(E(a,b),Q(R(a,b),E(a,b)))
 seed_bundle=N(I(rv,I(helper,neg_core)))
 combined_bundle=N(I(rv,neg_core))
 g_row=I(E(c,a),I(E(c,b),Q(R(a,b),E(a,b))))
 old_row=I(E(c,a),I(E(c,b),E(a,b)))
 return dict(seed_bundle=seed_bundle,combined_bundle=combined_bundle,g_row=g_row,old_row=old_row)

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--source',type=Path,default=ROOT/'sites222.json')
 ap.add_argument('--output',type=Path,default=ROOT/'source_receipt.json')
 ap.add_argument('--write-source',type=Path,help='Optional path to write reconstructed source bytes')
 args=ap.parse_args()
 assert __debug__ and not sys.flags.optimize,'Run without Python optimization'
 for path,pin in PINS.items():assert sha((ROOT/path).read_bytes())==pin,path
 parent=s.tree(json.loads((ROOT/'inputs/parent225_sites.json').read_text()))
 seed=s.tree(json.loads((ROOT/'inputs/seed223_sites.json').read_text()))
 groups=decoder_map(read_table(ROOT/'inputs/parent225.k.tm'),parent)
 def q(k):
  assert len(groups[k])==1
  return next(iter(groups[k]))
 grammar=json.loads((ROOT/'inputs/seed223_grammar.json').read_text())
 assert grammar['variant']=='seedrequest-s0-p0-r1-o120-hR'
 oldword=grammar['macro_word'];f=formulas()
 assert execute(oldword)==f['seed_bundle']==freeze(grammar['expression'])
 data=json.loads((ROOT/'inputs/macro_data.json').read_text())
 macros={int(k):freeze(v) for k,v in data['macros'].items()}
 assert all(s.boundary(n)==(0,0,False) for n in macros.values())
 raw=(ROOT/'inputs/Dag230.v').read_text()
 dag={int(q):(a,b) for q,a,b in re.findall(r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)',raw)}
 @cache
 def expand(q):
  def edge(ed):
   if ed=='EHalt':return 'CH',None
   kind,arg=ed.split();arg=int(arg)
   if kind=='ENode':return expand(arg)
   return {'EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC'}[kind],arg
  return tuple(edge(ed) for ed in dag[q])
 contracts={}
 for k,n in macros.items():
  proof=bisimulation(expand(k),n)
  contracts[str(k)]={key:value for key,value in proof.items() if key!='pairs'}
 def wordflat(w):return sum((flat(macros[k]) for k in w),())
 oldrow=[168,166,182,168,121,182,166,121,182,119,119]
 grow=[168,166,182,168,121,182,166,121,181,166,121,182,180,119,119]
 assert execute(oldrow)==f['old_row'] and execute(grow)==f['g_row']
 assert flat(seed)[486:786]==wordflat(oldrow)
 assert oldword[:9]==[166,121,181,168,166,121,181,180,119]
 assert oldword[9:20]==[166,121,182,166,121,181,166,121,182,180,119]
 assert oldword[-3:]==[119,119,218]
 newword=oldword[:9]+oldword[20:-2]+oldword[-1:]
 assert len(newword)==65 and execute(newword)==f['combined_bundle']
 starts=[2541]
 for k in oldword:starts.append(starts[-1]+size(macros[k]))
 assert starts[-1]==4781
 assert flat(seed)[2541:4781]==wordflat(oldword)
 rel,eq,all_,pairinc=q(155),q(182),q(86),q(99)
 assert flat(rel)==wordflat([166,121,181])
 assert flat(eq)==wordflat([166,121,182])
 assert flat(all_)==wordflat([180])
 assert flat(seed)[648:732]==flat((pairinc,eq))
 replacement=((pairinc,(rel,eq)),all_)
 initial=replace_intervals(seed,[(648,732,replacement),
     (starts[9],starts[20],None),(starts[-3],starts[-2],None)])
 old_node=s.subtree(initial,ROTATE)
 x,y=old_node[0];z=old_node[1]
 assert all(s.boundary(v)==(0,0,False) for v in (x,y,z))
 final=s.replace(initial,ROTATE,(x,(y,z)))
 raw_final=s.compact(s.sites(final))
 assert sha(raw_final)==SOURCE_SHA
 assert args.source.read_bytes()==raw_final,'Delivered source differs from deterministic reconstruction'
 if args.write_source:args.write_source.write_bytes(raw_final)
 # Independent primitive-word binding: only the full rho7 row and full bundle change.
 oldflat=flat(seed)
 expected=oldflat[:486]+wordflat(grow)+oldflat[786:2541]+wordflat(newword)+oldflat[4781:]
 assert flat(final)==expected and len(expected)==4744
 # Independent reference: split the old closed emitter at checked boundaries,
 # insert complete macros, and preserve the rest of the source literally.
 oldax=s.subtree(parent,TARGET)
 assert size(oldax)==4004
 prefix=[pairinc,rel,eq,all_]+closed_chunks(oldax,84,1893)
 suffix=closed_chunks(oldax,3970,4004)
 assert all(s.boundary(v)==(0,0,False) for v in prefix+suffix)
 referenceax=seq(prefix+[macros[k] for k in newword]+suffix)
 reference=s.replace(parent,TARGET,referenceax)
 assert flat(reference)==flat(final)
 gf,nf=s.graph_arithmetic(s.sites(final))
 gr,nr=s.graph_arithmetic(s.sites(reference))
 gi,ni=s.graph_arithmetic(s.sites(initial))
 assert gf==gr==gi==s.graph_intervals(s.sites(final))==s.graph_intervals(s.sites(reference))
 # Rebind the inherited seed source independently to the seed formula and unchanged body.
 oldprefix=closed_chunks(oldax,0,1893)
 seed_referenceax=seq(oldprefix+[macros[k] for k in oldword]+suffix)
 assert flat(seed_referenceax)==flat(s.subtree(seed,TARGET))
 assert s.replace(seed,TARGET,oldax)==parent
 seedproof=bisimulation(seed_referenceax,s.subtree(seed,TARGET))
 localproof=bisimulation(referenceax,s.subtree(final,TARGET))
 assert s.boundary(s.subtree(final,TARGET))==(0,0,False)
 metrics=s.metrics(final)
 assert metrics==dict(dag_nodes=208,leaf_occurrences=4744,maximum_depth=36,maximum_zero_run=6)
 result=dict(status='SEED_G222_EXACT_ALL_NATURAL_EMITTER_AND_SOURCE_PASS',
  source_sha256=SOURCE_SHA,source_metrics=metrics,
  input_pins=PINS,macro_contracts=contracts,
  row=dict(old_word=oldrow,new_word=grow,old_expression=f['old_row'],new_expression=f['g_row'],
   old_interval=[486,786],old_primitive_count=300,new_primitive_count=409),
  bundle=dict(old_word=oldword,new_word=newword,old_expression=f['seed_bundle'],new_expression=f['combined_bundle'],
   old_interval=[2541,4781],old_primitive_count=2240,new_primitive_count=1913),
  all_other_primitive_instructions_unchanged=True,eight_logical_row_positions_retained=True,
  arithmetic_decode_sideconditions=dict(bundle=decode_sides(f['combined_bundle']),row=decode_sides(f['g_row']),
   bundle_hypothesis='c != a and c != b; actual opaque matrix code equals private binder c'),
  source_reference=dict(full_graph_equality=True,independent_resolvers=2,guarded_cases=nf,
   reference_guarded_cases=nr,seed_local_bisimulation_boundaries=seedproof['test_pairs'],
   combined_local_bisimulation_boundaries=localproof['test_pairs']),
  rotation=dict(path=ROTATE,direction='right',factors_closed=True,whole_graph_preserved=True),
  gate='if c=a or c=b then 0 else And(V_R(a,b,c), Exists_c(And(H,W))) with recorded fusions',
  scope='All natural a,b,c and arbitrary prior top/stack with inherited clean-scratch macro interface. Finite structural and induction certificates, no bounded register sampling. Theory calibration, enumeration, blank startup and binary runtime remain separate proof layers.')
 args.output.parent.mkdir(parents=True,exist_ok=True)
 args.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k] for k in ('status','source_sha256','source_metrics','source_reference')},indent=2))
if __name__=='__main__':main()
