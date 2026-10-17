#!/usr/bin/env python3
"""Measure the certified-empty transfer-loop specialization with Wade backend.

The two loop-entry zero invariants come from register_abstract.py. This
driver measures new compilations; it is not a verified binary compiler.
"""
import sys,json,hashlib,re
from pathlib import Path
from functools import lru_cache
from collections import Counter
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'wade'))
import TMBuilder
from register_abstract import parse
BASE=HERE/'inputs'
REGS=['nextproof','topwff','wffstack','axiomcode','param1','param2','scratch1','scratch2','prooflist']

def tree(nodes):
 def visit(e):
  k,*n=e.split()
  if k=='CN':return ('N',*(visit(f) for f in nodes[int(n[0])]))
  return (k[1:],int(n[0])) if n else (k[1:],)
 return visit('CN 0')

@lru_cache(None)
def bounds(e):
 if e[0]=='N':
  a,b=bounds(e[1]),bounds(e[2])
  return max(a[0]-1,b[0]),max(a[1],b[1]-1)
 return ((1 if e[0]=='D' else e[1] if e[0]=='B' else 0), e[1] if e[0]=='C' else 0)

def transform(t,cuts,simplify=False):
 def visit(e,p):
  if p in cuts:
   assert e==cuts[p] and bounds(e)==(0,0)
   return ('B',0)
  if e[0]!='N':return e
  a,b=visit(e[1],p+'0'),visit(e[2],p+'1')
  if simplify:
   if a==('B',0) and bounds(b)==(0,0):return b
   if b==('B',0) and bounds(a)==(0,0):return a
  return ('N',a,b)
 return visit(t,'')

def intern(t):
 seen={};nodes={}
 def visit(e):
  if e[0]!='N':return e
  p=(visit(e[1]),visit(e[2]))
  if p not in seen:seen[p]=len(seen);nodes[seen[p]]=p
  return ('N',seen[p])
 root=visit(t)[1]
 return nodes,root

def compile_t(t,label):
 nodes,root=intern(t);builder=TMBuilder.TMBuilder();regs=[builder.reg(n) for n in REGS]
 order=[root]+[i for i in nodes if i!=root];ren={n:i for i,n in enumerate(order)}
 def edge(e):
  if e[0]=='N':return ren[e[1]]
  if e[0]=='I':return regs[e[1]].inc
  if e[0]=='D':return regs[e[1]].decnz
  if e[0]=='H':return 'halt'
  return f'_{"break" if e[0]=="B" else "continue"}.{e[1]}'
 for i,n in enumerate(order):
  seq=TMBuilder.Sequence(tuple(edge(e) for e in nodes[n]));seq.name='main().0' if i==0 else f'global.{i}'
  builder.sequences.append(seq)
 builder.generate();builder.tm.gc();target=HERE/(label+'.tm');builder.tm.save(str(target))
 # Independently invert every emitted decoder edge, including control-level
 # offsets determined by its left/right bit. This detects an accidental
 # root renumbering or register permutation in this measured compilation.
 byname={('main().0' if i==0 else f'global.{i}'):n for i,n in enumerate(order)}
 for name,n in byname.items():
  for bit,want in enumerate(nodes[n]):
   action=builder.tm.states[name,str(bit)];dest=action.nextstate
   if dest in byname:got=('N',byname[dest])
   elif dest=='halt':got=('H',)
   elif m:=re.fullmatch(r'3\.(.*)\.(inc|decnz)',dest):got=('I' if m[2]=='inc' else 'D',REGS.index(m[1]))
   elif dest.startswith('6.break.'):got=('B',int(dest.rsplit('.',1)[1])+(bit==0))
   elif dest.startswith('6.continue.'):
    k=int(dest.rsplit('.',1)[1]);got=('B',0) if bit==0 and action.write=='1' else ('C',k+bit)
   else:raise AssertionError((name,bit,dest))
   assert got==want,(name,bit,want,got)
   direct=want[0] in ('N','I','D','H')
   assert action.write==(str(bit) if direct else '1' if want==('B',0) and bit==0 else '0')
   assert action.direction==('R' if direct else 'L')
 # Totalize the one missing binary row and give a complete numbered table.
 state_names={q for q,b in builder.tm.states};start=builder.tm.start
 state_order=[start]+sorted(state_names-{start});mapping={q:i for i,q in enumerate(state_order)}
 mapping['halt']=len(state_names);numbered=[];missing=[]
 for q in state_order:
  for bit in ('0','1'):
   action=builder.tm.states.get((q,bit))
   if action is None:write,direction,dest=bit,'R','halt';missing.append([q,int(bit)])
   else:write,direction,dest=action.write,action.direction,action.nextstate
   numbered.append(f'{mapping[q]} {bit} {write} {direction} {mapping[dest]}\n')
 total=HERE/(label+'_total.tm');total.write_text('#! start 0\n'+''.join(numbered))
 (HERE/(label+'_labels.json')).write_text(json.dumps(mapping,indent=2,sort_keys=True)+'\n')
 (HERE/(label+'.json')).write_text(json.dumps({'root':root,'nodes':nodes},indent=2)+'\n')
 return {'label':label,'nodes':len(nodes),'working_states':len({q for q,b in builder.tm.states}),'raw_rows':len(builder.tm.states),
         'total_binary_rows':len(numbered),'totalized_missing_pairs':missing,'all_decision_edges_reextracted':True,
         'table_sha256':hashlib.sha256(target.read_bytes()).hexdigest(),'total_table_sha256':hashlib.sha256(total.read_bytes()).hexdigest(),
         'edge_kinds':dict(Counter(e[0] for v in nodes.values() for e in v))}

def main():
 _,nodes,sites=parse(BASE/'Prog254.v');t=tree(nodes)
 cuts={'11101001011000110':('N',('D',6),('N',('I',5),('C',2))),
       '11111100':('N',('D',1),('N',('I',6),('C',2)))}
 results=[compile_t(t,'global_baseline')]
 for simplified in (False,True):results.append(compile_t(transform(t,cuts,simplified),'global_empty_loops'+('_simplified' if simplified else '')))
 (HERE/'global_compile_results.json').write_text(json.dumps({'cuts':cuts,'results':results,'scope':'Exact compiler measurements; global source optimization proved by stated invariant argument, compiler correctness not kernel-verified.'},indent=2)+'\n')
 print(json.dumps(results,indent=2))
if __name__=='__main__':main()
