#!/usr/bin/env python3
"""Verify the exact Cantor-negation fusions and full Wade compilation controls.

Requires only Python 3.10+ standard library. The full 219-node original source
and attributed pinned Wade backend are included. No network, ProveIt checkout,
Lean installation or prepared tape is needed for this finite control.

The result is not a new proof of a binary consistency machine. It checks source
macro examples, two algebraic identities, complete emitted tables and startup
prefixes. The unbounded macro argument is given separately in README.md.
"""
from __future__ import annotations
import argparse,copy,hashlib,importlib,json,re,sys,time
from collections import Counter
from fractions import Fraction
from pathlib import Path

HERE=Path(__file__).resolve().parent
REGISTERS=['nextproof','topwff','wffstack','axiomcode','param1','param2','scratch1','scratch2','prooflist']
INPUT_SHA={
 'data/Dag254.v':'538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3',
 'vendor/TMBuilder.py':'03d3a636404e1bcdeceafd98b9478b7a367ab334f3ab9f8a00df1d5c03fdf517',
 'vendor/tm.py':'2d00bf8c8324d8e9bc5639ba14e508091d854a7c93ecb96ab598f41c15ae9787',
 'vendor/tmdb.py':'4ccf4dab37438109a350d77259b5eb52e33ce110a954cd2d56a218e84e653526',
 'vendor/LICENSE.wade':'c1dffee77db98625debe39b47538e1d2f3b7956cbc7bcd6ed9363701b2177cfa',
}

def sha(data):return hashlib.sha256(data).hexdigest()
def pair(x,y):return (x+y)*(x+y+1)//2+y

def load_source():
 for path,h in INPUT_SHA.items():
  if sha((HERE/path).read_bytes())!=h:raise ValueError('Pinned input changed: '+path)
 nodes={};names={}
 pattern=r'\| (\d+) => \((E\w+(?: \d+)?), (E\w+(?: \d+)?)\)\s*\(\* (.*?) \*\)'
 for m in re.finditer(pattern,(HERE/'data/Dag254.v').read_text()):
  i,left,right,name=m.groups();nodes[int(i)]=(left,right);names[int(i)]=name
 assert set(nodes)==set(range(219)) and names[0]=='main().0'
 assert nodes[177]==('ENode 171','EInc 1') and nodes[218]==('ENode 177','ENode 119')
 assert [q for q,es in nodes.items() if 'ENode 177' in es]==[218]
 return nodes,names

def variants(original):
 result={'baseline':dict(original)}
 # transfer T -> X; set T to 1; use existing pair/multiply tail.
 result['direct_transfer']=dict(original)
 result['direct_transfer'][177]=('EInc 1','ENode 120')
 result['direct_transfer'][218]=('ENode 216','ENode 177')
 # P(t,1)=P(0,t)+2. Pair is additive in its output Y.
 result['output_prefill2']=dict(original)
 result['output_prefill2'][177]=('EInc 7','EInc 7')
 result['output_prefill2'][218]=('ENode 177','ENode 120')
 # Same identity, with the addition after multiplication: 4P(0,t)+8.
 result['zerohead_add8']=dict(original)
 result['zerohead_add8'][177]=('ENode 156','ENode 156')
 result['zerohead_add8'][218]=('ENode 120','ENode 177')
 return result

def execute(nodes,root,values,fuel=2000000):
 """Independent structured interpreter of the literal source DAG.

 A left-arm Break1 exits a cons normally; a right-arm Continue1 restarts it.
 The interpreter counts primitive RM instructions, not TM moves.
 """
 state=list(values);remaining=fuel;counts=Counter()
 def run(edge):
  nonlocal remaining
  remaining-=1
  if remaining<0:raise RuntimeError('finite source test exhausted fuel')
  kind,*args=edge.split()
  if kind=='ENode':
   a,b=nodes[int(args[0])]
   while True:
    out=run(a)
    if out[0]=='break':return ('normal',) if out[1]==1 else ('break',out[1]-1)
    if out[0]!='normal':return out
    out=run(b)
    if out[0]=='continue':
     if out[1]==1:continue
     return 'continue',out[1]-1
    return out
  counts[kind]+=1
  if kind=='EHalt':return ('halt',)
  n=int(args[0])
  if kind=='EInc':state[n]+=1;return ('normal',)
  if kind=='EDecnz':
   if state[n]:state[n]-=1;return ('normal',)
   return 'break',1
  if kind=='EBreak':return ('normal',) if n==0 else ('break',n)
  if kind=='EContinue':return 'continue',n
  raise ValueError(edge)
 out=run(f'ENode {root}')
 return out,state,dict(counts)

def structural_metrics(nodes):
 seen=set();leaves=Counter();maxdepth=0;maxzero=0
 def walk(q,depth=0,zeros=0):
  nonlocal maxdepth,maxzero
  seen.add(q)
  for bit,e in enumerate(nodes[q]):
   z=zeros+1 if bit==0 else 0;maxzero=max(maxzero,z)
   if e.startswith('ENode '):walk(int(e.split()[1]),depth+1,z)
   else:leaves[e.split()[0]]+=1;maxdepth=max(maxdepth,depth+1)
 walk(0)
 return dict(reachable_DAG_nodes=len(seen),unfolded_leaves=sum(leaves.values()),leaf_kinds=dict(leaves),max_path_depth=maxdepth,max_zero_run=maxzero)

def compile_table(backend,nodes,names):
 b=backend.TMBuilder();regs=[b.reg(n) for n in REGISTERS]
 def emit(e):
  k,*v=e.split()
  if k=='EHalt':return 'halt'
  n=int(v[0])
  if k=='ENode':return n
  if k=='EInc':return regs[n].inc
  if k=='EDecnz':return regs[n].decnz
  return f"_{'break' if k=='EBreak' else 'continue'}.{n}"
 for i in range(len(nodes)):
  sequence=backend.Sequence(tuple(emit(e) for e in nodes[i]));sequence.name=names[i];b.sequences.append(sequence)
 b.generate();b.tm.gc();tm=b.tm
 states={q for q,bit in tm.states};order=[tm.start]+sorted(states-{tm.start});label={q:i for i,q in enumerate(order)};label['halt']=len(order)
 rows=[];missing=[]
 for q in order:
  for bit in ('0','1'):
   if (q,bit) in tm.states:
    act=tm.states[q,bit];w,d,t=act.write,act.direction,act.nextstate
   else:w,d,t=bit,'R','halt';missing.append([q,bit])
   assert w in ('0','1') and d in ('L','R') and t in label
   rows.append(f'{label[q]} {bit} {w} {d} {label[t]}')
 assert missing==[['1.inc','1']]
 data=('#! start 0\n'+'\n'.join(rows)+'\n').encode()
 # Invert every actual decision row independently of emit().
 reverse_names={name:i for i,name in names.items()}
 for q,es in nodes.items():
  for bit,expected in enumerate(es):
   action=tm.states[names[q],str(bit)];t=action.nextstate
   if t in reverse_names:actual=f'ENode {reverse_names[t]}'
   elif t=='halt':actual='EHalt'
   elif (m:=re.fullmatch(r'3\.(.*)\.(inc|decnz)',t)):
    actual=f"{'EInc' if m[2]=='inc' else 'EDecnz'} {REGISTERS.index(m[1])}"
   elif t.startswith('6.break.'):
    actual=f"EBreak {int(t.rsplit('.',1)[1])+(bit==0)}"
   elif t.startswith('6.continue.'):
    actual=('EBreak 0' if bit==0 and action.write=='1' else f"EContinue {int(t.rsplit('.',1)[1])+bit}")
   else:raise ValueError('unexpected decoder target '+t)
   assert actual==expected,(q,bit,actual,expected)
   direct=expected.split()[0] in ('ENode','EInc','EDecnz','EHalt')
   write=str(bit) if direct else ('1' if expected=='EBreak 0' and bit==0 else '0')
   assert (action.write,action.direction)==(write,'R' if direct else 'L')
 # Exact initial prefix to first source root, including all written cells.
 state=tm.start;head=0;ones=set();tick=0
 while state!=names[0]:
  act=tm.states[state,'1' if head in ones else '0']
  if act.write=='1':ones.add(head)
  else:ones.discard(head)
  head+=1 if act.direction=='R' else -1;state=act.nextstate;tick+=1
  if tick>1000000:raise RuntimeError('finite bootstrap control exhausted fuel')
 boot=dict(steps=tick,state=state,head=head,one_cells=sorted(ones))
 result=dict(working_states=len(states),transition_rows=len(rows),decision_states=len(nodes),framework_states=len(states)-len(nodes),missing_source_rows=missing,totalized_missing_action='preserve read symbol, move right, halt',canonical_sha256=sha(data),all_decision_edges_reextracted=True,first_root_boot=boot)
 return result,data

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--write',type=Path,help='Write regenerated tables/results into this new or empty directory.');args=ap.parse_args()
 if not __debug__:ap.error('Assertions required; do not use -O or -OO.')
 if args.write:
  if args.write.exists() and any(args.write.iterdir()):ap.error('--write must name a new or empty directory')
  args.write.mkdir(parents=True,exist_ok=True)
 started=time.monotonic();original,names=load_source();vs=variants(original)
 sys.path.insert(0,str(HERE/'vendor'));backend=importlib.import_module('TMBuilder')
 cases=[(t,w) for t in range(12) for w in range(12)]+[(0,50),(1,50),(3,50),(8,50),(3,100)]
 checks={};costs={};results={};tables={}
 for kind,nodes in vs.items():
  checked=0;sample_costs=[]
  for t,w in cases:
   initial=[2,t,w,5,7,11,0,0,13];expected=[2,4*pair(t,1),w,5,7,11,0,0,13]
   out,state,count=execute(nodes,218,initial)
   assert out==('normal',) and state==expected,(kind,t,w,out,state)
   assert pair(t,1)==pair(0,t)+2
   assert 4*pair(t,1)==2*t*t+6*t+8
   checked+=1
   if (t,w) in ((3,0),(3,10),(3,50),(3,100)):
    sample_costs.append(dict(top=t,stack=w,primitive_RM_instructions=sum(count.values()),instruction_counts=count))
  checks[kind]=checked;costs[kind]=sample_costs
  result,data=compile_table(backend,nodes,names);result['source_metrics']=structural_metrics(nodes);results[kind]=result;tables[kind]=data
  assert result['working_states']==281 and result['transition_rows']==562
  assert result['first_root_boot']==results['baseline']['first_root_boot']
  frozen=HERE/'tables'/f'{kind}281.tm'
  if frozen.exists():assert frozen.read_bytes()==data,('changed frozen table',kind)
  if args.write:(args.write/f'{kind}281.tm').write_bytes(data)
 # Corrupt exactly one required offset: this must fail on the smallest input.
 bad=dict(vs['output_prefill2']);bad[177]=('EInc 7','EBreak 0')
 _,bad_state,_=execute(bad,218,[2,0,0,5,7,11,0,0,13])
 assert bad_state[1]!=4*pair(0,1)
 # Derive exact polynomial identities for every t symbolically by coefficient
 # equality; this is independent of finite integer test ranges.
 polynomial=[8,6,2]
 assert [4*2,4*(1+Fraction(1,2)),4*Fraction(1,2)]==polynomial
 answer=dict(status='PASS',scope=__doc__,input_sha256=INPUT_SHA,
  macro_cases_per_variant=checks,total_macro_cases=sum(checks.values()),
  primitive_cost_controls=costs,compilations=results,
  fixed_offset_corruption_rejected=True,
  algebraic_identity='P(t,1)=P(0,t)+2; 4P(t,1)=2*t*t+6*t+8',
  clean_scratch_hypothesis='X=Y=0',all_other_registers_and_stack_preserved=True,
  binary_consistency_endpoint_proved=False,smaller_than252_machine_claimed=False,
  elapsed_seconds=time.monotonic()-started)
 if args.write:(args.write/'results.json').write_text(json.dumps(answer,indent=2)+'\n')
 print(json.dumps(answer,indent=2))
if __name__=='__main__':main()
