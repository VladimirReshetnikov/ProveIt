#!/usr/bin/env python3
"""Replay two rejected conceptual reductions, using only bundled inputs.

No new search variant is generated. The fold counts are matching sizes in
one finite opportunity census, not certified folded machines or global
lower bounds. The parity raw source contracts are replayed in full.
"""
from pathlib import Path
import argparse,hashlib,json,sys,tempfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
sys.path.insert(0,str(ROOT/'construction/vendor'))
import compiler as c, support as s

INC=('leaf','inc',1)
def tup(t):return tuple(map(tup,t))if isinstance(t,list)else t
def leaves(t):return leaves(t[0])+leaves(t[1])if c.isnode(t)else[t]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def deleted():
 raw=s.read_table(ROOT/'construction/inputs/parent.raw.native.tm')
 c.machine=lambda:(raw,[])
 c.MACROS[(INC,INC)]=99
 c.MACROS[((INC,INC),(INC,INC))]=190
 t=c.read_grammar(ROOT/'construction/inputs/parent.grammar.json')
 def deletefirst(t):
  if c.isnode(t[0]):return deletefirst(t[0]),t[1]
  assert t[0]=='node58'
  return t[1]
 cases=[]
 for name,u in [('PA194G',t),('deleted_copyH',deletefirst(t))]:
  rows,index,shape=c.build(u)
  matching=c.max_matching(c.opportunities_fast(rows,shape))
  cases.append({'case':name,'macro_tokens':len(leaves(u)),'raw_controls':len(rows)//2,
    'AX_readers':len(shape),'matching_size':len(matching),
    'optimistic_controls_after_matching':len(rows)//2-len(matching)})
 assert [(x['macro_tokens'],x['AX_readers'],x['matching_size'],x['optimistic_controls_after_matching'])for x in cases]==[(190,67,7,194),(189,67,7,194)]
 return {'status':'REPLAY PASS; rejected reduction','cases':cases,
   'semantic_change':'The AX prefix forms U(c,t) instead of U(c,h) and no longer saves the unmodified old top.',
   'barrier':'The existing all-store Push/Pop/selector proof no longer applies. No replacement modalized completeness compiler was established.',
   'scope':'Grammar-cost replay only. No physical startup/runtime verification, no accepted changed machine, and no state-count lower bound.'}

def parity(output):
 raw=s.read_table(HERE/'inputs/radix6.raw.tm')
 c.machine=lambda:(raw,[])
 c.MACROS[(INC,INC)]=99
 c.MACROS.pop(((INC,INC),(INC,INC)),None)
 c.MACROS.pop('node61',None)
 def norm(t):
  if t=='node60':return INC,INC
  return tuple(map(norm,t))if c.isnode(t)else t
 t=norm(c.read_grammar(HERE/'inputs/radix6.grammar.json'))
 w=leaves(t);ends=[]
 for j,x in enumerate(w):
  if x==INC and (j==len(w)-1 or w[j+1]!=INC):
   start=j
   while start and w[start-1]==INC:start-=1
   if j-start+1==3:ends.append(j)
 assert ends==[63,75,91]
 def insert(t,counter):
  if c.isnode(t):return insert(t[0],counter),insert(t[1],counter)
  j=counter[0];counter[0]+=1
  return (t,INC)if j in ends else t
 u=insert(t,[0])
 raw[68,0]=(0,True,108)
 raw[500,0]=raw[108,0];raw[500,1]=(1,True,68)
 raw[53,0]=(0,True,500)
 raw[38,1]=(1,True,30)
 raw[310,1]=(0,False,16)
 raw[34,0]=(0,False,501)
 raw[501,0]=(0,False,75);raw[501,1]=(1,False,2)
 rows,index,shape=c.build(u)
 controls={q for q,b in rows}
 eligible={q:1 for q in controls if q not in c.BOXSTATES}
 matching=c.max_matching(c.opportunities_fast(rows,eligible))
 assert(len(controls),len(shape),len(matching))==(205,68,7)
 ns={k:tup(v)for k,v in json.loads((HERE/'inputs/radix6.nodes.json').read_text()).items()}
 ns['node7']=(('leaf','dec',6),('node0',('leaf','halt',None)))
 ns['node168']=('node37','node56')
 ns['node172']=('node21',('node170',('leaf','continueTo',2)))
 c.raw_nodes=lambda:ns
 sites,ins,contracts=c.source(u)
 assert(len(sites),len(contracts))==(3787,4890)
 runtime=c.validate(rows,contracts)
 assert runtime=={'ok':True,'contracts':4890,'max_steps':488,'total_steps':1540591}
 text=s.table_text(rows)
 assert text==(HERE/'recorded/parity6.raw.tm').read_text()
 assert json.loads(json.dumps(u))==json.loads((HERE/'recorded/parity6.grammar.tree.json').read_text())
 (output/'parity6.raw.tm').write_text(text)
 (output/'parity6.grammar.tree.json').write_text(json.dumps(u)+'\n')
 return {'status':'REPLAY PASS; rejected reduction','codec':'I=6p, M=6p+1, U=6p+2, E=6p+4; odd-code halt test',
   'changed_equality_tag_ends':ends,'raw_controls':205,'fixed_controls':137,'AX_readers':68,
   'matching_size':7,'optimistic_controls_after_matching':198,'matching':matching,
   'source_sites':len(sites),'source_outcomes':len(contracts),'raw_symbolic_runtime':runtime,
   'raw_table_sha256':hashlib.sha256(text.encode()).hexdigest(),
   'scope':'Raw source-to-machine contracts only. No blank-start calibration, no certified simultaneous folded table, no Con(PA) equivalence, and no global lower bound.'}

def main():
 if not __debug__ or sys.flags.optimize:raise RuntimeError('Run with assertions enabled.')
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path)
 a=p.parse_args();out=a.output or Path(tempfile.mkdtemp(prefix='pa-negative-replay-'));out.mkdir(parents=True,exist_ok=True)
 result={'status':'PASS','deleted_copyH':deleted(),'parity6':parity(out)}
 (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
