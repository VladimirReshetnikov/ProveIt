#!/usr/bin/env python3
"""Literal residual-parameter MP splice on accepted command-order210 K215.
Own finite source/interface gates only; no physical allocation or runtime.
"""
import argparse,hashlib,json,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent/'vendor'))
import source_language as s
import source_splice as sp

def digest(b):return hashlib.sha256(b).hexdigest()
def write(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
def run(gate,regs,limit=100000):
 rows=s.sites((gate,('CH',None)));g=sp.cfg_intervals(rows);assert g==sp.cfg_arithmetic(rows)
 pc=0;regs=list(regs)
 for steps in range(limit):
  op,r,to=g[pc]
  if op=='CH':return regs,steps
  if op=='CI':regs[r]+=1;pc=to[0]
  elif op=='CD':positive=int(regs[r]>0);regs[r]-=positive;pc=to[positive]
  else:pc=to[0]
 raise ValueError('Finite source probe exceeded its explicit bound')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--source',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 raw=a.source.read_bytes();assert digest(raw)=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
 a.output.mkdir(exist_ok=False);rows=json.loads(raw);old=s.tree(rows);oldg=sp.cfg_intervals(rows);assert oldg==sp.cfg_arithmetic(rows)
 get=lambda lo,hi:sp.serial(sp.closed_forest(old,lo,hi))
 copyU=get(152,159);readMP=get(4591,4605);gate=get(4578,4590)
 assert copyU==((('CD',4),(('CI',1),(('CI',6),('CC',3)))),(('CD',6),(('CI',4),('CC',2))))
 assert [x[1:] for x in s.sites(readMP)]==[(o,4 if o=='CI' and r==5 else r) for _,o,r in s.sites(get(159,173))]
 assert sp.cfg_intervals(s.sites(readMP))==[(o,4 if o=='CI' and r==5 else r,to) for o,r,to in sp.cfg_intervals(s.sites(get(159,173)))]
 assert s.subtree(gate,'0110')==(('CD',6),('CC',2))
 consume=(('CD',4),(('CI',1),('CC',2)))
 gateH=sp.apply_closed_splices(gate,{(5,7):(('CD',5),(('CI',4),('CC',2)))})
 gateX=s.replace(gate,'0110',(('CD',6),(('CI',4),('CC',2))))
 variants=[]
 for name,newgate in [('h',gateH),('x',gateX)]:
  edits={(152,159):consume,(4578,4590):newgate,(4591,4605):None}
  assert all(v is None or s.boundary(v)==(0,0,False) for v in edits.values())
  new=sp.apply_closed_splices(old,edits);rr=s.sites(new);g=sp.cfg_intervals(rr)
  assert g==sp.cfg_arithmetic(rr) and s.graph_intervals(rr)==s.graph_arithmetic(rr)[0]
  # Independent ordinal binding of every retained instruction and guarded edge.
  mapping={};replacement={};cursor=0
  for i in range(len(rows)):
   covered=next(((lo,hi,v) for (lo,hi),v in edits.items() if lo<=i<hi),None)
   if covered:
    lo,hi,v=covered
    if i==lo:replacement[lo]=(cursor,0 if v is None else sp.size(v));cursor+=0 if v is None else sp.size(v)
   else:mapping[i]=cursor;cursor+=1
  assert cursor==len(rr)
  def redirect(target):
   if target in mapping:return mapping[target]
   for (lo,hi),v in edits.items():
    if lo<=target<hi:
     assert target==lo,('outside edge enters macro interior',target,lo,hi)
     return replacement[lo][0] if v is not None else redirect(hi%len(rows))
   raise AssertionError(target)
  edges=0
  for i,j in mapping.items():
   op,r,to=oldg[i];expected=(op,r,tuple(redirect(t) for t in to))
   assert g[j]==expected,(i,j,g[j],expected);assert tuple(rr[j][1:])==tuple(rows[i][1:]);edges+=len(to)
  # Complete finite macro interface probes, with arbitrary unaffected counters.
  gate_cases=0
  for A in range(40):
   for C in range(40):
    initial=[2,17,3,4,0,A,C,5,6];got,steps=run(newgate,initial)
    expected=initial[:];expected[1]=0 if A==C else 17;expected[4]=max((A-C if name=='h' else C-A)-1,0);expected[5]=expected[6]=0
    assert got==expected;gate_cases+=1
  load_cases=0
  for U in range(16):
   for T in range(16):
    initial=[2,T,3,4,U,5,0,6,7];before,_=run(copyU,initial);after,_=run(consume,initial)
    expected=initial[:];expected[1]+=U
    assert before==expected;expected[4]=0;assert after==expected;load_cases+=1
  out=a.output/name;out.mkdir();encoded=s.compact(rr);(out/'sites.json').write_bytes(encoded)
  result={'name':name,'source_sha256':digest(encoded),'metrics':s.metrics(new),'guarded_cases':sum(2 if x[1]=='CD' else 1 for x in rr),
   'old_splices':[[lo,hi,0 if v is None else sp.size(v)]for(lo,hi),v in edits.items()],
   'retained_instructions':len(mapping),'retained_guarded_edges':edges,'outside_edges_exact_under_splice_ordinal_map':True,
   'both_full_CFG_resolvers_agree':True,'gate_cases':gate_cases,'load_cases':load_cases,
   'residual':'max(A-C-1,0)'if name=='h'else'max(C-A-1,0)',
   'command_order':{'NIP':0,'DROP':1,'MP':2,'AX':'c+3'},'MP_numeric_field_removed':True,
   'scope':'Source reconstruction, full outside control binding, isolated finite macro probes. Ordinary all-natural macro argument separate; no physical allocation, startup or full runtime.'}
  write(out/'source-review.json',result);variants.append(result)
 result={'status':'PASS_LITERAL_SOURCE_AND_FINITE_INTERFACE_GATES','baseline':{'path':str(a.source),'sha256':digest(raw)},'variants':variants,
 'source_edits':'Only last U copy becomes consuming transfer, second AX equality cleanup retains one residual, and MP parameter-read14 leaves are removed.'}
 write(a.output/'result.json',result);print(json.dumps(result,indent=2))
if __name__=='__main__':main()
