#!/usr/bin/env python3
"""Check the 217-state initialized core and its definite blank-start failure.

This is NOT a 217-state blank-tape consistency construction.  --runtime
replays the quantified primitive contracts using the pinned inherited symbolic
engine.  The default checks exact construction, full blank-start failure,
and a positive control using the accepted K218 initialization.
"""
from pathlib import Path
import argparse, hashlib, json, sys, time
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sys.path.insert(0,str(HERE/'vendor'))
import independent_runtime as concrete

PINS={
 'baseline218/k218.native.tm':'2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f',
 'baseline218/sites218.json':'b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9',
 'core217/core.native.tm':'c3d90a672481086329d8ed93da24a885d80a553ae6298b3a6444bea0fd5cee53',
 'core217/vendor/symbolic_runtime.py':'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145',
 'core217/vendor/independent_runtime.py':'0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346',
 'core217/vendor/legacy_mapping.json':'26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf'}

def require(test,msg):
 if not test:raise ValueError(msg)
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def dump(path,obj):path.write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def run_blank(table,count,trace=False):
 q=h=0;ones=set();history=[]
 for tick in range(count):
  bit=int(h in ones);w,d,z=table[q,bit]
  if trace:history.append([tick,q,h,bit,w,d,z])
  if w:ones.add(h)
  else:ones.discard(h)
  h+=d;q=z
 return (q,h,ones),history

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--runtime',action='store_true')
 ap.add_argument('--output',type=Path,default=HERE/'fresh')
 args=ap.parse_args();require(__debug__ and not sys.flags.optimize,'Assertions must be enabled')
 args.output.mkdir(parents=True,exist_ok=True)
 for path,sha in PINS.items():require(digest(ROOT/path)==sha,'Input drift: '+path)
 old=concrete.table(ROOT/'baseline218/k218.native.tm');tab=concrete.table(HERE/'core.native.tm')
 expected={(q,b):a for(q,b),a in old.items()if q!=301}
 require(old[87,0]==(0,1,301),'Original entry changed')
 expected[87,0]=(0,1,88);expected[88,0]=(0,-1,51);expected[51,0]=(0,1,122)
 require(expected==tab,'Unexpected core construction')
 states={q for q,b in tab};require(len(states)==217 and len(tab)==434,'State census')
 require(set(tab)=={(q,b)for q in states for b in(0,1)},'Incomplete table')
 require({z for w,d,z in tab.values()}-states=={254},'Bad target')
 failed,trace=run_blank(tab,85,True)
 require(failed==(35,7,{-3,-2}),'Unexpected blank endpoint')
 require(tab[35,0]==(1,1,35),'Ray rule changed')
 # Induction: after n further steps q=35,h=7+n and ones={-3,-2} union [7,7+n).
 control,_=run_blank(old,312909)
 expected_tape={x-5 for x in concrete.frame('',[3,0,0,0,3,0,0,0,0],[1]*130,80)}
 require(control==(84,-5,expected_tape),'Accepted K218 positive control failed')
 receipt={'status':'INITIALIZED_CORE_ONLY_BLANK_START_REFUTED','states':217,'rows':434,
  'core_sha256':PINS['core217/core.native.tm'],'blank_steps_to_ray':85,
  'blank_endpoint':{'state':35,'head':7,'ones':[-3,-2]},'ray_action':[1,1,35],
  'blank_nonhalting':'Unconditional, by induction on the fresh rightward zero cell.',
  'baseline_positive_control':{'steps':312909,'state':84,'head':-5,'logical_registers':[3,0,0,0,3,0,0,0,0],'gap':80,'spares':[1]*130,'one_cells':len(expected_tape)},
  'driver_sha256':digest(Path(__file__)),'pins':PINS}
 dump(args.output/'construction_and_failure.json',receipt);dump(args.output/'blank_trace.json',trace)
 print('CONSTRUCTION_AND_BLANK_FAILURE_PASS',flush=True)
 if not args.runtime:return
 import symbolic_runtime as runtime
 mapping={int(q):int(z)for q,z in json.loads((HERE/'vendor/legacy_mapping.json').read_text()).items()}
 mapping.update({301:1301,302:1302})
 require(len(set(mapping.values()))==len(mapping),'Noninjective legacy map')
 legacy={(mapping[q],b):(w,d,mapping[z])for(q,b),(w,d,z)in tab.items()}
 sites=json.loads((ROOT/'baseline218/sites218.json').read_text())
 require(len(sites)==4744,'Source census')
 start=time.monotonic();lemmas,blocks=runtime.prove_blocks(legacy)
 cases=[];rows=set()
 for i,site in enumerate(sites):
  for positive in((False,True)if site[1]=='CD'else(False,)):
   ans=runtime.case(legacy,lemmas,site,positive)
   rows.update(ans.pop('rows'));ans.pop('trace')
   require(ans['duration'][0]>0,'Nonpositive finite block')
   cases.append({'index':i,'positive':positive,**ans})
   if len(cases)%500==0:print('PROVED',len(cases),round(time.monotonic()-start,2),flush=True)
 require(len(cases)==6167,'Incomplete guarded census')
 require(len(rows)==434,'Incomplete row coverage')
 # The same symbolic engine must reject a dispatch transition changed to halt.
 corrupt=dict(legacy);corrupt[96,0]=(0,1,254)
 try:runtime.case(corrupt,lemmas,sites[0],False)
 except Exception as err:negative={'status':'REJECTED','error':str(err)}
 else:raise ValueError('Initial-halt negative control was accepted')
 result={'status':'ALL_PRIMITIVE_INTERFACES_PROVED','scope':'Initialized frames only; the blank-start failure above remains.',
  'states':217,'rows':434,'cases':len(cases),'symbolic_steps':sum(c['symbolic_steps']for c in cases),
  'minimum_duration_constant':min(c['duration'][0]for c in cases),'direct_rows':len(rows),
  'seconds':time.monotonic()-start,'negative_control':negative,'block_schemas':blocks,
  'quantifiers':'Nine independent arbitrary natural registers, arbitrary natural extra gap, arbitrary first spare, arbitrary finite spare tail; both decrement guards.',
  'proof_level':'Executable mathematical certificate; no new proof-assistant or internal PA endpoint.',
  'core_sha256':PINS['core217/core.native.tm'],'source_sha256':PINS['baseline218/sites218.json'],
  'driver_sha256':digest(Path(__file__)),'pins':PINS}
 dump(args.output/'runtime.json',result);dump(args.output/'cases.json',cases)
 print(json.dumps({k:v for k,v in result.items()if k not in('block_schemas','pins')},indent=2),flush=True)
if __name__=='__main__':main()
