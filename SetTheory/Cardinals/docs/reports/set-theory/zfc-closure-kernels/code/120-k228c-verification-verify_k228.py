#!/usr/bin/env python3
"""Portable literal-table, dense-startup, and unbounded-runtime check for K228.

All CLI paths are explicit or relative to this file. Python3.10+ standard
library only; assertions must remain enabled. --quick checks construction
and the exact finite bootstrap and never emits a universal-runtime PASS.
"""
from pathlib import Path
import argparse,hashlib,importlib,json,sys,time
import table_reconstruction as build
ROOT=Path(__file__).resolve().parent
ENGINE_SHA='c046b4f7989dc198f067bde1de46e425682ba07bcdfc4bd91bc61a712498db79'
HELPER_SHA='a907dc901126ed7f2f40b2c767fd0f51558f9f65db8e9c7390f5db9c1701bd81'
CASE_SHA='d1a5732b35596ac20511bd8dd1c28f0d8895f3476ea5fa7c17d86454bab15961'
require=build.require

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def write(path,value):Path(path).write_text(json.dumps(value,indent=2)+'\n')
def source_check(sites):
 require(isinstance(sites,list) and len(sites)==5121,'Wrong source-leaf count')
 leaves=set();prefixes=set()
 for row in sites:
  require(isinstance(row,list) and len(row)==3,'Malformed source row');pc,op,arg=row
  require(isinstance(pc,str) and pc and len(pc)<=64 and set(pc)<={'0','1'} and pc not in leaves,'Malformed or duplicate source path')
  require(op in('CI','CD','CB','CC','CH'),'Wrong source opcode')
  require(arg is None if op=='CH' else type(arg) is int and arg>=0,'Wrong source operand')
  if op in('CI','CD'):require(arg<9,'Wrong source register')
  leaves.add(pc);prefixes.update(pc[:i] for i in range(len(pc)))
 require(not(leaves&prefixes),'Source is not prefix-free')
 require(all(p+b in leaves or p+b in prefixes for p in prefixes for b in('0','1')),'Source prefix tree is not full')
 cases=sum(2 if row[1]=='CD' else 1 for row in sites);require(cases==6656,'Wrong guarded-case count')
 return {'leaf_count':len(leaves),'guarded_cases':cases,'complete_binary_prefix_tree':True,'maximum_depth':max(map(len,leaves))}

def dense(table,start,steps):
 # This fixed tape is sufficient only for the fully specified bootstrap.
 # Every visited head position is range-checked, so the untouched infinite
 # zero exterior is represented exactly; it is not a runtime-value bound.
 center=4096;cells=bytearray(16384);q=start;h=center;lo=hi=h
 for tick in range(steps):
  require(0<=h<len(cells),'Finite bootstrap crossed the represented boundary')
  require((q,int(cells[h])) in table,f'Bootstrap halted before prescribed step {tick}')
  w,d,z=table[q,int(cells[h])];cells[h]=w;q=z;h+=d
  require(0<=h<len(cells),'Finite bootstrap crossed the represented boundary')
  lo=min(lo,h);hi=max(hi,h)
 return q,h-center,{i-center for i,b in enumerate(cells) if b},[lo-center,hi-center]

def startup(old,canonical,construction):
 oq,oh,oo,of=dense(old,0,408419);nq,nh,no,nf=dense(canonical,0,409835)
 require((oq,oh,len(oo))==(84,-5,351),'Released K230 bootstrap differs')
 require(nq==construction['dispatcher'] and nh==oh and no==oo,'Canonical K228 bootstrap has a different whole-tape seed')
 header=min(p for p in no if p>=nh);require(min(no)==nh-1 and header==176,'Wrong marker or header')
 pos=header+1;last=max(no);values=[]
 while pos<=last:
  require(pos not in no and pos+1 in no,'Malformed unary register block');pos+=1;begin=pos
  while pos in no:pos+=1
  values.append(pos-begin-1)
 require(values[:9]==[0,0,0,3,0,0,3,0,0] and values[9:]==[1]*167,'Wrong physical seed or spare tail')
 return {'status':'INDEPENDENT_DENSE_CANONICAL_STARTUP_PASS','original_steps':408419,'canonical_steps':409835,'original_final_state':oq,'canonical_final_state':nq,'head':nh,'header':header,'marker':nh-1,'physical_registers':values[:9],'spare_values':values[9:],'one_cells':sorted(no),'every_other_integer_cell':0,'original_head_footprint':of,'canonical_head_footprint':nf,'scope':'Exact prescribed finite blank initializations, including whole infinite tape; no assertion about a long nonhalting simulation.'}

def main():
 require(__debug__ and not sys.flags.optimize,'Run without -O/-OO or PYTHONOPTIMIZE')
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--original',type=Path,default=ROOT/'inputs/k230.tm');p.add_argument('--h-table',type=Path,default=ROOT/'inputs/k229_h_oldlabels.tm');p.add_argument('--sites',type=Path,default=ROOT/'inputs/sites_h.json');p.add_argument('--machine',type=Path,default=ROOT/'machines/k228.tm');p.add_argument('--engine-dir',type=Path,default=ROOT/'kernels');p.add_argument('--output-dir',type=Path,default=ROOT/'reproduced');p.add_argument('--quick',action='store_true');a=p.parse_args()
 a.output_dir.mkdir(parents=True,exist_ok=True)
 old,canonical,normalized,sites,construction=build.build(a.original,a.h_table,a.sites,a.output_dir/'machines')
 delivered_raw=a.machine.read_bytes();require(build.sha(delivered_raw)==build.PINS['canonical'],'Wrong canonical delivery bytes')
 parsed,st=build.parse(delivered_raw);build.validate(parsed,st,228,228);require(st==0 and parsed==canonical,'Canonical delivery fails exact reconstruction')
 require(set(q for q,b in parsed)==set(range(228)),'Working states must be exactly0..227')
 sf=source_check(sites);boot=startup(old,parsed,construction);write(a.output_dir/'dense_startup.json',boot)
 receipt={'status':'STATIC_CONSTRUCTION_AND_DENSE_STARTUP_PASS','machine_sha256':sha(a.machine),'source_sha256':sha(a.sites),'original_sha256':sha(a.original),'states':228,'rows':456,'source':sf,'dense_startup_file':'dense_startup.json','dense_startup_sha256':sha(a.output_dir/'dense_startup.json'),'driver_sha256':sha(__file__),'table_reconstruction_sha256':sha(build.__file__),'proof_assistant_endpoint':False,'cross_machine_right_one_guard_assumed':False,'scope':'Construction, relabeling and exact blank startup. Universal runtime requires the full mode.'}
 if a.quick:
  write(a.output_dir/'verification.json',receipt);print(json.dumps(receipt,indent=2));return
 ep=a.engine_dir/'runtime_engine.py';hp=a.engine_dir/'runtime_support.py';require(sha(ep)==ENGINE_SHA and sha(hp)==HELPER_SHA,'Wrong retained proof-engine bytes')
 sys.path.insert(0,str(a.engine_dir.resolve()));engine=importlib.import_module('runtime_engine')
 require(Path(engine.__file__).resolve()==ep.resolve() and Path(engine.r.__file__).resolve()==hp.resolve(),'Unexpected imported module path')
 lemmas,blocks=engine.prove_blocks(normalized);receipt.update(status='RUNTIME_IN_PROGRESS',engine_sha256=sha(ep),helper_sha256=sha(hp),list_induction_blocks=blocks)
 started=time.monotonic();cases=[];used=set()
 def save():
  receipt.update(cases=len(cases),seconds=time.monotonic()-started);write(a.output_dir/'verification.json',receipt)
 try:
  for index,site in enumerate(sites):
   for positive in((False,True) if site[1]=='CD' else(False,)):
    answer=engine.case(normalized,lemmas,site,positive);used.update(answer.pop('rows'));answer.pop('trace');cases.append({'index':index,'positive':positive,**answer})
    if len(cases)%1000==0:print('proved',len(cases),'of6656cases',round(time.monotonic()-started,2),'seconds',flush=True);save()
  require(len(cases)==6656 and used==set(normalized),'Incomplete runtime or literal-row coverage')
  casefile=a.output_dir/'runtime_cases.json';write(casefile,cases);require(sha(casefile)==CASE_SHA,'Replayed case certificate differs from previously validated complete output')
  receipt.update(status='K228_UNIVERSAL_MATHEMATICAL_PASS',symbolic_steps=sum(c['symbolic_steps'] for c in cases),maximum_symbolic_steps=max(c['symbolic_steps'] for c in cases),minimum_actual_steps=min(c['duration'][0] for c in cases),all_literal_rows_used=True,used_rows=sorted(used),cases_file=casefile.name,cases_sha256=sha(casefile),scope='All independent natural primary registers at each zero/positive guard, every nonnegative extra gap, arbitrary first spare and arbitrary finite spare tail; entire tape, exact source successor, positive duration. Source H-loop equivalence and released K230 calibration are separate supplied mathematical premises.',proof_construction_limit_per_case=4000,limits_scope='The4000limit bounds only symbolic proof construction. Values, actual runtime, gap and finite spare-list length are unbounded.',local_delayed_guard_status='No global old-state140/right-one theorem is claimed or assumed. The direct candidate runtime theorem proves the complete source-program contract.')
  require(receipt['symbolic_steps']==1614426 and receipt['maximum_symbolic_steps']==415 and receipt['minimum_actual_steps']==13,'Unexpected complete proof metrics')
  save();print(json.dumps({k:v for k,v in receipt.items() if k not in('list_induction_blocks','used_rows')},indent=2),flush=True)
 except Exception as exc:
  receipt.update(status='NOT_PROVED',site_index=locals().get('index'),site=locals().get('site'),positive=locals().get('positive'),error=repr(exc));save();raise
if __name__=='__main__':main()
