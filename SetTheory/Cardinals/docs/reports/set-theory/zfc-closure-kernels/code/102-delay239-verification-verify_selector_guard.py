#!/usr/bin/env python3
"""Check the new selector guard over exact boot and all unbounded RM cases.

The inherited symbolic engine supplies literal/unary/list induction rules.
This wrapper adds no rewrite rule; it checks a right-hand run length before
each old-table169/read1 transition and records its uniform positive margin.
"""
from pathlib import Path
import argparse, hashlib, importlib.util, json, sys, time

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--checker',type=Path,required=True);ap.add_argument('--table',type=Path,required=True);ap.add_argument('--sites',type=Path,required=True);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--boot-steps',type=int,default=409691)
    a=ap.parse_args();assert __debug__ and not sys.flags.optimize
    sys.path.insert(0,str(a.checker.resolve().parent))
    spec=importlib.util.spec_from_file_location('selector_guard_engine',a.checker);engine=importlib.util.module_from_spec(spec);spec.loader.exec_module(engine)
    tab=engine.r.table(a.table);sites=json.loads(a.sites.read_text());facts=engine.validate_inputs(tab,sites)
    assert len(tab)==480
    boot=[];q=95;h=0;ones=set()
    for tick in range(a.boot_steps):
        b=int(h in ones)
        if q==169 and b:
            assert h+1 in ones,('boot guard violation',tick,h)
            boot.append({'time':tick,'head':h,'window':''.join(str(int(h+j in ones))for j in range(-4,7))})
        w,d,q=tab[q,b]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
    assert q==96 and h==-5
    guard_events=[];context=None;ordinary_step=engine.State.step
    def guarded_step(self,table,lemmas,clock,motion):
        self.key()
        src=self.right if self.direction==1 else self.left
        if self.q==169 and src and src[0][0]=='run' and src[0][1]==1:
            assert self.direction==1,('unexpected169 direction',self.key())
            length=src[0][2]
            assert engine.nonnegative(length) and length[0]>=2,('selector guard lacks length2 margin',context,self.key())
            guard_events.append({'context':context,'right_one_run_length':length,'uniform_minimum':length[0]})
        return ordinary_step(self,table,lemmas,clock,motion)
    engine.State.step=guarded_step
    started=time.monotonic();lemmas,blocks=engine.prove_blocks(tab);cases=0;symbolic_steps=0
    for i,site in enumerate(sites):
        for positive in ((False,True)if site[1]=='CD'else(False,)):
            context={'site_index':i,'site':site,'positive':positive}
            answer=engine.case(tab,lemmas,site,positive)
            cases+=1;symbolic_steps+=answer['symbolic_steps']
            if cases%1000==0:print('guarded',cases,'cases','events',len(guard_events),flush=True)
    assert cases==8386 and guard_events
    receipt={'status':'UNBOUNDED_SELECTOR_GUARD_PASS','guard':'q=169 and tape[h]=1 implies tape[h+1]=1','baseline_sha256':hashlib.sha256(a.table.read_bytes()).hexdigest(),'sites_sha256':hashlib.sha256(a.sites.read_bytes()).hexdigest(),'inherited_checker_sha256':hashlib.sha256(a.checker.read_bytes()).hexdigest(),'wrapper_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'input_validation':facts,'boot_steps':a.boot_steps,'boot_endpoint':{'state':q,'head':h,'one_cells':len(ones)},'boot_guard_events':boot,'complete_cases':cases,'symbolic_steps':symbolic_steps,'runtime_guard_events':guard_events,'minimum_right_one_run':min(x['uniform_minimum']for x in guard_events),'seconds':time.monotonic()-started,'proof_scope':'Every literal169/read1 transition in the exact blank initialization and complete all-values/all-gap/arbitrary-spare-list instruction proof has a certified following1. Four list schemas are rechecked; no unary/list skip hides a169 control visit. The arbitrary-value cases and exact dispatch joins cover the complete subsequent run. This is an executable ordinary mathematical proof, not a Lean/Coq kernel proof.'}
    a.output.write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items()if k not in('runtime_guard_events','boot_guard_events','input_validation')},indent=2))

if __name__=='__main__':main()
