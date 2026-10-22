#!/usr/bin/env python3
"""Refine all 109 short-screen survivors against the literal source sites."""
import sys
sys.dont_write_bytecode=True
from forced_provider_screen import ROOT,REF,parse,run,replay,source_output
import hashlib,json,time

def main():
    beg=time.time();parent=parse(REF/'k215.tm')
    sites=json.loads((REF/'reference/k215/sites215.json').read_text())
    first=json.loads((ROOT/'forced_provider_results.json').read_text())
    results=[];survivors=[];runs=0;count={};parent_cache={}
    for ordinal,c in enumerate(first['survivors']):
        p=c['provider'];mode=c['mode']
        rows={k:v for k,v in parent.items()if k[0]!=189};rows[66,0]=(1,1,p)
        for b in ((0,)if mode=='zero'else(1,)if mode=='one'else(0,1)):rows[p,b]=parent[189,b]
        bad=None;passed=0
        for i,site in enumerate(sites):
            for pos in ([False,True]if site[1]=='CD'else[False]):
                regs=[0]*9
                if pos:regs[site[2]]=1
                runs+=1;ok,steps,_,out=run(rows,site,regs,[0],0,20000)
                if not ok:
                    kind=('bound'if'bound'in out else'outward_blank_ray'if'outward_blank_ray'in out else'unexpected_halt'if'halt'in out else'wrong_first_dispatch')
                    key=(i,pos)
                    if key not in parent_cache:
                        po,ps,_,pf=run(parent,site,regs,[0],0,20000);assert po
                        parent_cache[key]=(ps,pf)
                    ps,pf=parent_cache[key]
                    bad=dict(site_index=i,site=site,registers=regs,spares=[0],gap=0,
                             parent_steps=ps,parent_output=pf,steps=steps,actual=out,kind=kind)
                    if kind=='wrong_first_dispatch':
                        assert replay(parent,bad,ps)==pf
                        assert replay(rows,bad,steps)==out
                        want=source_output(site,regs);assert want is not None
                        assert out['pc_one_positions']!=want[0]or out['registers']!=want[1]
                    break
                passed+=1
            if bad:break
        result=dict(provider=p,mode=mode,passed_full_source_cases=passed,witness=bad)
        if not bad:survivors.append(result)
        results.append(result);kind=bad['kind']if bad else'survivor';count[kind]=count.get(kind,0)+1
        print('candidate',ordinal+1,'of',len(first['survivors']),p,mode,kind,'passed',passed,'seconds',round(time.time()-beg,2),flush=True)
        output=dict(status='FIXED_PROVIDER_FULL_SOURCE_REFINEMENT',processed=len(results),expected=len(first['survivors']),
                    sample_runs=runs,classifications=count,survivors=survivors,results=results,seconds=time.time()-beg,
                    first_screen_sha256=hashlib.sha256((ROOT/'forced_provider_results.json').read_bytes()).hexdigest(),
                    scope='Zero-valued registers and both zero/positive tests of CD at all literal source sites. Bounded at20000 transitions per primitive. Wrong outputs are independently replayed first-clean-redispatch counterexamples; bounds are not negative theorems.')
        (ROOT/'forced_provider_refinement.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:output[k]for k in ['processed','sample_runs','classifications','seconds']},indent=2),flush=True)

if __name__=='__main__':main()
