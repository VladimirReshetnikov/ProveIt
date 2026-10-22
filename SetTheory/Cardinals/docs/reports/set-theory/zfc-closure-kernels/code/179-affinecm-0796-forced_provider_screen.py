#!/usr/bin/env python3
"""A fixed 639-table shared-provider family; bounded first-redispatch screen.

No proof-assistant result or blank-start consistency calibration is asserted.
The 214 listed dense working labels omit 189, without renumbering.
"""
import sys
sys.dont_write_bytecode = True
from pathlib import Path
ROOT = Path(__file__).resolve().parent
REF = ROOT.parent if (ROOT.parent/'k215.tm').exists() else ROOT.parent/'deliverable'
sys.path.insert(0, str(REF))
from search_existential_spares import parse, run, decode
from audit_spare_counterexamples import replay, source_output
import hashlib, json, time

LIMIT = 20000

def blank_run(rows, limit=100000):
    ones=set(); q=0; h=0
    for tick in range(limit+1):
        if q==215:return {'kind':'halt','steps':tick}
        if tick and q==83:
            d=decode(h,ones)
            if d is not None:
                return {'kind':'first_clean_dispatch','steps':tick,'head':h,
                        'pc_one_positions':sorted(d[0]),'registers':d[1],
                        'spares':d[2],'gap':d[3]}
        if tick==limit:return {'kind':'bound','steps':tick}
        b=int(h in ones); w,di,z=rows[q,b]
        if w:ones.add(h)
        else:ones.discard(h)
        q=z;h+=di

def main():
    beg=time.time(); parent=parse(REF/'k215.tm')
    sites=json.loads((REF/'reference/k215/sites215.json').read_text())
    assert parent[66,0]==(1,1,189)
    assert parent[189,0]==(1,-1,40) and parent[189,1]==(1,-1,111)
    assert [k for k,v in parent.items() if k[0]!=189 and v[2]==189]==[(66,0)]
    shortest={}
    for i,site in enumerate(sites):
        key=tuple(site[1:])
        if key not in shortest or len(site[0])<len(shortest[key][1][0]):
            shortest[key]=(i,site)
    tests=[]
    for i,site in shortest.values():
        for regs,spares,gap in [([0]*9,[0],0),([1]*9,[0,2,1],3),([i%3 for i in range(9)],[2],0)]:
            ok,steps,_,out=run(parent,site,regs,spares,gap,LIMIT)
            assert ok,('parent control',i,site,regs,out)
            tests.append(dict(site_index=i,site=site,registers=regs,spares=spares,gap=gap,
                              parent_steps=steps,parent_output=out))
    assert len(tests)==69
    parent_blank=blank_run(parent)
    assert parent_blank['kind']=='first_clean_dispatch'
    results=[]; sample_runs=0; survivors=[]; independent=0
    for p in range(215):
        if p in (66,189):continue
        for mode in ('zero','one','both'):
            rows={k:v for k,v in parent.items() if k[0]!=189}
            rows[66,0]=(1,1,p)
            for b in ((0,) if mode=='zero' else (1,) if mode=='one' else (0,1)):
                rows[p,b]=parent[189,b]
            assert len(rows)==428 and all(z!=189 for w,d,z in rows.values())
            result=dict(provider=p,mode=mode,redirect=[66,0,1,1,p],
                        copied_rows=[[p,b,*parent[189,b]] for b in ((0,) if mode=='zero' else (1,) if mode=='one' else (0,1))])
            result['blank_start']=blank_run(rows)
            bad=None
            for ti,t in enumerate(tests):
                sample_runs+=1
                ok,steps,_,out=run(rows,t['site'],t['registers'],t['spares'],t['gap'],LIMIT)
                if not ok:
                    kind=('bound' if 'bound' in out else 'outward_blank_ray' if 'outward_blank_ray' in out
                          else 'unexpected_halt' if 'halt' in out else 'wrong_first_dispatch')
                    bad=dict(t,steps=steps,actual=out,kind=kind,sample_index=ti)
                    if kind=='wrong_first_dispatch':
                        assert replay(parent,bad,bad['parent_steps'])==bad['parent_output']
                        assert replay(rows,bad,steps)==out
                        expected=source_output(t['site'],t['registers'])
                        assert expected is not None
                        assert out['pc_one_positions']!=expected[0] or out['registers']!=expected[1]
                        independent+=1
                    break
            result['passed_samples']=ti if bad else len(tests)
            result['witness']=bad
            if not bad:survivors.append(result)
            results.append(result)
        if p%25==0:print('provider',p,'tables',len(results),'survivors',len(survivors),'seconds',round(time.time()-beg,2),flush=True)
    counts={}
    for r in results:
        key=r['witness']['kind'] if r['witness'] else 'survivor'
        counts[key]=counts.get(key,0)+1
    blank_counts={}
    for r in results:
        b=r['blank_start'];k=b['kind']
        if k=='first_clean_dispatch':
            k+=':logical_match' if all(b[f]==parent_blank[f]for f in ('registers','pc_one_positions')) else ':logical_mismatch'
        blank_counts[k]=blank_counts.get(k,0)+1
    output=dict(status='FIXED_FAMILY_BOUNDED_FIRST_REDISPATCH_SCREEN',family='p in 0..214 except66,189; redirect66/0 to1 R p; copy either or both old189 branches into p; delete189',
                providers=213,tables=len(results),samples=69,sample_runs=sample_runs,transition_bound=LIMIT,
                classifications=counts,wrong_outputs_independently_replayed=independent,
                parent_blank=parent_blank,blank_transition_bound=100000,blank_classifications=blank_counts,
                survivors=survivors,results=results,seconds=time.time()-beg,
                scope='Wrong first-clean-redispatch outputs refute only that reusable primitive contract. Bounds remain unresolved. Blank-prefix observations do not decide consistency calibration. No correct214-state machine is asserted.',
                hashes={str(p.relative_to(REF)):hashlib.sha256(p.read_bytes()).hexdigest()for p in [REF/'k215.tm',REF/'reference/k215/sites215.json']})
    (ROOT/'forced_provider_results.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps({k:output[k]for k in ['tables','sample_runs','classifications','wrong_outputs_independently_replayed','blank_classifications','seconds']},indent=2),flush=True)

if __name__=='__main__':main()
