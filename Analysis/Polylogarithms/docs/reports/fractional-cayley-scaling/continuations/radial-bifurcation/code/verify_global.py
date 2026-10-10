"""Standard-library-only exact proof of the global quartic sign transition.

Every saved root bracket and every interval in the complete b-cover is
checked. Floats appear only in progress/output diagnostics, not decisions.
Optional --start/--stop permit independent batch replay; a full run checks
coverage and writes the canonical verified receipt.
"""
from __future__ import annotations
import argparse,json,time
from pathlib import Path
from fractions import Fraction as F
from exact import I,SCALE,threshold_value
from taylor import threshold_jets,along_threshold
ROOT=Path(__file__).resolve().parents[1]

def main():
    if not __debug__:raise RuntimeError('Do not run verifiers with python -O')
    ap=argparse.ArgumentParser();ap.add_argument('--start',type=int,default=0);ap.add_argument('--stop',type=int);args=ap.parse_args()
    doc=json.loads((ROOT/'certificates/global_mesh.json').read_text());allcells=doc['cells'];roots=doc['roots']
    assert F(allcells[0]['lo'])==0 and F(allcells[-1]['hi'])==1
    for x,y in zip(allcells,allcells[1:]):assert F(x['hi'])==F(y['lo'])
    for c in allcells:
        lo,hi,mid=map(F,(c['lo'],c['hi'],c['mid']))
        assert lo<hi and mid==(lo+hi)/2
        assert (c['kind']=='increasing' and 0<=lo<hi<=F(9,10)) or (c['kind']=='concave' and F(9,10)<=lo<hi<=1)
    stop=len(allcells) if args.stop is None else args.stop
    assert 0<=args.start<stop<=len(allcells)
    cells=allcells[args.start:stop];needed=set()
    for c in cells:needed.update((c['lo'],c['hi'],c['mid']))
    t=time.time();verified={}
    for key in sorted(needed,key=F):
        r=roots[key];bl=I.point(F(key));al,ah=map(F,(r['lo'],r['hi']))
        assert al<ah
        kl=threshold_value(I.point(al),bl);kh=threshold_value(I.point(ah),bl)
        assert kl.lo>0 and kh.hi<0, ('root bracket fails',key,kl.dump(),kh.dump())
        verified[key]=I.bounds(al,ah)
    receipts=[]
    for index,c in enumerate(cells,args.start):
        lo,hi,mid=map(F,(c['lo'],c['hi'],c['mid']));h=I.point((hi-lo)/2)
        # Monotonic b-barriers enclose the entire implicitly defined graph.
        A=I(verified[c['hi']].lo,verified[c['lo']].hi);B=I.bounds(lo,hi)
        assert A.lo<=verified[c['mid']].lo<=verified[c['mid']].hi<=A.hi
        K,Q=threshold_jets(A,B)
        assert K.a.hi<0 and K.b.hi<0, ('barrier derivative fails',index)
        # K(lower-a, upper-b)>0 and K(upper-a, lower-b)<0 were
        # checked above. K_b<0 gives barriers for all intermediate b.
        # Expand the barriers by outward rounding; this preserves signs
        # because K_a<0. The dyadic box therefore contains the graph.
        whole=along_threshold(K,Q)
        K0,Q0=threshold_jets(verified[c['mid']],I.point(mid))
        center=along_threshold(K0,Q0)
        if c['kind']=='increasing':
            M=max(abs(whole[1].lo),abs(whole[1].hi));bound=center[0]-h*I(0,M)
            assert bound.lo>0, ('q prime fails',index,bound.dump())
            margin=bound.lo
        else:
            M=max(abs(whole[2].lo),abs(whole[2].hi));bound=center[1]+h*I(0,M)
            assert bound.hi<0, ('q double prime fails',index,bound.dump())
            margin=-bound.hi
        receipts.append({'cell':index,'kind':c['kind'],'strict_margin_dyadic_numerator':str(margin)})
        if index%128==0:print('verified cell',index,'elapsed',round(time.time()-t,1),flush=True)
    summary={'status':'PASS','bits':256,'start':args.start,'stop':stop,'cells_verified':len(cells),'root_boxes_verified':len(needed),
             'full_cover':args.start==0 and stop==len(allcells),
             'minimum_margin_by_kind':{kind:str(min(int(r['strict_margin_dyadic_numerator']) for r in receipts if r['kind']==kind)) for kind in ('increasing','concave') if any(r['kind']==kind for r in receipts)},
             'arithmetic':'integer outward dyadic intervals; no floating-point sign decisions', 'cells':receipts}
    if summary['full_cover']:
        assert F(int(summary['minimum_margin_by_kind']['increasing']),SCALE)>F(1,10**6)
        assert F(int(summary['minimum_margin_by_kind']['concave']),SCALE)>F(29,10**6)
        summary['certified_coarse_bounds']={'q_prime_on_0_to_0.9':'> 1e-6','q_double_prime_on_0.9_to_1':'< -2.9e-5'}
    name='global_verified.json' if summary['full_cover'] else f'global_verified_{args.start}_{stop}.json'
    (ROOT/'certificates'/name).write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k!='cells'},indent=2),flush=True)
if __name__=='__main__':main()
