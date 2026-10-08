"""Compare both local scanners against the independent reduced crossing cube."""
from pathlib import Path
import sys, random, json, time
ROOT=Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'code'),str(ROOT/'vendor')]
from braid_scan import scan_braid
from reference_cube import cube_homology

def main():
    rng=random.Random(202610072)
    cases=[(1,[]),(2,[1]),(2,[-1]),(2,[1]*3),(3,[1,-2]*2),(3,[1,2,-1,-2])]
    for b in (2,3,4):
        for _ in range(100):
            n=rng.randrange(0,10)
            cases.append((b,[rng.choice((-1,1))*rng.randrange(1,b) for _ in range(n)]))
    rows=[]; cert_stages=0; start=time.perf_counter()
    for number,(b,word) in enumerate(cases):
        a=scan_braid(b,word,backend='transfer',certificate=True)
        p=scan_braid(b,word,backend='pivot')
        r=cube_homology(b,word,max_crossings=10)
        expected={h:2*n for h,n in r['by_degree'].items()}
        assert a['unreduced_by_degree']==p['unreduced_by_degree']==expected,(b,word,a,p,r)
        assert [x['survivors'] for x in a['trace']]==[x['survivors'] for x in p['trace']]
        cert_stages+=len(word)
        rows.append({'strands':b,'word':word,'unreduced_rank':a['unreduced_rank'],
                     'by_degree':a['unreduced_by_degree'],
                     'max_pre_objects':max((x['pre_objects'] for x in a['trace']),default=1),
                     'max_survivors':max((x['survivors'] for x in a['trace']),default=1)})
    result={'status':'passed','cases':len(rows),'full_stage_certificates':cert_stages,
            'seed':202610072,'max_crossings':9,'seconds':time.perf_counter()-start,'data':rows}
    (ROOT/'results'/'braid_validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='data'},indent=2))
if __name__=='__main__': main()
