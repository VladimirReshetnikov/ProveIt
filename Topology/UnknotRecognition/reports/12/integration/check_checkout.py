"""Run paired checks against a real ProveIt fast/ checkout, without modifying it.

python integration/check_checkout.py --fast-dir /path/to/UnknotRecognition/fast
This external-checkout command was not executed in the artifact-generation run.
"""
import argparse,hashlib,json,pathlib,sys,time
ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.path[:0]=[str(ROOT/'src'),str(ROOT)]
from unknot_frobenius.adapters import install_on_empty_scan
from reference.legacy.fastunknot.diagram import Diagram
from reference.legacy.fastunknot.scan import best_scan_order
EXPECTED={'planar.py':'1078526e7e7dbaf0b7267728105d870d94136769',
          'scan_fast.py':'2c1ad52d14296b109376af19668ae0eebb4c6fdd'}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--fast-dir',required=True,type=pathlib.Path)
    ap.add_argument('--allow-version-change',action='store_true')
    args=ap.parse_args();base=args.fast_dir.resolve()
    for name,expected in EXPECTED.items():
        p=base/'fastunknot'/name;data=p.read_bytes()
        observed=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
        if observed!=expected and not args.allow_version_change:
            ap.error(f'{name} differs from inspected source; audit before --allow-version-change')
    sys.path.insert(0,str(base))
    from fastunknot.scan_fast import FastScan
    results=[]
    for name in ['trefoil','figure_eight','hard_unknot_8','conway','kinoshita_terasaka','torus_3_5']:
        pd=Diagram.from_json(json.loads((ROOT/'examples'/f'{name}.json').read_text())).pd
        order=best_scan_order(list(pd),tries=min(len(pd),12));answers=[]
        for mode in ['baseline','adaptive','forced']:
            scan=FastScan(max_objects=100000,deadline=time.monotonic()+30)
            if mode!='baseline':install_on_empty_scan(scan,minimum_pairs=0 if mode=='forced' else 64,
                                                      method='fast' if mode=='forced' else 'auto')
            for i in order:
                scan.add_crossing(pd[i]);scan.check_d_squared()
            scan.total_rank();answers.append(scan.ranks_by_degree())
        if not answers[0]==answers[1]==answers[2]:raise AssertionError(f'rank mismatch: {name}')
        results.append(dict(case=name,by_degree=answers[0],all_modes_agree=True))
    print(json.dumps(results,indent=2))

if __name__=='__main__':main()
