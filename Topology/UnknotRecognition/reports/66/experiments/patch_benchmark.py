"""Paired complete optimizers on explicit triangulated patch systems.

The mesh collection is generated before timing. Validation IS timed on each
solver route. Independent global mesh replay is timed and reported separately.
No patch is asserted embedded in a knot exterior.
"""
import argparse,json,platform,statistics,time
from pathlib import Path
from signed_continuations.patchwork import *


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',default='results/patch_benchmark.json');args=ap.parse_args()
    data={'scope':'Complete finite surface-patch disk selection, not unknot recognition',
          'python':platform.python_version(),'platform':platform.platform(),'repeats':3,'cases':[]}
    for rows,cols in ((2,4),(3,3),(3,5),(3,8)):
        system=grid_system(rows,cols);records=[]
        for repeat in range(3):
            result={}
            for small in ((False,True) if repeat%2==0 else (True,False)):
                start=time.perf_counter();answer=solve(system,reduced=small);elapsed=time.perf_counter()-start
                result['basis' if small else 'full']=(answer,elapsed)
            a,at=result['full'];b,bt=result['basis']
            assert a.minimum_cost==b.minimum_cost
            start=time.perf_counter();assert verify_witness(system,b);replay=time.perf_counter()-start
            records.append({'full_s':at,'basis_s':bt,'mesh_replay_s':replay,'minimum_cost':b.minimum_cost,
                            'disk_exists':b.disk_exists,'full_generated':sum(h['attempted'] for h in a.history),
                            'basis_generated':sum(h['attempted'] for h in b.history),
                            'full_peak_states':max(h['retained'] for h in a.history),
                            'basis_peak_states':max(h['retained'] for h in b.history),
                            'frontier_width':max(h['frontier'] for h in b.history),'temporary_width':b.temporary_width,
                            'basis_choices':b.choices,'basis_history':b.history})
        data['cases'].append({'rows':rows,'columns':cols,'sites':rows*cols,
                              'options':sum(len(x) for x in system.options),
                              'input_triangles':sum(len(s.triangles) for opts in system.options for s in opts),
                              'raw':records,'median_full_s':statistics.median(x['full_s'] for x in records),
                              'median_basis_s':statistics.median(x['basis_s'] for x in records),
                              'median_replay_s':statistics.median(x['mesh_replay_s'] for x in records)})
        print(rows,cols,records[0]['full_generated'],records[0]['basis_generated'],flush=True)
    p=Path(args.out);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(data,indent=2)+'\n')

if __name__=='__main__':main()
