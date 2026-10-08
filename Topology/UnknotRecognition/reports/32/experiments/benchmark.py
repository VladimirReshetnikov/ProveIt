"""Paired same-pivot local/rebuild ablation, with local/local controls.

Wall times include attachment, quantum checks, rebasing, final graded closure;
imports are excluded. No preprocessing filters are present. No production
fastunknot comparison is made. All completed samples are retained.
"""
import json,random,sys,time,platform,statistics,argparse
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]; sys.path.insert(0,str(ROOT/'src'))
from graded_scan import scan,Limits

def run(rounds=5):
 cases=[('torus4_4',4,[1,2,3]*4),('torus4_8',4,[1,2,3]*8),
        ('torus4_12',4,[1,2,3]*12),
        ('mixed_blocks',4,[1,2,3]*4+[-2]+[-3,-2,-1]*3+[2,1]),
        ('weaving4_4',4,[1,-2,3]*4)]
 rng=random.Random(1082026); rows=[]
 for name,s,w in cases:
  scan(s,w,limits=Limits(seconds=60))
  trials=[]
  for k in range(rounds):
   calls=[('local','local'),('rebuild','rebuild'),('control_a','local'),('control_b','local')]
   rng.shuffle(calls); trial={'round':k,'order':[a for a,b in calls]}; hom=None
   for label,mode in calls:
    r=scan(s,w,reducer=mode,limits=Limits(seconds=120))
    if hom is not None: assert hom==r['bigraded_homology']
    hom=r['bigraded_homology']
    trial[label]={'seconds':r['seconds'],'reduce_seconds':sum(t['reduce_seconds'] for t in r['trace']),
                  'update_pairs':sum(t['update_pairs'] for t in r['trace']),
                  'rebuild_scanned':sum(t['rebuild_scanned'] for t in r['trace'])}
   assert trial['local']['update_pairs']==trial['rebuild']['update_pairs']
   trials.append(trial)
  local=statistics.median(t['local']['seconds'] for t in trials)
  rebuild=statistics.median(t['rebuild']['seconds'] for t in trials)
  row=dict(name=name,strands=s,word=w,crossings=len(w),trials=trials,
           local_median=local,rebuild_median=rebuild,median_time_ratio=rebuild/local,
           paired_median_ratio=statistics.median(t['rebuild']['seconds']/t['local']['seconds'] for t in trials),
           aa_median_ratio=statistics.median(t['control_a']['seconds']/t['control_b']['seconds'] for t in trials),
           peak_objects=max(t['objects'] for t in r['trace']),
           peak_allocation=max(t['pre_objects'] for t in r['trace']),
           peak_occupancy=max(t['occupancy'] for t in r['trace']),
           homology=hom)
  rows.append(row); print(name,round(local,4),round(rebuild,4),round(rebuild/local,3),flush=True)
  out=dict(seed=1082026,rounds=rounds,python=sys.version,platform=platform.platform(),results=rows)
  (ROOT/'results'/'benchmark.json').write_text(json.dumps(out,indent=2)+'\n')
if __name__=='__main__':
 p=argparse.ArgumentParser(); p.add_argument('--rounds',type=int,default=5); a=p.parse_args(); run(a.rounds)
