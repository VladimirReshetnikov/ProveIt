"""Paired reference-backend timings, NOT the production fastunknot pipeline."""
from __future__ import annotations
import argparse, csv, json, platform, statistics, sys
from pathlib import Path
from time import monotonic, perf_counter
from unknot_windows import Diagram, low_window, probe, ScanLimit
from unknot_windows.orders import nice_order, certify, OrderError

CASES=[('weaving_3_4',3,[-1,2]*4),('weaving_3_5',3,[-1,2]*5),
       ('weaving_3_7',3,[-1,2]*7),('torus_3_7',3,[1,2]*7),
       ('positive_v_squared',3,[1,2,1,1,2,2]*2),
       ('padded_unknot',3,[1,2]+[1,-1]*5)]

def main():
 p=argparse.ArgumentParser(); p.add_argument('--repeats',type=int,default=3)
 p.add_argument('--seconds',type=float,default=20); p.add_argument('--max-objects',type=int,default=12000)
 p.add_argument('--output',type=Path,default=Path('results')); args=p.parse_args()
 if args.repeats<1: p.error('repeats must be positive')
 args.output.mkdir(exist_ok=True,parents=True)
 raw=[]; inputs=[]; summary=[]
 for name,b,word in CASES:
  d=Diagram.from_braid(b,word)
  try: cert=nice_order(d.pd)
  except OrderError: cert=certify(d.pd,range(len(word)))
  inputs.append({'name':name,'braid':{'strands':b,'word':word},'pd':d.pd,'order':cert.order,'nice':cert.nice,'girth':cert.girth})
  rows=[]
  for rep in range(args.repeats):
   modes=['full','window2','probe2'] if rep%2==0 else ['probe2','window2','full']
   for mode in modes:
    start=perf_counter(); state='OK'; ranks=None; verdict='NOT_APPLICABLE'; stats={}
    try:
     if mode=='probe2':
      r=probe(d,2,order=cert.order,max_objects=args.max_objects,seconds=args.seconds)
      verdict=r.verdict
      if r.reason.startswith('resource ceiling'): state='LIMIT'
      stats={'peak':max((x['stats'].get('max_objects_before_elimination',0) for x in r.runs),default=0),
             'compositions':sum(x['stats']['algebra']['compose_calls'] for x in r.runs)}
     else:
      r=low_window(d,len(word) if mode=='full' else 2,order=cert.order,
                   max_objects=args.max_objects,deadline=monotonic()+args.seconds)
      ranks=r.ranks
      stats={'peak':r.stats['max_objects_before_elimination'],'compositions':r.stats['algebra']['compose_calls']}
    except ScanLimit as exc: state='LIMIT'; verdict=str(exc)
    row={'name':name,'n':len(word),'girth':cert.girth,'nice':cert.nice,'repeat':rep,
         'mode':mode,'seconds':perf_counter()-start,'state':state,'verdict':verdict,
         'rank_sum':sum(ranks.values()) if ranks is not None else None,**stats}
    rows.append(row); raw.append(row)
  entry={'name':name,'n':len(word),'girth':cert.girth,'nice':cert.nice}
  for mode in ['full','window2','probe2']:
   rr=[x for x in rows if x['mode']==mode]
   entry[mode]={'all_completed':all(x['state']=='OK' for x in rr),
                'median_seconds':statistics.median(x['seconds'] for x in rr),
                'peak':max(x.get('peak',0) for x in rr),'verdict':rr[0]['verdict'],
                'compositions':rr[0].get('compositions'), 'rank_sum':rr[0]['rank_sum']}
  if entry['full']['all_completed'] and entry['window2']['all_completed']:
   entry['paired_speedup_median']=statistics.median(
      next(x['seconds'] for x in rows if x['repeat']==i and x['mode']=='full')/
      next(x['seconds'] for x in rows if x['repeat']==i and x['mode']=='window2') for i in range(args.repeats))
  summary.append(entry); print(json.dumps(entry),flush=True)
 metadata={'python':sys.version,'platform':platform.platform(),'backend':'supplied readable dictionary scanner',
           'repeats':args.repeats,'max_objects':args.max_objects,'seconds_per_run':args.seconds,
           'timing_protocol':'sequential alternating AB/BA-style triples; no warmup discarded; imports excluded',
           'comparison_scope':'same input, same crossing order, same min-fill policy; full homology versus requested low-degree window; no pipeline claim'}
 (args.output/'benchmark.json').write_text(json.dumps({'metadata':metadata,'inputs':inputs,'summary':summary,'raw':raw},indent=2)+'\n')
 keys=sorted(set().union(*(row.keys() for row in raw)))
 with (args.output/'benchmark_raw.csv').open('w',newline='') as f:
  w=csv.DictWriter(f,fieldnames=keys); w.writeheader(); w.writerows(raw)
 with (args.output/'benchmark_table.tex').open('w') as f:
  f.write('\\begin{tabular}{lrrrrrr}\\toprule\nInput & $n$ & $W$ & Full (s) & Window (s) & Ratio & Peak ratio\\\\\\midrule\n')
  for e in summary:
   a,z=e['full'],e['window2']
   f.write(e['name'].replace('_',r'\_')+f" & {e['n']} & {e['girth']} & {a['median_seconds']:.4f} & {z['median_seconds']:.4f} & {e.get('paired_speedup_median',0):.1f} & {a['peak']/max(1,z['peak']):.1f}\\\\\n")
  f.write('\\bottomrule\\end{tabular}\n')
if __name__=='__main__': main()
