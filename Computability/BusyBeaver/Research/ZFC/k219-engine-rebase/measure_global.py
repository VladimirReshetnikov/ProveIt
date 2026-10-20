#!/usr/bin/env python3
"""Measure global retired-decoder allocation on original-theory and R205 sources."""
from pathlib import Path
import argparse,hashlib,json,sys,time
HERE=Path(__file__).resolve().parent;BASE=HERE.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 assert __debug__ and not a.out.exists();sys.dont_write_bytecode=True;sys.path.insert(0,str(HERE/'code'));sys.path.insert(0,str(HERE))
 import source_language as s,build221 as b,global_allocator as g
 pins=json.loads((HERE/'inputs.json').read_text());assert all(sha(Path(p))==h for p,h in pins.items())
 a.out.mkdir(parents=True);records=[];controls=[]
 variants=[(f'hit{x:02}',BASE/f'k219-source-search/candidates/hit{x:02}.sites.json',True,'Original calculus; established equality macro source theorem, binary runtime pending')for x in(0,1,2,3,12)]
 for name in('RAB-left','RBC-left','RCA-right'):
  p=BASE/f'k219-pivot-fusion/results/membership-protected/{name}/sites.json'
  variants.append((name,p,False,'Modified fourth-parameter calculus; ZFC equiconsistency calibration remains open'))
 for name,p,hyp,scope in variants:pins[str(p.resolve())]=sha(p)
 for backend in(219,220):
  bp=BASE/f'candidate-k{backend}';table=b.read_table((bp/f'k{backend}.native.tm').read_bytes());old=s.tree(json.loads((bp/f'sites{backend}.json').read_text()))
  for pure in(True,False):
   ident,control=g.compile_tree(s,b,table,old,old,require_pure_rows=pure)
   assert ident==table and control['working_states']==backend;controls.append(dict(backend=backend,pure=pure,metrics=control))
   for name,p,hyp,scope in variants:
    rows=json.loads(p.read_text());tree=s.tree(rows);assert s.sites(tree)==rows and s.graph_arithmetic(rows)[0]==s.graph_intervals(rows)
    out=a.out/f'native{backend}-{name}-{"pure" if pure else "incoming-only"}'
    out.mkdir();start=time.monotonic();row=dict(backend=backend,variant=name,source_sha256=sha(p),source_path=str(p.resolve()),source_metrics=s.metrics(tree),hypothetical_right_ci_entries=hyp,calibration_scope=scope,require_pure_rows=pure)
    try:
     tt,m=g.compile_tree(s,b,table,old,tree,hypothetical_entries=hyp,require_pure_rows=pure);raw=b.table_bytes(tt);assert b.read_table(raw)==tt
     target=out/'candidate.native.tm';target.write_bytes(raw);row.update(status='SOURCE_DECODER_BINDING_PASS',metrics=m,table_sha256=sha(target))
    except (ValueError,KeyError,AssertionError)as e:row.update(status='REJECTED',reason=repr(e))
    row['seconds']=time.monotonic()-start;dump(out/'result.json',row);records.append(row)
    print(backend,name,pure,row['status'],row.get('metrics',{}).get('working_states'),row.get('metrics',{}).get('pool_used'),row.get('reason',''),flush=True)
 assert all(sha(Path(p))==h for p,h in pins.items())
 dump(a.out/'result.json',dict(status='GLOBAL_POOL_MEASUREMENTS_COMPLETE',inputs=pins,script_sha256=sha(Path(__file__)),allocator_sha256=sha(HERE/'global_allocator.py'),identity_controls=controls,results=records,scope='Allocation/prefix measurements, not machine acceptance. Incoming-only supplementary policy drops the own-row purity test while preserving every incoming-edge certificate.'))
if __name__=='__main__':main()
