#!/usr/bin/env python3
"""Rebuild adaptive-search positive controls and the pair cross-check.
Requires Python3 and a C++17 compiler; writes evidence to a new directory.
Intentionally damaged tables are checker controls, not research candidates.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,tempfile
HERE=Path(__file__).resolve().parent
PKG=HERE.parents[1]
DATA=PKG/'research/bootstrap'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(path):
 rows={}
 for line in path.read_text().splitlines():
  if not line.strip() or line.lstrip().startswith('#'):continue
  q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),d,int(n))
 return rows

def scalar(rows,n):
 q,h,ones=74,0,set()
 for _ in range(n):
  w,d,q=rows[q,int(h in ones)]
  if w:ones.add(h)
  else:ones.discard(h)
  h+=1 if d=='R' else -1
 return q,h,sorted(ones)

def main():
 if not __debug__: raise SystemExit('Verification requires assertions; run without -O.')
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--output',type=Path);ap.add_argument('--compiler',default='g++');ap.add_argument('--skip-pairs',action='store_true')
 a=ap.parse_args();out=a.output.resolve() if a.output else Path(tempfile.mkdtemp(prefix='pa194-startup-review-'))
 out.mkdir(parents=True,exist_ok=True);assert out!=HERE,'Use a fresh output directory.'
 prov=json.loads((HERE/'PROVENANCE.json').read_text())
 assert digest(DATA/'adaptive_startup.cpp')==prov['reviewed_program_sha256']
 assert digest(HERE/'primary.native.tm')==prov['primary_native_table_sha256']
 assert digest(HERE/'pair_startup.cpp')==prov['pair_checker_sha256']
 exe=out/'adaptive_startup';subprocess.run([a.compiler,'-O3','-std=c++17',str(DATA/'adaptive_startup.cpp'),'-o',str(exe)],check=True)
 base=load(HERE/'primary.native.tm')
 def run(name,rows,choices,k):
  table=out/(name+'.tm');table.write_text(''.join(f'{q} {b} {w} {d} {n}\n' for (q,b),(w,d,n) in sorted(rows.items())))
  ep=out/(name+'.tsv');ep.write_text(''.join(f'{i} {q} {b} {w} {1 if d=="R" else -1} {n}\n' for i,q,b,w,d,n in choices))
  cp=subprocess.run([str(exe),str(table),str(ep),str(DATA/'startup_any_frame_templates.tsv'),str(k),'200000'],text=True,capture_output=True,check=True)
  (out/(name+f'_k{k}.hits.jsonl')).write_text(cp.stdout);(out/(name+f'_k{k}.log')).write_text(cp.stderr)
  return [json.loads(line) for line in cp.stdout.splitlines()],cp.stderr.strip().splitlines()[-1]
 baseline,bline=run('primary',base,[],0)
 assert len(baseline)==1 and baseline[0]['steps']==58154 and baseline[0]['pc']==25
 expected=baseline[0];q,h,ones=scalar(base,58154);assert(q,h,ones)==(84,expected['head'],expected['ones'])
 rs=dict(base);rs[74,0]=(0,'R',254);rs[0,0]=(0,'R',254)
 choices=[(10,74,0,0,'L',254),(11,74,0,*base[74,0]),(20,0,0,0,'L',254),(21,0,0,*base[0,0])]
 no,l1=run('two_repairs',rs,choices,1);yes,l2=run('two_repairs',rs,choices,2)
 assert not no and len(yes)==1 and yes[0]['edits']==[11,21] and yes[0]['steps']==58154
 rs=dict(base);rs[0,0]=(0,'R',0)
 no,l0=run('future_ray',rs,[(30,0,0,*base[0,0])],0);rayyes,l3=run('future_ray',rs,[(30,0,0,*base[0,0])],1)
 assert not no and len(rayyes)==1 and rayyes[0]['edits']==[30] and rayyes[0]['steps']==58154
 for r in (yes[0],rayyes[0]):assert r['ones']==expected['ones'] and r['head']==expected['head'] and r['values']==expected['values']
 cp=subprocess.run([str(exe),str(DATA/'runtime193.native.tm'),str(DATA/'edits.tsv'),str(DATA/'startup_any_frame_templates.tsv'),'2','200000'],text=True,capture_output=True,check=True)
 assert not cp.stdout;(out/'runtime193_adaptive2.log').write_text(cp.stderr)
 result={'status':'PASS','baseline_scalar_whole_tape':True,'primary':bline,'two_nested_repairs':l2,'one_repair_insufficient':l1,'future_edit_prevents_ray_cut':l3,'unrepaired_ray':l0,'runtime193_adaptive2':cp.stderr.strip().splitlines()[-1],'source_hash':prov['reviewed_program_sha256']}
 if not a.skip_pairs:
  pair=out/'pair_startup';subprocess.run([a.compiler,'-O3','-std=c++17',str(HERE/'pair_startup.cpp'),'-o',str(pair)],check=True)
  cp=subprocess.run([str(pair),str(DATA/'runtime193.native.tm'),str(DATA/'edits.tsv'),str(DATA/'startup_any_frame_templates.tsv'),'200000','74'],text=True,capture_output=True,check=True)
  assert not cp.stdout;(out/'brute_pair.log').write_text(cp.stderr);result['brute_pairs_start74']=cp.stderr.strip().splitlines()[-1]
 (out/'review_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2));print('Fresh evidence:',out)
if __name__=='__main__':main()
