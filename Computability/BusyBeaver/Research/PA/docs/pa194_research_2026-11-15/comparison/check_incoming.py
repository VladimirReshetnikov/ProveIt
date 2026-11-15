#!/usr/bin/env python3
"""Independent shape and finite whole-tape startup audit of 17 new deliveries.
This check establishes no unbounded run or arithmetic-calibration theorem.
"""
import argparse,csv,hashlib,io,json,pathlib,tempfile,zipfile
BASE=pathlib.Path(__file__).resolve().parent
STEPS={'PA194AX11GDH':57922,'PA194AX11GDHS':57768,'PA194AX11GDHF':57870,'PA194AX11GDHR':58022,
 'PA194GD':58154,'PA194GDH':57922,'PA194GDHS':57768,
 'PA194AX11H_SF':57918,'PA194LC_AX11H_SF':57918,
 'PA194LCAX11GHF':57870,'PA194LCAX11GHSF':57712,
 'PA194LCG':57870,'PA194LCGS':57712,'PA194LCGMS':57970,'PA194LCGSMS':57812,
 'PA194H5X':57922,'PA194JH5X':57922}
MECHANISMS={
 'pa194_gd_research_2026-11-14':'Independent generalization binder c and diagonal offset d+x; original distribution; no-push MP',
 'pa194_ax11gdh_research_2026-11-15':'GDH with eleven-entry, four-field AX interface; symmetric, fast and separated-helper variants',
 'pa194_comparison_and_new_designs_2026-11-15':'Compatible selector and two-shortcut composition, on AX11H and loop-continuation AX11H',
 'pa194_lcfast_tagged_research_2026-11-14':'Loop continuation plus two guarded physical shortcuts, on GH/GHS',
 'pa194_loop_return_2026-11-14':'Loop continuation plus three guarded physical shortcuts, on GH/GHS',
 'pa194_marker_separation_2026-11-14':'Separate marker history on LCG/LCGS using a dedicated helper',
 'pa194_witness_research_2026-11-15':'Independent witness-axiom consequent; optional J first-head replacement'}

def parse(raw):
 rows={}
 for l in raw.decode('ascii').splitlines():
  if not l.strip() or l.lstrip().startswith('#'):continue
  a,b,c,d,e=l.split();q,r,w,n=map(int,(a,b,c,e))
  assert (q,r) not in rows and r in (0,1) and w in (0,1) and d in ('L','R')
  rows[q,r]=(w,-1 if d=='L' else 1,n)
 assert len(rows)==388 and {q for q,b in rows}==set(range(194))
 assert all((q,b) in rows for q in range(194) for b in (0,1))
 assert {n for w,d,n in rows.values()}-set(range(194))=={194}
 reach={0};stack=[0]
 while stack:
  q=stack.pop()
  for b in (0,1):
   n=rows[q,b][2]
   if n<194 and n not in reach:reach.add(n);stack.append(n)
 assert len(reach)==194
 return rows

def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('source',type=pathlib.Path,help='Pinned ProveIt checkout containing docs/incoming')
 ap.add_argument('--output',type=pathlib.Path)
 args=ap.parse_args();out=args.output or pathlib.Path(tempfile.mkdtemp(prefix='pa194-startup-'))
 out.mkdir(parents=True,exist_ok=True)
 expected=json.loads((BASE/'incoming_principal_audit.json').read_text())
 assert len(expected)==17 and {r['name'] for r in expected}==set(STEPS)
 bound=json.loads((BASE/'source_blob_binding.json').read_text())
 archives={}
 for entry in bound['files']:
  if not entry['path'].endswith('.zip'):continue
  raw=(args.source/entry['path']).read_bytes()
  assert hashlib.sha256(raw).hexdigest()==entry['sha256'],entry['path']
  archives[pathlib.PurePosixPath(entry['path']).name]=zipfile.ZipFile(io.BytesIO(raw))
 ref='pa194_ax11gdh_research/machine/startup.json'
 seed=json.loads(archives['pa194_ax11gdh_research_2026-11-15.zip'].read(ref));target=set(seed['one_cells'])
 records=[]
 for previous in expected:
  archive=previous['archive'];name=previous['name'];loc=previous['path']
  raw=archives[archive].read(loc)
  assert hashlib.sha256(raw).hexdigest()==previous['sha256'],name
  rows=parse(raw);q=h=0;ones=set();used=set()
  for t in range(STEPS[name]):
   assert q!=194,(name,'early halt',t)
   b=int(h in ones);used.add((q,b));w,d,q=rows[q,b]
   if w:ones.add(h)
   else:ones.discard(h)
   h+=d
  label_path=str(pathlib.PurePosixPath(loc).with_name('labels.json'))
  labels=json.loads(archives[archive].read(label_path))
  if isinstance(labels,dict):
   if 'dense_to_native' in labels:labels=labels['dense_to_native']
   else:raise ValueError(('unknown labels schema',loc))
  native=labels[q] if isinstance(labels,list) else labels[str(q)]
  assert native==84 and h==-2,(name,native,h)
  assert ones==target,(name,sorted(ones^target))
  rec={'name':name,'archive':archive,'path':loc,
       'states':194,'start':0,'halt':194,'blank':0,'graph_reachable_states':194,
       'sha256':hashlib.sha256(raw).hexdigest(),
       'startup_steps':STEPS[name],'seed_native_state':native,'seed_head':h,
       'one_cells':sorted(ones),'whole_tape_startup_matches_reference':True,
       'startup_transition_rows_executed':len(used),'mechanism':MECHANISMS[archive.removesuffix('.zip')],
       'scope':'Finite complete-tape startup only; no arithmetic calibration or unbounded execution theorem.'}
  records.append(rec);print(name,STEPS[name],'PASS',flush=True)
 assert len(records)==17 and {r['name'] for r in records}==set(STEPS)
 (out/'incoming_principal_audit.json').write_text(json.dumps(records,indent=2)+'\n')
 cols=['name','archive','path','states','sha256','startup_steps','mechanism']
 with (out/'incoming_principal_audit.csv').open('w') as f:
  w=csv.DictWriter(f,cols);w.writeheader()
  for r in records:w.writerow({k:r[k] for k in cols})
 for z in archives.values():z.close()
 print('Output:',out)

if __name__=='__main__':main()
