#!/usr/bin/env python3
"""Rebuild and verify the accepted PA194QN5/QN6 tables without network access.

Default mode performs all construction and independent literal-tape checks.
--quick omits both long universal physical replays, but retains the exact input,
source, algebraic, quotient, full-startup and table-identity checks.
Fresh generated files go in a new directory, never over the release evidence.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile,time
ROOT=Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 if not __debug__ or sys.flags.optimize:raise SystemExit('Run without -O.')
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--quick',action='store_true')
 ap.add_argument('--full',action='store_true',help='Explicit full verification (the default).')
 ap.add_argument('--work',type=Path)
 a=ap.parse_args()
 if a.quick and a.full:ap.error('--quick and --full are mutually exclusive')
 if a.work:
  work=a.work.resolve();work.mkdir(parents=True,exist_ok=False)
 else:work=Path(tempfile.mkdtemp(prefix='pa194qn-replay-'))
 started=time.time()
 args=[sys.executable,'-B',str(ROOT/'construction/build.py'),'--output',str(work/'machines')]
 if a.quick:args.append('--quick')
 subprocess.run(args,check=True)
 machines=[work/'machines'/name for name in ['PA194QN5','PA194QN6']]
 for machine in machines:
  for file in ['machine.tm','machine.native.tm','raw.native.tm','sites.json','instructions.json','nodes.json','folds.json','local_cases.json','labels.json','emitter_audit.json','source_binding.json']:
   assert (machine/file).read_bytes()==(ROOT/'machines'/machine.name/file).read_bytes(),(machine.name,file)
 subprocess.run([sys.executable,'-B',str(ROOT/'verification/independent/source_audit.py'),*[str(p)for p in machines],'--output',str(work/'independent')],check=True)
 subprocess.run([sys.executable,'-B',str(ROOT/'verification/exchange_certificate.py'),'--output',str(work/'exchange_certificate.json')],check=True)
 assert (work/'exchange_certificate.json').read_bytes()==(ROOT/'verification/exchange_certificate.json').read_bytes()
 subprocess.run([sys.executable,'-B',str(ROOT/'comparison/check_novelty.py'),
   *[str(p/'machine.tm')for p in machines],
   '--output',str(work/'candidate_novelty.json')],check=True)
 novelty=json.loads((work/'candidate_novelty.json').read_text())
 assert len(novelty)==2
 assert all(x['structurally_new_in_corpus'] and not x['matches'] and
            x['same_size_spanning_tables']==76 and
            x['literal_representatives_reparsed_and_hash_checked']==76
            for x in novelty)
 if not a.quick:
  subprocess.run([sys.executable,'-B',str(ROOT/'verification/independent/check.py'),*[str(p)for p in machines],'--output',str(work/'independent')],check=True)
 result={'status':'PASS','mode':'quick'if a.quick else'full','machines':[],
   'universal_physical_replays_performed':not a.quick,
   'source_and_emitter_independently_reconstructed':True,
   'novelty_rechecked_against_76_literal_frontier_tables':True,
   'fresh_directory':str(work),'elapsed_seconds':time.time()-started,
   'scope':'Executable certificates and exact artifact identities; not an end-to-end proof-assistant theorem.'}
 for machine in machines:result['machines'].append({'name':machine.name,'dense_sha256':sha(machine/'machine.tm')})
 (work/'reproduction_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2),flush=True)
if __name__=='__main__':main()
