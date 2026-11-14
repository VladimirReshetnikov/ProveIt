#!/usr/bin/env python3
"""Rebuild and audit PA194QHS without a repository checkout or network.

Default: both universal physical implementations, source/propositional audit,
command identities, all 32 fold cases, exact dense bytes, and whole startup.
--quick omits only the independent literal-tape replay; it still reruns the
construction symbolic engine. Recorded independent receipts remain separate.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile
ROOT=Path(__file__).resolve().parent

def run(args):
 print('Running:', ' '.join(map(str,args)),flush=True)
 subprocess.run([sys.executable,'-B',*map(str,args)],check=True)

def main():
 if not __debug__ or sys.flags.optimize:raise RuntimeError('Run without Python -O or PYTHONOPTIMIZE.')
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--quick',action='store_true');p.add_argument('--output',type=Path);a=p.parse_args()
 work=Path(tempfile.mkdtemp(prefix='pa194qhs_replay_'))
 generated=work/'machine'
 run([ROOT/'construction/build_qhs.py','--output',generated])
 for name in ['machine.tm','machine.native.tm','raw.native.tm','labels.json','nodes.json','folds.json','local_cases.json','instructions.json','sites.json','source.json','source_binding.json']:
  if (generated/name).read_bytes()!=(ROOT/'machine'/name).read_bytes():raise AssertionError('Rebuilt file mismatch: '+name)
 run([ROOT/'verification/check_source.py',generated,'--output',work/'source.json'])
 run([ROOT/'verification/check_commands.py','--output',work/'commands.json'])
 run([ROOT/'comparison/check_qhs_source.py',ROOT/'construction/inputs/parent_QH.instructions.json',generated/'instructions.json','--output',work/'independent_source.json'])
 run([ROOT/'comparison/compare_candidate.py',generated/'machine.tm','--output',work/'novelty.json'])
 novelty=json.loads((work/'novelty.json').read_text())
 if novelty['matches']:raise AssertionError('Candidate is already present in the pinned corpus.')
 if novelty['working_states']!=194 or novelty['start_graph_reachable']!=194:
  raise AssertionError('Candidate has the wrong size or graph reachability.')
 if not a.quick:run([ROOT/'verification/check_literal.py',generated,'--output',work/'independent'])
 result={'status':'PASS','machine_sha256':hashlib.sha256((generated/'machine.tm').read_bytes()).hexdigest(),
   'exact_reconstruction':True,'independent_literal_replay_performed':not a.quick,
   'independent_source_preservation_binding':True,'pinned_corpus_novelty':True,
   'evidence_directory':str(work),'kernel_checked':False,
   'scope':'Finite-source, command, and universal physical certificates; mathematical calibration and executor soundness are separate proof dependencies.'}
 if a.output:a.output.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
