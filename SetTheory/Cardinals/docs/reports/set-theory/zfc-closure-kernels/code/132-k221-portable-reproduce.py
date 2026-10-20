#!/usr/bin/env python3
"""Offline K221 reconstruction and ordinary mathematical-certificate replay.
Default freshly proves all final K221 runtime cases. The baseline K222
calculus and source construction are replayed from the pinned complete delivery.
--quick checks stored
runtime integrity instead. --full-baseline also freshly replays all inherited
K222 and its inherited runtime proofs. No mode claims a new Rocq or Lean endpoint.
"""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,os,shutil,stat,subprocess,sys,time,zipfile
ROOT=Path(__file__).resolve().parent
BASE_SHA='4f677d8253846069a77dcac648a0a2bfe002ec8530886924ae3eba71e97e00d7'
def need(x,msg):
 if not x:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,obj):p.write_text(json.dumps(obj,indent=2)+'\n')
def safe(name):
 p=PurePosixPath(name);need(isinstance(name,str) and name and not p.is_absolute() and all(v not in ('','.','..') for v in name.rstrip('/').split('/')) and '\\'not in name and ':'not in name and '\x00'not in name,'Unsafe archive member');return p

def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output-dir',type=Path,required=True);ap.add_argument('--quick',action='store_true');ap.add_argument('--full-baseline',action='store_true');args=ap.parse_args()
 need(__debug__ and not sys.flags.optimize and not os.environ.get('PYTHONOPTIMIZE'),'Assertions must remain enabled')
 out=args.output_dir.resolve();need(out!=ROOT and ROOT not in out.parents,'Output must be outside portable directory');need(not out.exists()or not any(out.iterdir()),'Output must be initially empty');out.mkdir(parents=True,exist_ok=True);(out/'logs').mkdir()
 receipt=dict(status='RUNNING',mode='quick'if args.quick else'full_final_runtime',full_baseline=args.full_baseline,phases=[]);beg=time.monotonic()
 def save():receipt['seconds']=time.monotonic()-beg;dump(out/'replay.json',receipt)
 def phase(name,cmd):
  print(name,flush=True);start=time.monotonic();log=out/'logs'/(name+'.log')
  with log.open('w')as f:r=subprocess.run([sys.executable,'-B',*map(str,cmd)],stdout=f,stderr=subprocess.STDOUT,env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'})
  receipt['phases'].append(dict(name=name,returncode=r.returncode,seconds=time.monotonic()-start,log=str(log.relative_to(out))));save();need(r.returncode==0,'Phase failed: '+name+'; see '+str(log))
 try:
  # Complete portable manifest is sealed by the packaging stage.
  manifest=json.loads((ROOT/'manifest.json').read_text());need(manifest['schema_version']==1,'Manifest version')
  seen=set()
  for entry in manifest['files']:
   name=entry['path'];need(name not in seen and name!='manifest.json','Duplicate/self manifest entry');seen.add(name)
   p=ROOT/safe(name);need(p.is_file()and not p.is_symlink() and ROOT in p.resolve().parents,'Missing/nonregular/escaping manifest file')
   need(all(not parent.is_symlink() for parent in p.parents if parent!=ROOT),'Symlink manifest ancestor')
   need(p.stat().st_size==entry['size'] and sha(p)==entry['sha256'],'Manifest mismatch: '+name)
  actual=set()
  for p in ROOT.rglob('*'):
   need(not p.is_symlink(),'Symlink portable member')
   if p.is_file() and p!=ROOT/'manifest.json':actual.add(p.relative_to(ROOT).as_posix())
  need(actual==seen,'Manifest does not cover exact portable inventory')
  receipt['manifest_files']=len(manifest['files']);save()
  arc=ROOT/'vendor/K222_Construction_2026-10-20.zip';need(sha(arc)==BASE_SHA,'Pinned K222 archive differs')
  with zipfile.ZipFile(arc)as z:
   members=set()
   for info in z.infolist():
    r=safe(info.filename);need(r.parts[0]=='K222_Construction_2026-10-20','Unexpected baseline root')
    need(r.as_posix() not in members,'Duplicate archive member');members.add(r.as_posix())
    mode=stat.S_IFMT(info.external_attr>>16);need(mode in (0,stat.S_IFREG,stat.S_IFDIR) and not info.flag_bits&1,'Nonregular/encrypted archive member')
    target=out/'baseline'/r;need(out in target.resolve().parents,'Escaping archive member')
    if info.is_dir():target.mkdir(parents=True,exist_ok=True)
    else:
     target.parent.mkdir(parents=True,exist_ok=True)
     with z.open(info) as src,target.open('xb') as dst:shutil.copyfileobj(src,dst)
     need(target.stat().st_size==info.file_size,'Truncated archive member')
  baseline=out/'baseline/K222_Construction_2026-10-20'
  flags=['--full-baseline']if args.full_baseline else['--quick']
  phase('01_baseline222',[baseline/'portable/reproduce.py',*flags,'--output-dir',out/'baseline_replay'])
  phase('02_build221',[ROOT/'build221.py','--baseline',baseline,'--output',out/'construction'])
  phase('03_exact_source_equivalence',[ROOT/'verification/check_grammar_equivalence.py','--baseline',baseline/'machine/sites222.json','--candidate',out/'construction/sites.json','--output',out/'grammar221.json'])
  phase('04_exact_decoder_binding',[ROOT/'verification/check_decoder_binding.py','--source',out/'construction/sites.json','--allocation',out/'construction/allocation.json','--table',out/'construction/candidate.tm','--output',out/'decoder221.json'])
  phase('05_independent_all_tape_fold',[ROOT/'verification/check_fold_all_tapes.py','--old',out/'construction/prefold.tm','--new',out/'construction/candidate.tm','--witness',ROOT/'certificates/fold_witness.json','--output',out/'fold221.json'])
  phase('05b_second_all_tape_fold',[ROOT/'verification/check_fold_standalone.py','--old',out/'construction/prefold.tm','--new',out/'construction/candidate.tm','--certificate',ROOT/'certificates/fold_witness.json','--output',out/'fold221_second.json'])
  phase('06_canonical_and_blank',[ROOT/'canonicalize.py','--table',out/'construction/candidate.tm','--source',out/'construction/sites.json','--output',out/'canonical'])
  if args.quick:
   shutil.copytree(ROOT/'runtime/reference_results',out/'runtime')
   need((out/'runtime/candidate.tm').read_bytes()==(out/'construction/candidate.tm').read_bytes(),'Stored runtime table differs')
   need((out/'runtime/sites.json').read_bytes()==(out/'construction/sites.json').read_bytes(),'Stored runtime source differs')
  else:phase('07_fresh_unbounded_runtime',[ROOT/'runtime/verify221.py',out/'construction',out/'runtime'])
  phase('08_independent_runtime_audit',[ROOT/'runtime/audit221.py',out/'runtime'])
  phase('09_fresh_source_invariants',[ROOT/'runtime/generate_invariants221.py',out/'runtime'])
  phase('10_independent_invariant_audit',[ROOT/'runtime/check_invariants221.py',out/'runtime'])
  receipt.update(status='QUICK_K221_REPLAY_PASS'if args.quick else'FULL_K221_REPLAY_PASS',source_sha256=sha(out/'construction/sites.json'),native_table_sha256=sha(out/'construction/candidate.tm'),canonical_table_sha256=sha(out/'canonical/k221.tm'),proof_boundary='Ordinary mathematical certificates; no newly compiled exact221 Rocq/Lean endpoint. Runtime receipts alone do not establish consistency calibration.');save();print(receipt['status'],flush=True)
 except Exception as e:receipt.update(status='FAILED',error=repr(e));save();raise
if __name__=='__main__':main()
