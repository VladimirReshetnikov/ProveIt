#!/usr/bin/env python3
"""Reproduce conditional-K223, writing exclusively to an external output directory."""
from pathlib import Path
import argparse,hashlib,json,shutil,subprocess,sys,time,zipfile
HERE=Path(__file__).resolve().parent

def need(p,m):
 if not p:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output-dir',type=Path,required=True);ap.add_argument('--full',action='store_true',help='Freshly rederive all 6,238 unbounded guarded instruction cases.');a=ap.parse_args();out=a.output_dir.resolve()
 need(out!=HERE and HERE not in out.parents,'Output must be outside the immutable packet')
 manifest=json.loads((HERE/'MANIFEST.json').read_text())
 actual={str(p.relative_to(HERE))for p in HERE.rglob('*')if p.is_file()and p.name!='MANIFEST.json'}
 need(actual==set(manifest),'Packet inventory differs from MANIFEST.json')
 for name,expected in manifest.items():need(sha(HERE/name)==expected,f'Packet checksum mismatch: {name}')
 archive=HERE/'upstream/K224_Construction_2026-10-20.zip';need(sha(archive)=='cf5db8d08a34f5661ad1266226809ed1f0099fd38374c66d127e1e06519c6887','Changed upstream archive')
 with zipfile.ZipFile(archive)as z:
  prefix='K224_Construction_2026-10-20/';lines=z.read(prefix+'SHA256SUMS').decode().splitlines();up={name:expected for expected,name in(line.split(None,1)for line in lines)}
  need(set(z.namelist())=={prefix+n for n in up}|{prefix+'SHA256SUMS'},'Upstream inventory')
  for name,expected in up.items():need(hashlib.sha256(z.read(prefix+name)).hexdigest()==expected,f'Upstream checksum: {name}')
  bindings={'baseline224.k.tm':'portable/machine/results/candidate224.k.tm','baseline_sites.json':'portable/parent225/sites225.json','parent225.k.tm':'portable/parent225/candidate225.k.tm','legacy_state_map.json':'portable/machine/reference/legacy_state_map.json','emitter_contract.json':'portable/theory/emitter_contract.json'}
  for local,member in bindings.items():need((HERE/'inputs'/local).read_bytes()==z.read(prefix+member),f'Upstream input binding: {local}')
 need(not out.exists()or not any(out.iterdir()),'Output directory must be new or empty');out.mkdir(parents=True,exist_ok=True);beg=time.monotonic();logs=out/'logs';logs.mkdir();checks=['pinned_upstream_inventory_and_input_bindings']
 def run(name,args,opt=False):
  print(name,flush=True);cmd=[sys.executable,'-B']+(['-O']if opt else[])+[str(x)for x in args]
  with(logs/f'{name}.log').open('w')as f:subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,check=True)
  checks.append(name)
 # Snapshot executable audit material; every generated receipt lives in out.
 for name in['inputs','audit','contextual','runtime']:shutil.copytree(HERE/name,out/name)
 run('construction',[HERE/'build.py','--output',out/'results'])
 run('source_emitter_hilbert',[HERE/'theory/verify_conditional_source.py','--base-sites',out/'inputs/baseline_sites.json','--candidate-sites',out/'results/sites.json','--output',out/'source_emitter_binding.json'])
 # The independently authored source audit binds the same Hilbert endpoints.
 (out/'theory').mkdir();shutil.copyfile(HERE/'theory/conditional_fusion_certificate.json',out/'theory/conditional_fusion_certificate.json')
 run('independent_source',[out/'audit/check_conditional223_source.py'],True)
 D=out/'fold_binding';F=D/'fold_0';F.mkdir(parents=True)
 for src,dest in [('prefold224.k.tm',D/'candidate.tm'),('candidate223.k.tm',F/'candidate.tm')]:shutil.copyfile(out/'results'/src,dest)
 for dest in [D/'sites.json',F/'sites.json']:shutil.copyfile(out/'results/sites.json',dest)
 shutil.copyfile(HERE/'inputs/allocation.json',D/'allocation.json');shutil.copyfile(out/'results/local_fold_proof.json',F/'local_proof.json');recipe=json.loads((HERE/'recipe.json').read_text())['fold'];dump(F/'recipe.json',dict(keep=recipe['keep'],drop=recipe['drop'],helpers=recipe['helpers'],kind='general_three_step_tag'))
 run('transparent_fold',[out/'audit/check_conditional223_fold.py'],True)
 run('independent_fold_certificate',[out/'contextual/replay_local_certificate.py'],True)
 R=out/'runtime';RR=R/'results';RR.mkdir(exist_ok=True)
 shutil.copyfile(out/'results/candidate223.k.tm',R/'inputs/candidate.tm');shutil.copyfile(out/'results/sites.json',R/'inputs/sites.json');shutil.copyfile(R/'reference/invariants.json',RR/'invariants.json')
 if a.full:
  run('full_unbounded_runtime',[R/'verify223.py'])
 else:
  needed=['proof.json','cases.json','candidate.legacy.tm','legacy_mapping.json']
  for name in needed:
   p=HERE/'runtime/reference/portable'/name;need(p.exists(),f'No stored portable evidence {name}; use --full')
   shutil.copyfile(p,RR/name)
  shutil.copyfile(R/'inputs/candidate.tm',RR/'candidate.tm');shutil.copyfile(R/'inputs/sites.json',RR/'sites.json')
 run('independent_runtime_integrity_startup',[R/'audit223.py'],True)
 run('independent_source_invariant',[R/'check_invariants223.py'],True)
 run('independent_decoder_bindings',[out/'contextual/audit_decoder_bindings.py'],True)
 C=out/'canonical';C.mkdir();ren=json.loads((out/'results/renumbering223.json').read_text())
 for src,dest in [('candidate223.tm','k223.tm'),('candidate223.k.tm','k223.native.tm'),('sites.json','sites223.json')]:shutil.copyfile(out/'results'/src,C/dest)
 dump(C/'canonicalization.json',dict(halt=223,native_to_canonical=ren['native_to_canonical'],canonical_to_native=ren['canonical_to_native'],canonical_sha256=sha(C/'k223.tm'),native_sha256=sha(C/'k223.native.tm'),source_sha256=sha(C/'sites223.json')))
 run('independent_canonical_isomorphism',[out/'contextual/audit_canonical.py'],True)
 run('seven_tamper_controls',[out/'contextual/tamper_controls.py'],True)
 proof=json.loads((RR/'proof.json').read_text());res=dict(status='FULL_REPRODUCTION_PASS'if a.full else'QUICK_REPRODUCTION_AND_STORED_EVIDENCE_PASS',fresh_unbounded_runtime_replay=a.full,working_states=223,rows=446,guarded_cases=proof['cases'],startup_steps=proof['startup']['steps'],canonical_sha256=sha(out/'results/candidate223.tm'),native_sha256=sha(out/'results/candidate223.k.tm'),source_sha256=sha(out/'results/sites.json'),checks=checks,seconds=time.monotonic()-beg,scope='Exact construction and emitter/fusion binding, whole-tape local fold, startup, stored runtime integrity/coverage, source invariants, decoder/label/canonical binding, and negative controls. With --full, also freshly rederives every unbounded instruction case. Mathematical equiconsistency and inherited macro/calculus contracts are documented separately in theory/.')
 dump(out/'reproduction.json',res);print(json.dumps(res,indent=2))
if __name__=='__main__':main()
