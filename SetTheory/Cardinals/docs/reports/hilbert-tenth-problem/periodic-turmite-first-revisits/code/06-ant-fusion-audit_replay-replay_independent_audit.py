#!/usr/bin/env python3
"""Relocate the exact frozen independent fusion audits without changing them.
Only path/provenance binding changes. All imports and outputs are explicit.
"""
import argparse, hashlib, importlib.util, json, os, pathlib, runpy, sys
sys.dont_write_bytecode=True
AUDIT_MANIFEST_SHA='6ffaa0336e1fac214a76e9f46d4c652eaabd804c601f42cd6605a7484a0302bb'
CANDIDATE_PINS={
 'fusion_source.py':'5e433001dcdb4a26f7dcb0419a41f124fae983aeb76088d55d4b603802232f60',
 'INPUT_PINS.json':'d8a6f7131539c8c3b04caee0f17094b6e12845e23a690dd5b7712d95a64d9eb9',
 'fused-receipt.json':'8230ba6bed0e6209f814094168551282252c709681cc0b744cace678e4b703ee'}
ORIGINAL_BASE=pathlib.PurePosixPath('/workspace/shared/ant-compression-report47-release-20261004')
COPY_FILES=('audit_exact.py','audit_caches_weights.py','GENERIC_PROOF.md')

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def require(test,message):
 if not test:raise ValueError(message)
def json_read(path):return json.loads(path.read_text())
def tree(root):return {str(p.relative_to(root)):sha(p) for p in sorted(root.rglob('*')) if p.is_file()}
def relpath(text):
 p=pathlib.PurePosixPath(text)
 require(not p.is_absolute() and all(x not in ('.','..') for x in p.parts),'Unsafe relative path: '+text)
 return pathlib.Path(*p.parts)
def checked_dir(text):
 p=pathlib.Path(text).resolve(strict=True);require(p.is_dir(),'Not a directory: '+str(p));return p

def main():
 require(__debug__,'Optimized Python is not supported; use python -B, never -O')
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--audit-dir',required=True,help='Frozen independent_audit directory, without candidate_snapshot if omitted from package')
 ap.add_argument('--candidate-dir',required=True,help='Frozen Report48 science directory')
 ap.add_argument('--report47-dir',required=True,help='Extracted complete Research_Report47 release directory')
 ap.add_argument('--out-dir',required=True,help='Previously absent directory outside all three source trees; its parent must exist')
 args=ap.parse_args()
 audit=checked_dir(args.audit_dir);candidate=checked_dir(args.candidate_dir);baseline=checked_dir(args.report47_dir)
 requested=pathlib.Path(args.out_dir)
 require(not os.path.lexists(requested),'Output already exists; select a new directory')
 output=requested.parent.resolve(strict=True)/requested.name
 require(output.name not in ('.','..') and not os.path.lexists(output),'Output is not a new directory')
 for src in [audit,candidate,baseline]:
  require(output!=src and src not in output.parents,'Output must be outside source tree '+str(src))
 require(sha(audit/'MANIFEST.json')==AUDIT_MANIFEST_SHA,'Frozen audit manifest hash mismatch')
 manifest=json_read(audit/'MANIFEST.json')
 for rel,h in manifest.items():require(sha(audit/relpath(rel))==h,'Frozen audit file hash mismatch: '+rel)
 for rel,h in CANDIDATE_PINS.items():require(sha(candidate/rel)==h,'Frozen candidate file hash mismatch: '+rel)
 baseline_expected=json_read(audit/'frozen-before.json')
 baseline_before=tree(baseline)
 require(baseline_before==baseline_expected,'Extracted Report47 release differs from the95 frozen baseline files')
 source_before={'audit':tree(audit),'candidate':tree(candidate)}
 input_pins=json_read(candidate/'INPUT_PINS.json')
 require(len(input_pins)==18,'Unexpected provenance inventory')
 mapped={}
 for rel,row in input_pins.items():
  local=relpath(rel)
  original=pathlib.PurePosixPath(row['source'])
  require(original.is_relative_to(ORIGINAL_BASE),'Unexpected original provenance root: '+row['source'])
  suffix=relpath(str(original.relative_to(ORIGINAL_BASE)))
  require(sha(candidate/local)==sha(baseline/suffix)==row['sha256'],'Relocated provenance hash mismatch: '+rel)
  mapped[rel]={'baseline_relative_path':suffix.as_posix(),'sha256':row['sha256']}
 output.mkdir(mode=0o700)
 for rel in COPY_FILES:
  with (output/rel).open('xb') as f:f.write((audit/rel).read_bytes())
 # Import byte-identical audited code from the fresh output directory. The module
 # guard prevents a run before its three path bindings and provenance hook change.
 spec=importlib.util.spec_from_file_location('audit_exact',output/'audit_exact.py')
 module=importlib.util.module_from_spec(spec);sys.modules['audit_exact']=module;spec.loader.exec_module(module)
 module.ROOT=output;module.SNAP=candidate;module.BASE=baseline
 def authenticate_relocated():
  # Same equality/hash checks as the frozen authenticate(); only the source path
  # uses the authenticated baseline-relative mapping rather than an old location.
  pins=json_read(candidate/'INPUT_PINS.json')
  require(pins==input_pins,'Input pins changed during replay')
  for rel,row in pins.items():
   target=baseline/relpath(mapped[rel]['baseline_relative_path'])
   require(sha(candidate/relpath(rel))==sha(target)==row['sha256'],'Relocated authentication failed: '+rel)
  receipt=json_read(candidate/'fused-receipt.json')
  require(sha(candidate/'fusion_source.py')==receipt['source_sha256'],'Candidate source/receipt mismatch')
  return receipt,pins
 module.authenticate=authenticate_relocated
 print('Authenticated frozen inputs; running exact coefficient and full-source audit',flush=True)
 module.main()
 # This frozen script intentionally runs at import. run_path executes its exact
 # copied bytes with __file__ in the fresh directory; import audit_exact resolves
 # to the already-bound authenticated module above. No source-tree write occurs.
 print('Running exact cache and ordinary-polynomial weight audit',flush=True)
 runpy.run_path(str(output/'audit_caches_weights.py'),run_name='__main__')
 require(tree(baseline)==baseline_before,'Baseline source files changed')
 require(tree(audit)==source_before['audit'],'Audit source files changed')
 require(tree(candidate)==source_before['candidate'],'Candidate source files changed')
 repeated={}
 for rel in ['audit-receipt.json','finite-identities.json','caches-weights-receipt.json','frozen-before.json','frozen-after.json']:
  require(json_read(output/rel)==json_read(audit/rel),'Replay evidence differs from frozen evidence: '+rel)
  repeated[rel]={'sha256':sha(output/rel),'json_identical_to_frozen':True}
 result={'status':'PASS_RELOCATED_FROZEN_INDEPENDENT_AUDITS','adapter_sha256':sha(pathlib.Path(__file__)),'frozen_audit_manifest_sha256':AUDIT_MANIFEST_SHA,'candidate_pins':CANDIDATE_PINS,'provenance_mapping':mapped,'frozen_scripts_byte_identical':True,'replayed_evidence':repeated,'baseline_files':len(baseline_before),'all_source_trees_unchanged':True,'outputs_only_in_fresh_directory':True,'no_upstream_physical_execution':True}
 with (output/'replay-receipt.json').open('x') as f:json.dump(result,f,indent=2);f.write('\n')
 print(result['status'],flush=True)
if __name__=='__main__':main()
