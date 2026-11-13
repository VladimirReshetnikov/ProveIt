#!/usr/bin/env python3
"""Read-only receipt and direct-pin audit; does not replay Lean."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def req(x,s):
    if not x:raise RuntimeError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=Path(__file__).resolve().parents[2]
d=base/'research'/'p64-qcube72-forward-graph-draft'
rfile=d/'observations'/'attempt03'/'result.json';r=json.loads(rfile.read_bytes())
req(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'],'receipt status')
req(r['guards_before']==r['guards_after'],'guard comparison')
req(r['group_rss_samples']>0,'no RSS samples')
for p,info in r['guards_after'].items():
    p=Path(p)
    if info is None:req(not os.path.lexists(p),'new guarded companion '+str(p))
    else:req(p.is_file() and str(p.resolve())==info['realpath'] and sha(p)==info['sha256'],'direct guard drift '+str(p))
req(sha(d/'check03.py')==r['runner_sha256'] and sha(d/'missing_child.py')==r['missing_child_helper_sha256'],'runner/helper')
source=d/'FreeMainGraphForward.lean';snap=d/'observations'/'attempt03'/'FreeMainGraphForward.lean'
req(source.read_bytes()==snap.read_bytes(),'source snapshot mismatch')
s=source.read_text()
for token in ['theorem actual_gap_positive','theorem exists_positive_main_gap',
 'InternalZero (P64QCube76Y.graph','P64Root.main_root p w hwp hb hF hYdiv hmain',
 'FreeMainForward.positive_of_pell_bound','P64QCubeMap.lift_pos p v hv']:
    req(token in s,'source statement/derivation '+token)
req('sorry' not in s and 'admit' not in s and 'axiom ' not in s,'unexpected source admission')
tmp=Path('/tmp/p64-qcube72-forward-graph-priority-check03')
req((tmp/'result.json').read_bytes()==rfile.read_bytes(),'copied receipt mismatch')
req(sha(tmp/'FreeMainGraphForward.olean')==r['object_sha256'] and sha(tmp/'compile.log')==r['log_sha256'],'object/log hashes')
expected=("'FreeMainGraphForward.actual_gap_positive' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
          "'FreeMainGraphForward.exists_positive_main_gap' depends on axioms: [propext, Classical.choice, Quot.sound]\n")
req((tmp/'compile.log').read_text()==expected,'unexpected full compiler output')
providers=[(base/'research'/'p64-qcube72-forward-model-guarded'/'observations'/'attempt01'/'result.json',
            '/tmp/p64-qcube72-forward-priority-check01/FreeMainForward.olean'),
           (base/'research'/'p64-qcube76y-graph-model-guarded-check'/'observations'/'attempt02'/'result.json',
            '/tmp/p64-qcube76y-graph-model-priority-check02/IndependentYGraphDraft.olean')]
provider_links={}
for receipt,obj in providers:
    info=json.loads(receipt.read_text())
    req(info['status']=='PASS' and info['exit']==0 and info['object_sha256']==sha(obj),'provider receipt '+str(receipt))
    provider_links[str(receipt.relative_to(base))]={'receipt_sha256':sha(receipt),'object_sha256':sha(obj)}
result={'status':'PASS_RECEIPT_AND_SOURCE_SCOPE_REVIEW','script_sha256':sha(__file__),
 'reviewed_receipt_sha256':sha(rfile),'source_sha256':sha(source),'log_sha256':sha(tmp/'compile.log'),
 'object_sha256':sha(tmp/'FreeMainGraphForward.olean'),'direct_guard_count':len(r['guards_after']),
 'provider_links':provider_links,
 'scope':'Read-only review of actual-zero gap positivity and selected direct receipts; no Lean replay, reverse map, existence equivalence, iPRA endpoint or full transitive ancestry.'}
print(json.dumps(result,indent=2,sort_keys=True))
