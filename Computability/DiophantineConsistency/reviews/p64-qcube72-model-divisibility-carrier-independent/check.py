#!/usr/bin/env python3
"""Read-only direct-provider, log and scope review; no Lean launch."""
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def need(b,s):
    if not b:raise RuntimeError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
base=Path(__file__).resolve().parents[2];research=base/'research'
d=research/'p64-qcube72-model-divisibility-draft';c=research/'p64-qcube72-model-carrier-draft'
stages={
 'divisibility':(d,'attempt02','FreeMainDivisibility.lean','check02.py',True),
 'scale':(c,'scale01','FreeMainCarrierScale.lean','check01.py',True),
 'shape':(c,'shape01','FreeMainGraphShape.lean','check_shape01.py',True),
 'failed_graph':(c,'graph01','FreeMainGraphDivisibility.lean','check_graph01.py',False)}
expected_log={
 'divisibility':"'FreeMainDivisibility.dvd_of_cube_dvd_three' depends on axioms: [propext, Classical.choice, Quot.sound]\n'FreeMainDivisibility.scale_dvd_carrier' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
 'scale':"'FreeMainCarrierScale.of_carrier' depends on axioms: [propext, Classical.choice, Quot.sound]\n",
 'shape':"'FreeMainGraphShape.output_shape' depends on axioms: [propext]\n'FreeMainGraphShape.M_eval' depends on axioms: [propext]\n"}
receipts={};objects={};records={}
for label,(root,attempt,source_name,runner,ok) in stages.items():
    path=root/'observations'/attempt/'result.json';r=json.loads(path.read_text());records[label]=r
    need(r['guards_before']==r['guards_after'] and r['guards_stable'] and r['stop_reason'] is None,'guard or stop '+label)
    need(r['status']==('PASS' if ok else 'FAILED') and r['exit']==(0 if ok else -6),'status '+label)
    source=root/source_name; snap=root/'observations'/attempt/source_name
    need(sha(root/runner)==r['runner_sha256'] and sha(root/'missing_child.py')==r['missing_child_helper_sha256'],'runner/helper '+label)
    need(str(source) in r['guards_after'],'source guard missing '+label)
    for name,entry in r['guards_after'].items():
        p=Path(name)
        if p==source and not ok:
            need(snap.is_file() and sha(snap)==entry['sha256'] and sha(source)!=entry['sha256'],'failed source scope')
        elif entry is None:need(not os.path.lexists(p),'shadow appeared '+name)
        else:need(p.is_file() and str(p.resolve())==entry['realpath'] and sha(p)==entry['sha256'],'direct guard drift '+name)
    if snap.exists():need(sha(snap)==r['guards_after'][str(source)]['sha256'],'source snapshot '+label)
    obj=Path(r['command'][-1]);log=obj.parent/'compile.log'
    need(sha(log)==r['log_sha256'] and (obj.parent/'result.json').read_bytes()==path.read_bytes(),'log/receipt '+label)
    if ok:
        need(obj.is_file() and not obj.is_symlink() and sha(obj)==r['object_sha256'] and log.read_text()==expected_log[label],'success artifacts '+label)
    else:
        need(r['object_sha256'] is None and not os.path.lexists(obj) and 'lean::memory_exception' in log.read_text() and "excessive memory consumption detected at 'interpreter'" in log.read_text() and 'depends on axioms' not in log.read_text(),'failed graph artifacts')
    receipts[label]=sha(path);objects[label]=r['object_sha256']
def guarded(r,h):return any(isinstance(v,dict) and v.get('sha256')==h for v in r['guards_after'].values())
need(guarded(records['scale'],objects['divisibility']),'divisibility to scale')
graph_receipt=json.loads((research/'p64-qcube72-free-main-candidate/observations/graph/result.json').read_text())
need(graph_receipt['status']=='PASS' and guarded(records['shape'],graph_receipt['object_sha256']) and guarded(records['failed_graph'],objects['scale']),'graph/scale direct link')
# Verify exact named statement scope in the pinned source text.
s=(d/'FreeMainDivisibility.lean').read_text();sc=(c/'FreeMainCarrierScale.lean').read_text();sh=(c/'FreeMainGraphShape.lean').read_text();draft=(c/'FreeMainGraphDivisibility.lean').read_text()
for tok in ('theorem dvd_of_cube_dvd_three (q h : V)','(hd : q*q*q ∣ 3*h) : q ∣ h',
            'theorem scale_dvd_carrier (U D N : V) (hU : 0 < U)','(hm : D*D = U*U*N) : U ∣ D'):
    need(tok in s,'divisibility scope '+tok)
for tok in ('theorem of_carrier (q s X Y U H b h D N : V)','(hq : 0 < q) (hU0 : 0 < U)',
            '(hY : Y = q*q*q*s) (hU : U = Y*Y)','(hD : D = U*b+H*h) (hsq : D*D=U*U*N) : q ∣ h'):
    need(tok in sc,'scale scope '+tok)
for tok in ('theorem output_shape','theorem M_eval {R : Type*} [CommRing R]'):
    need(tok in sh,'shape scope '+tok)
need('import FreeMainGraphShape' in draft and 'theorem q_dvd_h' in draft,'current draft scope')
out={'status':'PASS_SCOPE_AND_RECEIPT_REVIEW','script_sha256':sha(__file__),
     'receipt_sha256':receipts,'object_sha256':objects,
     'failed_graph_source_sha256':sha(c/'observations/graph01/FreeMainGraphDivisibility.lean'),
     'current_unchecked_graph_source_sha256':sha(c/'FreeMainGraphDivisibility.lean'),
     'scope':'Read-only direct-pin/source review; graph01 failed and rewritten client is unchecked. No Lean replay, 72-zero q|h theorem, reverse map or iPRA endpoint.'}
print(json.dumps(out,indent=2,sort_keys=True))
