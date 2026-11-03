#!/usr/bin/env python3
"""Read-only review of the direct graph's fixed-port model halt bridge."""
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys

if sys.flags.optimize: raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe'
B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
H=D/'research/ordinary12-xq91-candidate/observations/halt-attempt04/terminal.json'
E=P/'observations/equivalence-attempt01';PB=P/'observations/portbounds-attempt01'
A1=P/'observations/halt-attempt01';A2=P/'observations/halt-attempt02';A=P/'observations/haltv2-attempt01'
PINS={P/'HALT.md':'801afbc176b65de01b475bf245a9de8d47f06cac1e3477a37d216c7130778144',
 P/'DirectMainHalt.lean':'d522a6dda7a6515cece3ac60f0fcad082b361987ee3556962fd8d51fdcdfdc12',
 P/'DirectPortBounds.lean':'40a3015bb7b3b526f14e6403121055845ff70d368c789daa5ee48567cfce2ae8',
 P/'run-portbounds.py':'94ef2f6c996bc995fa31b9e0503a890594a865471c7dca5a6cdede168124bd57',
 P/'run-halt.py':'88810f0e9eb2fbe014b14ee9d1f45de7a252b4315f2ddee72079c7b2833534c0',
 P/'run-halt-v2.py':'e65321dd9e1f1dbb9636b52335f086e225d3ddf2557fd0edf00d514114d4ead4',
 E/'terminal.json':'e53e7960c10aa1194001c147a8a11eafb6505fdfc557624ed7145e48fbcfd2bb',
 PB/'terminal.json':'c4c79382721a94e7ce218455b919f8598bcc759478a350f1091f65f86dba956b',
 A1/'terminal.json':'5f54de1457d4526808049e74534bc5c4d6dbd982a086ed0025af49ad4eada1f4',
 A2/'terminal.json':'584810a1ea237d8572df8163166954174bae8e6992323ffc75134ccbb3d1caca',
 A/'terminal.json':'67fc1a846731aab86e408e198475e2cae6a21820575a3a21a21accf8a3f15e4d',
 B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f',
 H:'c803da72a3e41dd422dc697425bf20ccf1bb4624be67ac0138a0ce42e39310c5'}
def need(x,m):
    if not x:raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def verify_pins():
    for p,h in PINS.items():need(sha(p)==h,'input mismatch: '+str(p))
verify_pins()
s=(P/'DirectMainHalt.lean').read_text();b=(P/'DirectPortBounds.lean').read_text()
for text in (s,b):
    need('variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in text,'model assumption')
    need('set_option linter.' not in text,'unexpected local lint suppression')
for fragment in (
 'import DirectMainEquivalence','import XQ91Halt','import DirectPortBounds',
 'theorem positive_model_iff :', 'InternalZero (graph p).output v',
 'ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0',
 'CompactFixedBeta.bounds (1:V) (by simp)',
 'DirectPortBounds.bounds CompactFixedBeta.betaNat (paramKernel rho) lowNat highNat',
 'hbounds.1 hbounds.2.1 hbounds.2.2.1',
 'DirectMainEquivalence.positive_zero_iff naturalPorts hp.1 hp.2.1 hp.2.2',
 'h.trans (FreeJXQ91Halt.positive_model_iff (V:=V))',
 'theorem shifted_model_iff :', 'internalZero_positiveShift',
 'tsub_add_cancel_of_le (pos_iff_one_le.mp (hpos j))',
 'theorem shifted_byte_model_iff :', 'rw [byteP_eq]',
):need(fragment in s,'halt statement or proof mismatch: '+fragment)
for fragment in ('theorem bounds (beta K L H : ℕ)',
 '(hb : 0<(beta:V)) (hl : (L:V)<(beta:V))',
 '(hh : (beta:V)+(H:V)<2*(beta:V))',
 'let ps := ports beta K L H',
 '0<(ps 0:V) ∧ (ps 2:V)<(ps 0:V) ∧ (ps 3:V)<2*(ps 0:V)',
 'change ((beta+H:ℕ):V)<2*(beta:V)', 'rw [Nat.cast_add]'):
    need(fragment in b,'port bounds mismatch: '+fragment)

equiv=json.loads((E/'terminal.json').read_text());port=json.loads((PB/'terminal.json').read_text())
ok=json.loads((A/'terminal.json').read_text());bad1=json.loads((A1/'terminal.json').read_text());bad2=json.loads((A2/'terminal.json').read_text())
for folder,receipt,source,runner in ((PB,port,'DirectPortBounds.lean','run-portbounds.py'),
                                    (A,ok,'DirectMainHalt.lean','run-halt-v2.py')):
    need(receipt['exit']==0 and receipt['reason'] is None and receipt['union_unchanged'] and receipt['halt_union_unchanged'] and
         receipt['union_count']==1291 and receipt['halt_union_count']==1294,'accepted receipt failed')
    need(sha(folder/'source.txt')==receipt['source_sha256']==receipt['source_after']==sha(P/source),'source mismatch: '+source)
    need(receipt['runner_sha256']==receipt['runner_after']==sha(P/runner),'runner mismatch: '+runner)
    need(receipt['lean_sha256']==receipt['lean_after']==sha(receipt['command'][0]),'Lean binary mismatch')
    need(sha(folder/'stdout')==receipt['stdout_sha256'] and sha(folder/'stderr')==receipt['stderr_sha256'] and not (folder/'stderr').read_bytes(),'log mismatch')
    need(receipt['base_receipt_sha256']==sha(B) and receipt['halt_receipt_sha256']==sha(H),'base receipt mismatch')
    out=Path(receipt['output_root'])/source.replace('.lean','.olean')
    need(sha(out)==receipt['object_sha256'],'output mismatch: '+source)
for folder,receipt in ((A1,bad1),(A2,bad2)):
    log=(folder/'stdout').read_text()
    need(receipt['exit']!=0 and 'error:' in log and 'excessive memory' in log,'failure not preserved')
    need(sha(folder/'source.txt')==receipt['source_sha256'] and sha(folder/'stdout')==receipt['stdout_sha256'] and
         sha(folder/'stderr')==receipt['stderr_sha256'],'failed snapshot mismatch')
need('Type mismatch' in (A1/'stdout').read_text(),'attempt01 cast mismatch not preserved')
need((PB/'stdout').read_text()=="'DirectPortBounds.bounds' depends on axioms: [propext, Classical.choice, Quot.sound]\n",'port axiom report')
expected=''.join("'DirectMainHalt."+n+"' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for n in
                 ('positive_model_iff','shifted_model_iff','shifted_byte_model_iff'))
need((A/'stdout').read_text()==expected,'halt axiom reports')
need(ok['object_sha256']=='90076ca109db40f625a9cd7574782f44a0531336fc1c423ccff2748545c711ee','halt object pin')

paths=[Path(x) for x in ok['lean_path'].split(':')]
def first(module):
    xs=[p/(module+'.olean') for p in paths if (p/(module+'.olean')).is_file()]
    need(xs,'missing first-resolved module: '+module)
    return xs[0]
for key,module,receipt in [('portbounds','DirectPortBounds',port),('equivalence','DirectMainEquivalence',equiv)]:
    path=first(module)
    need(path==Path(receipt['output_root'])/(module+'.olean') and sha(path)==receipt['object_sha256']==ok[key+'_producer_sha256'],
         'first-resolved direct input mismatch: '+module)
halt_receipt=json.loads(H.read_text());halt=first('XQ91Halt')
need(halt==Path(halt_receipt['output_root'])/'XQ91Halt.olean' and sha(halt)==ok['xq91_halt_producer_sha256']==halt_receipt['object_sha256'],'XQ91 halt input mismatch')
for key,value in equiv.items():
    if key.endswith('_producer_sha256'):need(ok.get(key)==value,'inherited producer mismatch: '+key)

base=json.loads(B.read_text());haltbase=json.loads(H.read_text());haltlib=paths[-3];lib=paths[-2]
def inventory(root, expected, count):
    actual={x.relative_to(root).as_posix():x for x in root.rglob('*') if x.is_file()}
    need(len(actual)==count and set(actual)==set(expected),'union membership mismatch: '+str(root))
    for n,p in actual.items():
        z=expected[n]
        need(p.is_symlink() and os.readlink(p)==z['link'] and str(p.resolve(strict=True))==z['resolved'] and sha(p)==z['sha256'],'union mismatch: '+n)
def verify_unions():
    inventory(lib,base['union'],1291);inventory(haltlib,haltbase['union'],1294)
    need(all(name in haltbase['union'] and haltbase['union'][name]['sha256']==z['sha256'] for name,z in base['union'].items()),'shared provider hash conflict')
verify_unions()
for review in ('ordinary12-direct-main-equivalence-independent','ordinary12-xq91-halt-independent'):
    proc=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews'/review/'check.py')],capture_output=True,timeout=180)
    need(proc.returncode==0 and not proc.stderr and json.loads(proc.stdout)['status']=='PASS','prior review failed: '+review)
verify_unions();verify_pins()
need(sha(Path(ok['output_root'])/'DirectMainHalt.olean')==ok['object_sha256'],'halt object changed')
print(json.dumps({'status':'PASS','positive_shifted_byte_theorems':3,'fixed_beta_and_port_bounds':'PASS',
                  'direct_and_halt_unions':[1291,1294],'shared_hashes':1291,'failed_attempts_preserved':2,
                  'preexisting_lean_processes':len(ok['preflight']['lean']),
                  'maximum_sampled_lean_processes':max(len(x['lean']) for x in ok['samples']),
                  'scope':'all-IΣ₁-model halt theorem; no internal iPRA or Lean PDF/file theorem'},indent=2))
