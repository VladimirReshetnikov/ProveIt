#!/usr/bin/env python3
"""Read-only audit of bounded-port direct/91 positive-zero equivalence."""
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys

if sys.flags.optimize: raise SystemExit('optimized Python refused')
D=Path(__file__).resolve().parents[2];P=D/'research/ordinary12-direct-main-probe'
B=D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json'
E=P/'observations/equivalence-attempt01';R0=P/'observations/restricted-attempt01'
R=P/'observations/restricted-attempt02';F=P/'observations/forward-attempt01'
G=P/'observations/gap-attempt02'
PINS={P/'EQUIVALENCE.md':'efac76bf4d8f025c59ba71e939b0c24604e9a9eb4d4e3809f00a75abcaf9b158',
      P/'DirectMainEquivalence.lean':'fa47d935f56421fc923cc847d885ff86710df9b12fba453f214b00a116ad2dbb',
      P/'run-equivalence.py':'645ab96950516a9a844d5e811e35301b9b9e27e5044a39bf00e0754bd84969ce',
      P/'RESTRICTED.md':'14ca18bd3d672ba6e569316b091005cda2a7417197db0fcd221e924a33ee2c2f',
      P/'DirectMainRestricted.lean':'325c6a956f8a5942b0d5861111d170e2a2b6fe9ab19815c42ec69a2dfb45bbbe',
      P/'DirectMainForward.lean':'de770e415209f42b1d0222a8e41edb573efe86cf0884ee88b786a6f536f6c491',
      E/'terminal.json':'e53e7960c10aa1194001c147a8a11eafb6505fdfc557624ed7145e48fbcfd2bb',
      R0/'terminal.json':'e8b839a4d94f766b75d482078af2fb4f12032d915ed5eef2f3ffe26ca72cfe32',
      R/'terminal.json':'48b6f9cc81cb574647ebad1007b290e1cd1cc5c5ecd916dd8837ed63da1171e4',
      F/'terminal.json':'d0ee9633116c763c60067bdf76b9fa6dbfb1d64c3f729772074611a1c909d3d9',
      G/'terminal.json':'49eb8ec66b51700455705f57eb51cf201e353ad00ca805c8aa47264e8509212a',
      B:'8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'}
def need(x,m):
    if not x: raise SystemExit(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def verify_pins():
    for p,h in PINS.items():need(sha(p)==h,'input mismatch: '+str(p))
verify_pins()
s=(P/'DirectMainEquivalence.lean').read_text();r=(P/'DirectMainRestricted.lean').read_text();f=(P/'DirectMainForward.lean').read_text()
for text in (s,r,f):
    need('variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]' in text,'model assumption')
    need('set_option linter.' not in text,'unexpected local lint suppression')
for fragment in (
 'theorem positive_zero_iff (p : Fin 4 → ℕ)',
 '(hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))',
 'InternalZero (graph (DirectMainForward.integerPorts p)).output v',
 'InternalZero (FreeJXQ91.graph (DirectMainForward.integerPorts p)).output v',
 'DirectMainGap.graph_gap p v hb hl hh hv hz',
 '(DirectMainRestricted.exists_iff_restricted p).mpr ⟨v,hv,hgap,hz⟩',
 'DirectMainForward.exists_direct_of_xq91 p h',
):need(fragment in s,'equivalence statement/composition mismatch: '+fragment)
for fragment in ('def inverse (v : Fin 12 → V) : Fin 12 → V := Function.update v 11 (v 11-v 5)',
                 '(hgap : v 5<v 11)', 'tsub_pos_iff_lt.mpr hgap',
                 'tsub_add_cancel_of_le (le_of_lt hgap)',
                 'v 5<v 11 ∧ InternalZero (graph (integerPorts p)).output v',
                 '(zero_iff p (inverse v)).mp', 'rw [inverse_transform v hgap]'):
    need(fragment in r,'restricted converse mismatch: '+fragment)
for fragment in ('Function.update v 11 (v 11+v 5)', 'add_pos (hv 11) (hv 5)',
                 'theorem exists_direct_of_xq91 (p : Fin 4 → ℕ)',
                 '(zero_iff p v).mpr hz'):
    need(fragment in f,'forward map mismatch: '+fragment)

accepted=json.loads((E/'terminal.json').read_text())
restricted0=json.loads((R0/'terminal.json').read_text())
restricted=json.loads((R/'terminal.json').read_text())
forward=json.loads((F/'terminal.json').read_text())
gap=json.loads((G/'terminal.json').read_text())
for folder,receipt,src in ((E,accepted,'DirectMainEquivalence.lean'),(R,restricted,'DirectMainRestricted.lean'),(F,forward,'DirectMainForward.lean'),(G,gap,'DirectMainGap.lean')):
    need(receipt['exit']==0 and receipt['reason'] is None and receipt['union_unchanged'] and receipt['union_count']==1291,'author receipt failed')
    need(sha(folder/'source.txt')==receipt['source_sha256']==receipt['source_after']==sha(P/src),'source mismatch: '+src)
    need(sha(folder/'stdout')==receipt['stdout_sha256'] and sha(folder/'stderr')==receipt['stderr_sha256'] and not (folder/'stderr').read_bytes(),'log mismatch: '+src)
    out=Path(receipt['output_root'])/(src.replace('.lean','.olean'))
    need(sha(out)==receipt['object_sha256'],'producer output mismatch: '+src)
need(restricted0['exit']!=0 and 'error:' in (R0/'stdout').read_text(),'restricted failure not preserved')
need(sha(R0/'source.txt')==restricted0['source_sha256'] and sha(R0/'stdout')==restricted0['stdout_sha256'] and sha(R0/'stderr')==restricted0['stderr_sha256'],'restricted failed snapshot mismatch')
expected="'DirectMainEquivalence.positive_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
need((E/'stdout').read_text()==expected,'unexpected accepted axiom report')
need(accepted['source_sha256']==sha(P/'DirectMainEquivalence.lean') and
     accepted['runner_sha256']==accepted['runner_after']==sha(P/'run-equivalence.py') and
     accepted['lean_sha256']==accepted['lean_after']==sha(accepted['command'][0]),'accepted input changed')
need(sha(Path(accepted['output_root'])/'DirectMainEquivalence.olean')==
     accepted['object_sha256']=='167b9617d2df21aedf9be5403d8e64b0a072747b929a282b22b480f2558d0c4f','accepted object mismatch')

paths=[Path(x) for x in accepted['lean_path'].split(':')]
for key,module,receipt in (('gap','DirectMainGap',gap),('restricted','DirectMainRestricted',restricted),('forward','DirectMainForward',forward)):
    candidates=[root/(module+'.olean') for root in paths if (root/(module+'.olean')).is_file()]
    need(candidates and sha(candidates[0])==accepted[key+'_producer_sha256']==receipt['object_sha256'],'first-resolved object mismatch: '+module)
    need(candidates[0]==Path(receipt['output_root'])/(module+'.olean'),'first-resolved path mismatch: '+module)
# All preceding gap-producer pins must be unchanged in this join.
for key,value in gap.items():
    if key.endswith('_producer_sha256'):
        need(accepted.get(key)==value,'inherited producer pin mismatch: '+key)
need(sha(accepted['command'][0])==accepted['lean_sha256'] and accepted['base_receipt_sha256']==sha(B),'binary/base mismatch')
base=json.loads(B.read_text());lib=paths[-2]
def verify_union():
    actual={x.relative_to(lib).as_posix():x for x in lib.rglob('*') if x.is_file()}
    need(len(actual)==1291 and set(actual)==set(base['union']),'selected union membership')
    for n,p in actual.items():
        z=base['union'][n]
        need(p.is_symlink() and os.readlink(p)==z['link'] and str(p.resolve(strict=True))==z['resolved'] and sha(p)==z['sha256'],'union mismatch: '+n)
verify_union()
for name in ('ordinary12-direct-main-graph-gap-independent','ordinary12-direct-main-forward-independent'):
    q=subprocess.run([sys.executable,'-I','-S','-B',str(D/'reviews'/name/'check.py')],capture_output=True,timeout=180)
    need(q.returncode==0 and not q.stderr and json.loads(q.stdout)['status']=='PASS','prior review failed: '+name)
verify_union();verify_pins()
need(sha(Path(accepted['output_root'])/'DirectMainEquivalence.olean')==accepted['object_sha256'],'accepted output drift')
print(json.dumps({'status':'PASS','ports':['0<beta','MC<beta','MF<2*beta'],
                  'statement':'positive direct zero iff positive XQ91 zero in every IΣ₁ model',
                  'gap_and_restricted_converse':'PASS','forward_map':'PASS',
                  'producer_objects':21,'selected_union_objects':1291,
                  'preexisting_lean_processes':len(accepted['preflight']['lean']),
                  'maximum_sampled_lean_processes':max(len(x['lean']) for x in accepted['samples']),
                  'scope':'model equivalence only; no fixed-port halt or iPRA theorem'},indent=2))
