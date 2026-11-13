#!/usr/bin/env python3
import hashlib,json,os,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize: raise SystemExit('requires python3 -I -S -B')
D=Path(__file__).resolve().parents[2]; P=D/'research/normalized106-rational66-actual'; O=P/'observations/attempt02';PRE=D/'research/normalized106-rational66-specialization'
def H(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(v,s):
 if not v: raise RuntimeError(s)
pins={'Normalized106RationalActual.lean':'3a423c71cd37c7129b262042c512a8523f84b3a892ba4459564d5831681e48ae','check02.py':'f8b0ffa2457f0ee3910f36eabb90bbebe64621f73f22c56dc3c3c78391edacd5','observations/attempt02/result.json':'3b70da32f03ab55d9e52d01106e95a087f513869f33296cb78c558fc6f118394','observations/attempt02/outer-terminal.json':'409516fd5ffa06cca004f9ca367cc45e5ce6875c35f4d159dc64cb0f37a836d1'}
for f,h in pins.items():need(H(P/f)==h,'pin '+f)
r=json.loads((O/'result.json').read_text());t=json.loads((O/'outer-terminal.json').read_text());need(r['status']=='PASS' and r['exit']==0 and r['stop_reason'] is None and r['guards_stable'] and r['guards_before']==r['guards_after'],'result');need(t['session_id']==73833 and t['terminal_exit_code']==0 and t['returned_session_id'] is None,'outer exit')
for name,meta in r['guards_after'].items():
 p=Path(name.removeprefix('producer:'))
 if meta is None: need(not os.path.lexists(p),'unexpected '+name)
 else:
  target=meta.get('realpath',meta.get('resolved'));need(p.is_file() and str(p.resolve())==target and H(p)==meta['sha256'],'guard '+name)
  if 'link' in meta:need((os.readlink(p) if p.is_symlink() else None)==meta['link'],'link '+name)
need(H(O/'compile.log')==r['log_sha256']=='cff2bb678953a4e2b0698006662f0dd2baf81a92368b87f9f26c786cb6753877','log');l=(O/'compile.log').read_text();need(l.count('depends on axioms:')==2 and l.count('Classical.choice')==2 and l.count('Quot.sound')==2 and l.count('propext')==2 and not any(x in l for x in ['sorryAx','warning:','error:']),'axioms')
obj=Path('/tmp/normalized106-rational66-actual-priority-check02/Normalized106RationalActual.olean');need(H(obj)==r['object_sha256']=='64287a9ab9685809828186004896973e5c46e252391fadc992aaaf8cc761ae7c','object')
prior=json.loads((PRE/'observations/attempt01/result.json').read_text());need(H(PRE/'observations/attempt01/result.json')=='c3aac61e3de7684d63cac156e9b784cefa16dda0835dfd0775282d67ed612124' and prior['exit']==0,'prior receipt')
prior_obj=Path('/tmp/normalized106-rational66-specialization-priority-check01/Normalized106RationalSpecialization.olean');need(H(prior_obj)==prior['object_sha256']=='3efc847b71b735789230892c2929879672a2f4042acae0daab4b88c8aa3cff07','prior object')
need(any(k.endswith('/Normalized106RationalSpecialization.olean') and v and v['sha256']==H(prior_obj) for k,v in r['guards_after'].items()),'prior object direct guard')
need(any(k.endswith('/CurrentKernelData2011.olean') and v and v['sha256']=='932f7951a955a29106d40b5e2b94feeb34c612164e3e606970dc0933a142a455' for k,v in r['guards_after'].items()),'actual fixed-port object guard')
need(not any(k.endswith('/ModelCarrierSyntax.olean') for k in r['guards_after']),'unexpected stage078 output guard')
snapshot=Path('/tmp/ha87-full-transitive-p3xt6wra/source-snapshots/DiophantineConsistency_CurrentKernelData2011.lean');need(H(snapshot)=='529b2f89e4e93516a8a52343d98dc749c57f5a967d8ef522b92373bf3adf0a2c','actual port source')
need('def ports : Fin 4 → ℤ := CurrentMasks2011.ports (K : ℤ)' in snapshot.read_text(),'port tuple source identity')
maskpath=Path('/tmp/ha87-full-transitive-p3xt6wra/source-snapshots/DiophantineConsistency_CurrentMaskData2011.lean'); statepath=Path('/tmp/ha87-full-transitive-p3xt6wra/state.json');need(H(statepath)=='84c3bc6f6c34c47e67278c43df8580444d32e2946844a4c40c31cfd747f33a90','port producer state'); state=json.loads(statepath.read_text()); rec={x['module']:x for x in state['records']}; kr=rec['DiophantineConsistency.CurrentKernelData2011']; mr=rec['DiophantineConsistency.CurrentMaskData2011'];need(kr['exit']==0 and kr['source_sha256']==H(snapshot) and kr['object_sha256']=='932f7951a955a29106d40b5e2b94feeb34c612164e3e606970dc0933a142a455' and mr['exit']==0 and mr['source_sha256']==H(maskpath) and mr['object_sha256']==kr['dependency_hashes']['DiophantineConsistency.CurrentMaskData2011'],'port producer linkage'); mask=maskpath.read_text();need('def radix : ℕ := 2 ^ 47' in mask and 'def beta : ℕ := radix ^ 2011 - 1' in mask and 'def ports (K : ℤ) : Fin 4 → ℤ := ![beta, K, lowPort, highPort + beta]' in mask,'beta and tuple source')

print(json.dumps({'status':'PASS_READ_ONLY_INDEPENDENT_REVIEW','direct_guards':len(r['guards_after']),'outer_session':73833,'outer_exit':0,'lean_child_exit':0,'scope':'Historical fixed-port provider and preceding rational specialization object; no Lean replay or new transitive ancestry.'},sort_keys=True,indent=2))
