#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign28-zero-bridge-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'a7e7a3072162674d830383692a0ac8817abee0cc77ddd11741dded7c620353c8','source-manifest.json':'ea2b5abba8c57898ffe8ca52198e76fa2e33069124d71514a08cd44336003247','first-cuts-survey.py':'65bf351fcb60496ffa1a0c44ff1f8b9b7831646c2e30cb8e28235d7827ecb126'}.items():assert sha(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['Sign28CoordinateRecover','Sign28CoordinateDrop','Sign28ForwardBridge','Sign28ReverseBridge'];src=[]
assert [r['module'].split('.')[-1] for r in m]==names
for r,n in zip(m,names):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();src.append(s);assert sha(p)==r['source_sha256'];assert [x[7:] for x in s.splitlines() if x.startswith('import ')]==r['imports']
a,b,c,d=src
for expected in ['v 16 = (v 9 + 1) * (beta * (v 1 + 1) + 1)','v 23 = (v 19 + (v 11 + 1)) ^ 2','v 30 = (v 29) ^ 2'] :assert expected in a
assert a.count('SharingSign31Squares.seed_zero_iff_residuals p v')==3 and a.count('apply ι_injective')==3 and a.count('sub_eq_zero.mp he')==3
assert 'Sign28FirstCuts.lift beta (drop v) = v' in b and all(f'{name}_coordinate p' in b for name in ('x','c2','s2'))
indices=[int(x) for x in re.findall(r'v (\d+)',re.search(r'def drop\b[^\n]*\n\s*!\[(.*?)\]',b,re.S).group(1))];assert indices==[i for i in range(32) if i not in (16,23,30)]
old=['q3','X','Y','E','kY','ell','Delta','mainRoot','c2','Dc2','N1','gap','tau','N0','Nt','cTminusR','V','normalizedS','normalizedS2','V2minusY2','Na','scaledNs'];new=[x for x in old if x not in ('X','c2','normalizedS2')];assert len(old)==22 and len(new)==19
for s,seq,direction in [(c,old,'forward'),(d,new,'backward')]:
 branches=[x for x in s.splitlines() if x.strip().startswith('· exact ')];assert len(branches)==len(seq)
 for term,line in zip(seq,branches):
  if term in ('X','c2','normalizedS2'):
   assert 'Sign28FirstCuts.old_'+term+'_zero' in line;continue
  owner='Sign28FirstCuts' if term in ('E','mainRoot','Dc2','Na','scaledNs') else 'Sign28RemainingCuts';assert owner+'.'+term+'_eval' in line
  if term!='q3':assert owner+'.'+('new' if direction=='forward' else 'old')+'_'+term+'_row' in line
  assert (').mpr' if direction=='forward' else ').mp') in line
assert all('(hp0 : ((p 0 : ℤ) : DiffRing V) = ι beta)' in s for s in (a,b,c,d))
assert 'InternalZero (SharingSeed31Sextic.seed p) (Sign28FirstCuts.lift beta v)' in c and 'InternalZero (SharingSeed28Sextic.seed p) (Sign28CoordinateRecover.drop v)' in d
assert 'Sign28CoordinateRecover.lift_drop p beta v hp0 hz' in d
p=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,timeout=120,check=True);assert not p.stderr and json.loads(p.stdout)['status']=='PASS_NO_LEAN_PREFLIGHT'
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','modules':4,'old_rows':22,'new_rows':19,'scope':'proposed same-port zero implications with explicit beta cast; no Lean success or endpoint claim'},sort_keys=True,indent=2))
