#!/usr/bin/env python3
import hashlib,json,re
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-zero-bridge-check';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'9b03c17fc52f1dfd8794efb70756cebe3ae445cc241f6f88f98cc5ca57659051','source-manifest.json':'33900f362c0e5ce783b300a655ef92ab1b523553a05a8efd2a0564d216443354','first-cut-survey.py':'ed8dd43c24b91864f6c09dbe14a58fc98dc4f693e71476a0dc71bae788ff7985'}.items():assert sha(P/n)==h
m=json.loads((P/'source-manifest.json').read_text())['rows'];names=['Sign31CoordinateRecover','Sign31CoordinateDrop','Sign31ForwardBridge','Sign31ReverseBridge'];src=[]
assert [r['module'].split('.')[-1] for r in m]==names
for r,n in zip(m,names):
 p=P/'src/DiophantineConsistency'/f'{n}.lean';s=p.read_text();src.append(s);assert sha(p)==r['source_sha256'];assert [x[7:] for x in s.splitlines() if x.startswith('import ')]==r['imports']
a,b,c,d=src;assert 'v 27 = (v 5 + 1) ^ 2' in a and 'SharingSign32Squares.seed_zero_iff_residuals p v' in a and 'apply ι_injective' in a and 'sub_eq_zero.mp he' in a
assert 'Sign31FirstCut.lift (drop v) = v' in b and 'f2_coordinate p v hz' in b
lift=[x.strip() for x in re.search(r'def drop\b[^\n]*\n\s*!\[(.*?)\]',b,re.S).group(1).split(',')];assert lift==[f'v {i}' for i in range(27)]+[f'v {i}' for i in range(28,33)]
remaining=['X','Y','E','kY','ell','Delta','mainRoot','c2','Dc2','N1','gap','tau','N0','Nt','cTminusR','V','normalizedS','normalizedS2','V2minusY2','Na','scaledNs'];old=['q3']+remaining[:14]+['f2']+remaining[14:];new=['q3']+remaining;assert len(old)==23 and len(new)==22
for s,seq,direction in [(c,old,'forward'),(d,new,'backward')]:
 branches=[x for x in s.splitlines() if x.strip().startswith('· exact ')];assert len(branches)==len(seq)
 for term,line in zip(seq,branches):
  if term=='f2':assert 'Sign31FirstCut.old_f2_zero p v' in line;continue
  owner='Sign31FirstCut' if term in ('V','scaledNs') else 'Sign31RemainingCuts';assert owner+'.'+term+'_eval' in line
  if term!='q3':assert owner+'.'+('new' if direction=='forward' else 'old')+'_'+term+'_row' in line
  assert (').mpr' if direction=='forward' else ').mp') in line
assert 'InternalZero (SharingSeed32Sextic.seed p) (Sign31FirstCut.lift v)' in c and 'InternalZero (SharingSeed31Sextic.seed p) (Sign31CoordinateRecover.drop v)' in d
print(json.dumps({'status':'PASS_STATIC','scope':'four proposed coordinate-recovery/forward/reverse modules, all branches/source mappings checked; no Lean proof yet'}))
