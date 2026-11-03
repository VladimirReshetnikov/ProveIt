#!/usr/bin/env python3
"""Audit exact retained inferred full-coefficient iPRA types; no Lean replay."""
from pathlib import Path
from hashlib import sha256
import json,re
D=Path(__file__).resolve().parents[2];R=D/'research';P=R/'ten-positive-80-bfs-displayed-full-ipra';S=P/'BFSDisplayedFullIPRA.lean';O=P/'observations/attempt01';t=json.loads((O/'terminal.json').read_text())
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
assert sha(O/'terminal.json')=='bd210ff5388f1353c65821031bde96e55a42ed20dac592ad42fe5a5943092ece' and t['status']=='PASS' and t['exit']==0 and t['reason'] is None
assert sha(S)==t['source_sha256']=='3b1c8abd65d3307af067a8f0e5f72c773f1b84673dad6e1882d368639aa21da8' and sha(P/'run.py')==t['runner_sha256'] and sha(t['output'])==t['output_sha256']=='74ec93c2bf96e2dbab51c271943c9c4e50502b5ab6440f8b7b23e0aa71406f85'
for path,z in t['pins'].items():assert sha(path)==z['sha256'] and str(Path(path).resolve())==z['resolved'],path
assert sha(O/'stdout')==t['stdout_sha256']=='a84fb24c0f02fe93d98d22d5632a0e2b146220675dfe13a1262fe6c3ef48e1ad' and sha(O/'stderr')==t['stderr_sha256'] and not (O/'stderr').read_text()
s=S.read_text();assert re.findall(r'^import\s+(\S+)',s,re.M)==['BFSDisplayedLowInferredV4','BFSDisplayedHighIPRA'] and not re.search(r'\b(?:sorry|admit)\b',s)
names=['standard_consistency','standard_translated_consistency','reference_consistency','reference_translated_consistency'];assert re.findall(r'set_option linter\.defProp false in\s+def\s+(\w+)',s)==['ports_eq']+names and s.count('linter.defProp')==5
assert 'congrArg\n  (fun lo => ports BFSDisplayedBetaIPRA.displayedBeta (BFSDisplayedSlots.displayedKernel rho) lo (BFSHighSymbolic.displayedHigh rho))\n  BFSDisplayedLowInferred.low_formula' in s
for n in names:
 b=s.split('def '+n+' :=',1)[1].split('\nset_option ',1)[0].split('\n#check ',1)[0];assert 'Eq.mp (congrArg (fun p =>' in b and 'positiveShift (graph (integerPorts p)).output' in b and 'ports_eq) BFSDisplayedHighIPRA.'+n in b
log=(O/'stdout').read_text();assert not re.search(r'(?i)\b(?:error|warning)(?:\([^:\n]*\))?:|\bsorryAx\b',log)
low='((2 ^ 67) ^ 8807 - 1 - ∑ j ∈ CompactConcreteMask.support, (2 ^ 67) ^ j - 2 * (2 ^ 67) ^ 1063)'
for i,n in enumerate(names):
 head='BFSDisplayedFullIPRA.'+n+' :';assert log.count(head)==1;start=log.index(head);end=log.index('BFSDisplayedFullIPRA.'+names[i+1]+' :',start) if i+1<len(names) else log.index("'BFSDisplayedFullIPRA.",start);block=log[start:end]
 for frag in ['positiveShift','nativeNoZero','integerPorts','ports BFSDisplayedBetaIPRA.displayedBeta (BFSDisplayedSlots.displayedKernel rho)',low,'BFSHighSymbolic.displayedHigh rho','🡘']:assert frag in block,(n,frag)
 assert ('standardTheory ⊢' if n.startswith('standard') else 'referenceTheory ⊢') in block and (('erase' in block)==n.startswith('reference'))
 assert ('mappedNativeRefutation embedding' if 'translated' not in n else 'sourceSentence') in block
 ax=f"'BFSDisplayedFullIPRA.{n}' depends on axioms: [propext, Classical.choice, Quot.sound]";assert log.count(ax)==1
roots=[Path('/tmp/bfs-low-inferred-ys8rrjp6'),Path('/tmp/bfs-printed-high-9cpcolrs'),Path('/tmp/bfs-printed-beta-sjarp8v0'),Path('/tmp/bfs-high-symbolic-85ibqx1z'),Path('/tmp/bfs-high-flat-ygaljyep'),Path('/tmp/bfs-high-runs-95e4auty'),Path('/tmp/bfs-high-generic-nsp2g8fz'),Path('/tmp/bfs-printed-ipra-9m_nfq32'),Path('/tmp/bfs-printed-slots-qwdduxw9'),Path('/tmp/bfs-printed-kernel-orsko0l9'),Path('/tmp/bfs-printed-selectors-4w6qxofm'),Path('/tmp/direct-bfs-80-coherent-8gret5ed/lib'),Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')]
for n in ['BFSDisplayedLowInferredV4','BFSDisplayedHighIPRA']:
 q=next((r/(n+'.olean') for r in roots if (r/(n+'.olean')).is_file()),None);assert q and str(q) in t['pins'] and sha(q)==t['pins'][str(q)]['sha256'];print('direct',n,q,sha(q))
print('PASS retained #check confirms 4 no-premise standard/reference proof term types: same shifted graph, displayed beta/kernel/low/high, exact natural subtraction; five local defProp suppressions')
print('External PDF/TeX/JSON/payload binding and complete new-client historical/source/package/dynamic closure remain unauthenticated; no Lean replay')
