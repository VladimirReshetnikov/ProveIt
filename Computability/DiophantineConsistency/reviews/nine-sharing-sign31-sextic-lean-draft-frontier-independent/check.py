#!/usr/bin/env python3
import hashlib,json,re,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign31-sextic-lean-draft';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'SharingSeed31Sextic.lean':'52e887de8cc5197d0c7ad8543f9e1b3f51f42a20302475b83df342693d8469c1','SharingSeed31BridgeDraft.lean':'0e3bbc84ee88879183619bbe283321f651621345a9c4deab3febe903aaa21ad3','generate.py':'e2ee0a6e2a39fcbe05e7c53636c7a158122b5023fc4842d2f730074ad6586e07','check.py':'8c3a2e78bde876b92479924c3bd984854b8d75b9d62e8840ac51bdd907576b46','check_bridge.py':'9b59ea4fe0e5457f08e46f5a486b4b16c6a13d3131116d65cf758b7a81bf2bd5'}.items():assert sha(P/n)==h
s=(P/'SharingSeed31BridgeDraft.lean').read_text();assert 'import DiophantineConsistency.SharingSeed31Sextic' in s and 'import DiophantineConsistency.SharingSeed32Sextic' in s
for name,n in [('lift',33),('drop',32)]:
 a=re.search(r'def '+name+r'\b[^\n]*\n\s*!\[(.*?)\]',s,re.S);assert a;vals=[x.strip() for x in a.group(1).split(',')];assert len(vals)==n
 if name=='lift':assert vals==[f'v {i}' for i in range(27)]+['(v 5 + 1) ^ 2']+[f'v {i}' for i in range(27,32)]
 else:assert vals==[f'v {i}' for i in range(27)]+[f'v {i}' for i in range(28,33)]
assert len(re.findall(r'^def (?:ForwardTarget|BackwardTarget)\b',s,re.M))==2 and not re.search(r'^(?:theorem|lemma)\b',s,re.M) and not re.search(r'\b(?:sorry|admit)\b',s)
assert re.search(r'def ForwardTarget.*?∀ v : Fin 32 → V, InternalZero \(SharingSeed31Sextic.seed p\) v →\s*InternalZero \(SharingSeed32Sextic.seed p\) \(lift v\)',s,re.S)
assert re.search(r'def BackwardTarget.*?∀ v : Fin 33 → V, InternalZero \(SharingSeed32Sextic.seed p\) v →\s*InternalZero \(SharingSeed31Sextic.seed p\) \(drop v\)',s,re.S)
x=subprocess.run([sys.executable,'-I','-S','-B',str(P/'check.py')],check=True,capture_output=True,timeout=30);assert not x.stderr and x.stdout==(P/'result.json').read_bytes()
r=json.loads(x.stdout);assert r['residuals']==22 and r['max_residual_syntactic_degree']==3 and r['coordinate_zero_unused'] and r['coordinate_indices']==list(range(1,32))
print(json.dumps({'status':'PASS_SOURCE_ONLY','scope':'all 22 ASTs via pinned source parser, exact 33/32 coordinate maps and two open targets; no Lean parsing, proof or endpoint'},indent=2,sort_keys=True))
