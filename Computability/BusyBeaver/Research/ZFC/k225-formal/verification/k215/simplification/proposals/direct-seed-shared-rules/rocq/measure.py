#!/usr/bin/env python3
"""Bind the input snapshots, measure the complete refactor, and emit source diffs."""
from pathlib import Path
import difflib, hashlib, json, re

ROOT=Path(__file__).resolve().parent
P='6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95'
J='c132d7eae8158cd3a9850ea3eb7251158c3dd821'
K='3142e4dd980f0be12f4abb636c4ae2528afc17eb'
PREFIX='Computability/BusyBeaver/Research/ZFC/k225-formal/'
inputs=[]
for local in sorted((ROOT/'upstream').rglob('*.v')):
    rel=local.relative_to(ROOT/'upstream')
    if rel.parts[0]=='ZF':
        repo,owner,commit='busy-beaver','jeff87654',J
        path='ZF/stdzf/coq/'+rel.name
        norm='none'
    elif rel.parts[0]=='K230S':
        repo,owner,commit='k230-rocq','elliotglazer',K
        path='coq/settheory/'+rel.name
        norm='CRLF to LF'
    else:
        repo,owner,commit='ProveIt','VladimirReshetnikov',P
        path=PREFIX+'rocq/rocq-extension/coq/215/'+rel.name
        norm='none'
    raw=local.read_bytes()
    inputs.append(dict(repository=repo,owner=owner,commit=commit,source_path=path,
        packet_path=str(local.relative_to(ROOT)),normalization=norm,
        sha256=hashlib.sha256(raw).hexdigest(),
        source_url=f'https://github.com/{owner}/{repo}/blob/{commit}/{path}'))
(ROOT/'evidence/source_manifest.json').write_text(json.dumps(dict(inputs=inputs),indent=2)+'\n')

def stats(p):
    raw=(ROOT/p).read_bytes()
    return dict(path=p,lines=len(raw.splitlines()),bytes=len(raw),
                sha256=hashlib.sha256(raw).hexdigest())
before=[stats('upstream/ZF/L1_LProp.v'),stats('upstream/K215F/L224Prop.v')]
after=[stats('proof/PropositionalCore.v'),stats('proof/L1_LProp.v'),stats('proof/L224Prop.v')]
std=(ROOT/'upstream/ZF/L1_LProp.v').read_text()
restricted=(ROOT/'upstream/K215F/L224Prop.v').read_text()
restricted=re.sub(r'\bm(llp\d+|lpc_\w+)\b',r'\1',restricted)
for a,b in [('lprov224','lprov'),('MDET','LDET'),('MB1','LB1'),('MB2','LB2'),('MB3','LB3')]:
    restricted=re.sub(r'\b'+a+r'\b',b,restricted)
same=(std[std.index('Lemma llp5'):].strip()==restricted[restricted.index('Lemma llp5'):].strip())
assert same
metrics=dict(before=before,after=after,
    before_total={k:sum(x[k] for x in before) for k in ('lines','bytes')},
    after_total={k:sum(x[k] for x in after) for k in ('lines','bytes')},
    derivation_count_each=len(re.findall(r'^Lemma ',std,re.M)),
    intermediate_derivations=len(re.findall(r'^Lemma llp',std,re.M)),
    public_derivations=len(re.findall(r'^Lemma lpc_',std,re.M)),
    exact_duplicate_proofs_after_renaming=same,
    api_examples=len(re.findall(r'^Example ',(ROOT/'proof/PropositionalAPIAudit.v').read_text(),re.M)),
    source_counts_not_term_sizes=True,full_endpoint_not_checked=True)
(ROOT/'evidence/metrics.json').write_text(json.dumps(metrics,indent=2)+'\n')

def diff(old,new,path):
    a=(ROOT/old).read_text().splitlines(keepends=True) if old else []
    b=(ROOT/new).read_text().splitlines(keepends=True)
    return ''.join(difflib.unified_diff(a,b,fromfile='a/'+path if old else '/dev/null',tofile='b/'+path))
common=PREFIX+'rocq/common/PropositionalCore.v'
production=diff(None,'proof/PropositionalCore.v',common)
production+=diff('upstream/K215F/L224Prop.v','proof/L224Prop.v',
                 PREFIX+'rocq/rocq-extension/coq/215/L224Prop.v')
(ROOT/'patches/proveit-sources.patch').write_text(production)
(ROOT/'patches/jeff-reference-facade.patch').write_text(
    diff('upstream/ZF/L1_LProp.v','proof/L1_LProp.v','ZF/stdzf/coq/L1_LProp.v'))
print(json.dumps({k:v for k,v in metrics.items() if k not in ('before','after')},indent=2))
