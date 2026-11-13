#!/usr/bin/env python3
"""Independently check source selection, prior ancestry and header graph; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
from collections import Counter
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2];ROOT=D.parents[1]
new=D/'research/ordinary14-natural79-beta-only-overlay';old=D/'research/ordinary14-natural79-corrected-reflection-overlay';older=D/'research/ordinary14-natural79-combined-slim-overlay';prior80=D/'research/ordinary14-natural80-combined-slim-overlay';alt=D/'research/ordinary14-natural79-beta-only-zero-w-draft/source'
def sha(b):return hashlib.sha256(b).hexdigest()
def pin(p,h):
 b=p.read_bytes();assert sha(b)==h,(p,sha(b));return b
N=json.loads(pin(new/'inventory.json','62a171aeb4ba22745d0750e6dc4ec2310c43e294f35a4a25a9dfccfafbafa503'))
O=json.loads(pin(old/'inventory.json','fc9da87f4178c7f3b06c549a792f7e80baac2217a6735bcb38e49b280a90d434'))
P=json.loads(pin(older/'inventory.json','7f8f722c1a96194dc453a797a2ffafbcfea614b2c8c83fda9a51daefb0558483'))
Q=json.loads(pin(prior80/'inventory.json','bd10f4c2b320ce1255f57f5bf1e9aefc346d2b2a2b5a8b989547f78f060c2be7'))
author=json.loads(pin(D/'research/ordinary14-natural79-beta-only-zero-w-draft/receipt.json','5331a284de1853e0314c9346c7cc922701a64c99a7328f15b66cbfb7827cba24'))
review=json.loads(pin(D/'reviews/ordinary14-natural79-beta-only-zero-w-independent/result.json','a82524b1c97d283766f477228eab6108f12439b95f99efbdf68a422791b6e324'))
by=lambda i:{r['module']:r for r in i['drafts_topological']}
newrows=by(N);oldrows=by(O);olderrows=by(P);rows80=by(Q)
assert len(newrows)==len(N['drafts_topological'])==195 and len(oldrows)==196 and len(olderrows)==195 and len(rows80)==184
assert set(oldrows)-set(newrows)=={'Natural79ZeroWJPos'} and set(newrows)<set(oldrows)
changed={'Natural79Endpoint','Natural79ZeroWMainNorm','Natural79ZeroWRootCut','Natural79ZeroWDivisibility'}
assert changed<=set(newrows) and not (changed & set(rows80))
files=list((new/'source').iterdir());assert len(files)==195 and all(p.is_file() and not p.is_symlink() and p.name.endswith('.lean.src') for p in files)
assert {p.name for p in files}=={n+'.lean.src' for n in newrows}
for n in oldrows:
 previous=pin(old/oldrows[n]['overlay_path'],oldrows[n]['overlay_sha256'])
 assert pin(D/oldrows[n]['selected_path'],oldrows[n]['selected_sha256'])==previous
 if oldrows[n]['original_path'] is not None:pin(D/oldrows[n]['original_path'],oldrows[n]['original_sha256'])
 if n not in newrows:continue
 current=pin(new/newrows[n]['overlay_path'],newrows[n]['overlay_sha256'])
 assert pin(D/newrows[n]['selected_path'],newrows[n]['selected_sha256'])==current
 if n in changed:
  assert current==(alt/(n+'.lean.src')).read_bytes() and sha(current)==author['inert_snapshots'][n+'.lean.src']
  key={'Natural79ZeroWMainNorm':'main','Natural79ZeroWRootCut':'root','Natural79ZeroWDivisibility':'div','Natural79Endpoint':'endpoint'}[n]
  assert review['inputs']['new_'+key]['sha256']==sha(current)
 else:assert current==previous
 if n in rows80:
  eighty=pin(prior80/rows80[n]['overlay_path'],rows80[n]['overlay_sha256'])
  seventy9=pin(older/olderrows[n]['overlay_path'],olderrows[n]['overlay_sha256'])
  assert current==previous==seventy9==eighty
assert Counter(r['kind'] for r in newrows.values())=={'unchanged-corrected-overlay':191,'beta-only-alternative':4}
assert 'NaturalDvdReflectionSlim' in newrows and 'StrictK0Symbolic' in newrows and 'Natural80Endpoint' in newrows
helper=(new/newrows['NaturalDvdReflectionSlim']['overlay_path']).read_text()
assert helper.startswith('import Foundation.FirstOrder.Arithmetic.IOpen.Basic\n')
headers={};qualified=set();order={r['module']:i for i,r in enumerate(N['drafts_topological'])}
for n,r in newrows.items():
 data=(new/r['overlay_path']).read_text();imps=[]
 for line in data.splitlines():
  if not line.strip():continue
  if not line.startswith('import '):break
  assert re.fullmatch(r'import\s+[A-Za-z0-9_.]+(?:\s+[A-Za-z0-9_.]+)*\s*',line),line
  imps+=line.split()[1:]
 bare=[x for x in imps if '.' not in x];qual=[x for x in imps if '.' in x]
 assert bare==r['bare_imports'] and qual==r['qualified_imports']
 assert 'Natural79ZeroWJPos' not in bare and all(x in order and order[x]<order[n] for x in bare)
 headers[n]=bare;qualified.update(qual)
seen=set();todo=['Natural79Endpoint']
while todo:
 n=todo.pop()
 if n in seen:continue
 seen.add(n);todo.extend(headers[n])
assert seen==set(newrows)
project={r['module']:r for r in N['qualified_direct_sources']};external={r['module']:r for r in N['external_direct_sources']}
assert set(project)=={r['module'] for r in O['qualified_direct_sources']} and len(project)==41
assert set(external)=={r['module'] for r in O['external_direct_sources']} and len(external)==3
assert qualified==set(project)|set(external)
for r in project.values():pin(D/r['path'],r['sha256'])
for r in external.values():
 p=Path(r['path']);pin(p if p.is_absolute() else ROOT/p,r['sha256'])
print(json.dumps({'scope':'exact inert source selections and initial import graph, no Lean/provider proof',
 'selected_snapshots':195,'unchanged_corrected':191,'alternatives':4,'removed':'Natural79ZeroWJPos',
 'preserved_natural80_snapshots':184,'corrected_reflection_helper_retained':True,
 'strict_k0_and_natural80_endpoint_retained':True,'qualified_project_sources':41,'external_direct_sources':3,
 'all_reachable_in_dependency_first_order':True,'lean_executed':False},sort_keys=True,indent=2))
