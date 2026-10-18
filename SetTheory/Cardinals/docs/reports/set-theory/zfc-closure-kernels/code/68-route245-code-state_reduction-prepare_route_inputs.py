#!/usr/bin/env python3
"""Prepare the routing-aware search input from pinned grammar metadata."""
import argparse,json
from pathlib import Path
P=argparse.ArgumentParser();P.add_argument('--inputs',type=Path,required=True);P.add_argument('--output-dir',type=Path,required=True);P.add_argument('--bootstrap-lock',type=Path);a=P.parse_args();a.output_dir.mkdir(parents=True,exist_ok=True)
s=json.loads((a.inputs/'closed-sequence-grammar-next22.json').read_text());enc={v:k for k,v in json.loads((a.inputs/'semantic-symbols.json').read_text()).items()};lines=(a.inputs/'semantic.txt').read_text().splitlines();n,nr,na=map(int,lines[0].split());names={int(q):w for k,w,q in map(str.split,lines[1:n+1])};released={24,89,107,152,154,175,188,207,213,245};roots=[names[q]for q in s['required_entry_roots']if q not in released];router=names[175]+names[207]
new=[f'{n+1} {len(roots)} {na}']+lines[1:n+1]+[f'{len(names[175])} {router} 177']+roots+lines[n+1+nr:]
(a.output_dir/'route-grammar.txt').write_text('\n'.join(new)+'\n')
groups={}
for c in s['left_entry_projection_constraints']:
 r=c['reason'];key=(r['source'],r['read']);prefix=c['prefix'];root=names[c['root']]
 if r.get('via')==177:prefix=str(r['previous'])+prefix;root=router
 groups.setdefault(key,{'root':root,'cs':[]})['cs'].append((prefix,''.join(enc[t]for t in c['word'])))
props=(a.inputs/'semantic-constraints22.txt').read_text().splitlines()[23:];out=[str(len(groups))]
for(src,read),g in groups.items():
 out.append(f"{src} {read} {g['root']} {len(g['cs'])}");out.extend(f'{prefix} {target}'for prefix,target in g['cs'])
out+=props;(a.output_dir/'route-constraints.txt').write_text('\n'.join(out)+'\n')
if a.bootstrap_lock:
 d=json.loads(a.bootstrap_lock.read_text());cs=d['block_aware_constraints'];assert len(cs)==54
 (a.output_dir/'bootstrap-lock54.txt').write_text(str(len(cs))+'\n'+'\n'.join(f"{c['word']} {c['bit']} {c['target_word']}"for c in cs)+'\n')
print(json.dumps(dict(grammar_rules=n+1,mandatory_roots=len(roots),route_groups=len(groups),released_old_roots=sorted(released)),indent=2))
