#!/usr/bin/env python3
"""Prepare ordinary, finest-word, and trace-word discovery inputs portably."""
from pathlib import Path
import argparse,json,shutil
from fine_semantic_domain import Domain,trace_normal

p=argparse.ArgumentParser();p.add_argument('--package',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args()
assert __debug__
d=Domain(a.package);s=d.source;ex=d.expand;out=a.output;out.mkdir(parents=True,exist_ok=True)
for name in ['route-grammar.txt','route-constraints.txt','bootstrap-lock54.txt']:
 shutil.copyfile(a.package/'inputs/state_reduction'/name,out/name)
shutil.copyfile(a.package/'grammar.json',out/'grammar245.json')
g=json.loads((out/'grammar245.json').read_text())
(out/'fine_encoding.json').write_text(json.dumps(dict(atom_expansions=d.expansions,fine_tokens=d.token_encoding,semantic_symbols=d.fine_symbols),indent=2)+'\n')
lines=(out/'route-grammar.txt').read_text().splitlines();n,nr,na=map(int,lines[0].split());fine=[lines[0]];trace=[lines[0]]
for row in lines[1:n+1]:
 k,w,q=row.split();left,right=w[:int(k)],w[int(k):];fine.append(f'{len(ex(left))} {ex(w)} {q}');trace.append(f'{ex(w)} {ex(left)} {ex(right)}')
tail=[ex(w)for w in lines[n+1:n+nr+1]]
for row in lines[n+nr+1:]:
 if row.strip():c,k=row.split();tail.append(f'{d.expansions[c]} {k}')
(out/'fine-route-grammar.txt').write_text('\n'.join(fine+tail)+'\n');(out/'trace-grammar.txt').write_text('\n'.join(trace+tail)+'\n')
lines=(out/'route-constraints.txt').read_text().splitlines();i=1;ng=int(lines[0]);res=[lines[0]]
for _ in range(ng):
 src,bit,w,nc=lines[i].split();i+=1;res.append(f'{src} {bit} {ex(w)} {nc}')
 for _ in range(int(nc)):
  bits,t=lines[i].split();i+=1;res.append(f'{bits} {ex(t)}')
ne,oe,natoms=map(int,lines[i].split());res.append(lines[i]);i+=1
for _ in range(ne):
 row=lines[i].split();i+=1
 if row[0]=='W':row[1]=ex(row[1])
 res.append(' '.join(row))
for _ in range(natoms):c,e=lines[i].split();i+=1;res.append(f'{d.expansions[c]} {e}')
assert not any(row.strip()for row in lines[i:]);(out/'fine-route-constraints.txt').write_text('\n'.join(res)+'\n')
lines=(out/'bootstrap-lock54.txt').read_text().splitlines();res=[lines[0]]
for row in lines[1:]:
 if row.strip():w,b,t=row.split();res.append(f'{ex(w)} {b} {ex(t)}')
(out/'fine-bootstrap-lock54.txt').write_text('\n'.join(res)+'\n')
for name,transform in [('seed245.txt',lambda w,a,b:f'{len(a)} {w}'),('fine-seed245.txt',lambda w,a,b:f'{len(ex(a))} {ex(w)}'),('trace-seed245.txt',lambda w,a,b:f'{ex(w)} {ex(a)} {ex(b)}')]:
 lines=[str(len(g['rules']))]+[transform(w,a,b)for w,a,b in g['rules']]+[str(len(g['routes']))]+[(r['word']if name=='seed245.txt'else ex(r['word']))for r in g['routes']]
 (out/name).write_text('\n'.join(lines)+'\n')
info={c:d.footprint(i)for c,i in d.token_ast.items()};(out/'trace-info.txt').write_text(str(len(info))+'\n'+'\n'.join(f'{c} {mask} {int(halt)}'for c,(mask,halt)in info.items())+'\n')
classes={}
for w in [ex(w)for w,_,_ in g['rules']]+list(d.expansions.values()):
 classes.setdefault(trace_normal(w,d.disjoint_pairs),[]).append(w)
collisions=[v for v in classes.values()if len(v)>1]
(out/'trace_collisions.json').write_text(json.dumps(dict(token_info=info,classes=len(classes),collisions=collisions),indent=2)+'\n')
# Release both projections of the two nodes involved in the final-loop
# association rotation.  Keeping either ordered child would keep its split.
released={'eijkKCqkjGeU','eijkKCqkjGe'}
locks=[row for row in (out/'bootstrap-lock54.txt').read_text().splitlines()[1:]if row.strip()and row.split()[0]not in released]
assert len(locks)==50
(out/'bootstrap-lock50.txt').write_text('50\n'+'\n'.join(locks)+'\n')
(out/'no-locks.txt').write_text('0\n')
rotated=[(w,a,b)for w,a,b in g['rules']if w!='eijkKCqkjGe']
rotated=[(w,'eijkKCqkjG','eU')if w=='eijkKCqkjGeU'else(w,a,b)for w,a,b in rotated]+[('eU','e','U')]
assert len(rotated)==128 and all(w==a+b for w,a,b in rotated)
lines=[str(len(rotated))]+[f'{len(a)} {w}'for w,a,b in rotated]+[str(len(g['routes']))]+[r['word']for r in g['routes']]
(out/'seed245-rotated-lastloop.txt').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(status='PASS',fixed_atoms=44,finest_atoms=30,AX_fine_length=len(ex(max((w for w,_,_ in g['rules']),key=len)))),indent=2))
