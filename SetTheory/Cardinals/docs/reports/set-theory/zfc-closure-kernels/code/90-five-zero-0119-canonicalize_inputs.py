import json
from pathlib import Path
from functools import lru_cache
import argparse
p=argparse.ArgumentParser(description='Regenerate the exact 30-token semantic dictionary and search inputs.')
p.add_argument('--reference',type=Path,default=Path(__file__).resolve().parent/'reference_data')
p.add_argument('--output',type=Path,required=True)
a=p.parse_args();B=a.reference;P=a.output;P.mkdir(parents=True,exist_ok=True)
s=json.loads((B/'reference/grammar/closed-sequence-grammar-next22.json').read_text());symbols=json.loads((B/'reference/grammar/semantic-symbols.json').read_text());ast=s['ast_dag']
@lru_cache(None)
def bounds(i):
 r=ast[i]
 if r[0]=='L':
  op,*arg=r[1]
  return (1,0) if op=='dec' else (arg[0],0) if op=='brk' else (0,arg[0]) if op=='cont' else (0,0)
 a,b=bounds(r[1]),bounds(r[2]);return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)
@lru_cache(None)
def finest(i):
 r=ast[i]
 return finest(r[1])+finest(r[2]) if r[0]=='N' and bounds(r[1])==bounds(r[2])==(0,0) else (i,)
fine={c:finest(s['atoms'][name]['ast'])for c,name in symbols.items()}
alphabet=sorted({x for v in fine.values()for x in v});codes={x:'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'[i]for i,x in enumerate(alphabet)}
enc={c:''.join(codes[x]for x in v)for c,v in fine.items()}
def encode(w):return ''.join(enc[c]for c in w)
lines=(B/'inputs/state_reduction/route-grammar.txt').read_text().splitlines();n,nr,na=map(int,lines[0].split());out=[lines[0]]
for row in lines[1:n+1]:
 k,w,q=row.split();out.append(f'{len(encode(w[:int(k)]))} {encode(w)} {q}')
out += [encode(w)for w in lines[n+1:n+1+nr]]
out += [f'{enc[c]} {m}'for c,m in map(str.split,lines[n+1+nr:])]
(P/'canonical-grammar.txt').write_text('\n'.join(out)+'\n')
lines=(B/'inputs/state_reduction/route-constraints.txt').read_text().splitlines();ng=int(lines[0]);out=[lines[0]];i=1
for _ in range(ng):
 src,read,rt,nc=lines[i].split();i+=1;out.append(f'{src} {read} {encode(rt)} {nc}')
 for _ in range(int(nc)):
  pre,w=lines[i].split();i+=1;out.append(f'{pre} {encode(w)}')
ne,original,natoms=map(int,lines[i].split());out.append(lines[i]);i+=1
for _ in range(ne):
 row=lines[i].split();i+=1
 out.append('W '+encode(row[1]) if row[0]=='W'else ' '.join(row))
for _ in range(natoms):
 c,e=lines[i].split();i+=1;out.append(enc[c]+' '+e)
assert i==len(lines)
(P/'canonical-constraints.txt').write_text('\n'.join(out)+'\n')
lines=(B/'inputs/state_reduction/bootstrap-lock54.txt').read_text().splitlines();out=[lines[0]]
for w,bit,t in map(str.split,lines[1:]):out.append(f'{encode(w)} {bit} {encode(t)}')
(P/'canonical-lock54.txt').write_text('\n'.join(out)+'\n')
d=json.loads((B/'grammar.json').read_text())
(P/'canonical-resume.txt').write_text(str(len(d['rules']))+'\n'+'\n'.join(f'{len(encode(l))} {encode(w)}'for w,l,r in d['rules'])+'\n'+str(len(d['routes']))+'\n'+'\n'.join(encode(r['word'])for r in d['routes'])+'\n')
(P/'canonical-map.json').write_text(json.dumps(dict(physical_atoms=enc,fine_ast_ids={v:k for k,v in codes.items()},fine_expansions=fine),indent=2)+'\n')
print('fine tokens',len(alphabet),'terminals',len(enc),'distinct',len(set(enc.values())))
