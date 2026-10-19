import argparse,json
from pathlib import Path
from functools import cache
p=Path(__file__).resolve().parents[2]
ap=argparse.ArgumentParser();ap.add_argument("--output",type=Path,default=p/"inputs/fine");args=ap.parse_args();outdir=args.output;outdir.mkdir(parents=True,exist_ok=True)
s=json.loads((p/'inputs/closed-sequence-grammar-next22.json').read_text());symbols=json.loads((p/'inputs/semantic-symbols.json').read_text());seed=json.loads((p/'results/state_reduction/candidate-zero6-k128.json').read_text());grammar={w:(l,r)for w,l,r in seed['rules']};ast=s['ast_dag']
lines=(p/'inputs/semantic.txt').read_text().splitlines();nr,nt,na=map(int,lines[0].split());old={w:(w[:int(k)],w[int(k):])for k,w,q in map(str.split,lines[1:nr+1])};names={int(q):w for k,w,q in map(str.split,lines[1:nr+1])};allowed={c:int(m)for c,m in map(str.split,lines[1+nr+nt:])};byast={int(i):names[int(q)]for q,i in s['sequence_ast_roots'].items()}
@cache
def bounds(i):
 row=ast[i]
 if row[0]=='L':
  op,*xs=row[1];return (1,0)if op=='dec' else (xs[0],0)if op=='brk' else (0,xs[0])if op=='cont' else (0,0)
 a,b=bounds(row[1]),bounds(row[2]);return max(a[0]-1,b[0],0),max(a[1],b[1]-1,0)
@cache
def finest(i):
 row=ast[i]
 return finest(row[1])+finest(row[2])if row[0]=='N'and bounds(row[1])==bounds(row[2])==(0,0)else(i,)
fineids=sorted({i for name in symbols.values()for i in finest(s['atoms'][name]['ast'])});encode={i:chr(65+k)for k,i in enumerate(fineids)};atom={c:''.join(encode[i]for i in finest(s['atoms'][name]['ast']))for c,name in symbols.items()}
def expand(w):return ''.join(atom[c]for c in w)
def join(a,b):return a[0]+1,max(a[0]+1,a[1],b[1]),max(a[2],b[2])+1
@cache
def ap(i):
 if i in byast:return wp(byast[i])
 row=ast[i];return(0,0,0)if row[0]=='L'else join(ap(row[1]),ap(row[2]))
@cache
def wp(w):return ap(s['atoms'][symbols[w]]['ast'])if len(w)==1 else join(*(wp(x)for x in grammar.get(w,old.get(w))))
roots=set(seed['roots'])|{r['word']for r in seed['routes']};ax=names[76];locks={l.split()[0]for l in(p/'inputs/state_reduction/bootstrap-lock54.txt').read_text().splitlines()[1:]};fixed=set()
def freeze(w):
 if len(w)==1 or w in fixed:return
 fixed.add(w)
 for child in grammar[w]:freeze(child)
for w in sorted((roots-{ax})|locks):freeze(w)
dictionary={expand(c):dict(spelling=c,mask=allowed[c],properties=wp(c))for c in symbols}
for w in sorted(fixed):
 f=expand(w);assert f not in dictionary;dictionary[f]=dict(spelling=w,mask=3,properties=wp(w))
private={expand(w):(expand(l),expand(r))for w,(l,r)in grammar.items()if w not in fixed};assert len(private)==len(grammar)-len(fixed)
value=dict(seed=seed,atom=atom,fixed={w:grammar[w]for w in sorted(fixed)},dictionary=dictionary,rules=private,ax=expand(ax),ax_word=ax,ax_properties=wp(ax),full_properties=ap(s['original_ast']),fine_ids=fineids)
(outdir/'input.json').write_text(json.dumps(value,indent=2)+'\n')
out=[f'{len(dictionary)} {len(private)} {wp(ax)[0]} {wp(ax)[2]+64-ap(s["original_ast"])[2]}']
for w,d in dictionary.items():out.append(f'{w} {d["mask"]} '+ ' '.join(map(str,d['properties'])))
for w,(a,b)in private.items():out.append(f'{w} {a} {b}')
out.append(expand(ax));(outdir/'input.txt').write_text('\n'.join(out)+'\n')
decomp={}
for i,row in enumerate(ast):
 if row[0]=='N'and bounds(row[1])==bounds(row[2])==(0,0):
  w=''.join(encode[j]for j in finest(i));a=''.join(encode[j]for j in finest(row[1]));b=''.join(encode[j]for j in finest(row[2]))
  decomp[w]=(a,b)
out.append(str(len(decomp)))
for w,(a,b)in decomp.items():out.append(f'{w} {a} {b}')
(outdir/'expanded-input.txt').write_text('\n'.join(out)+'\n')
value['decompositions']=decomp;(outdir/'expanded-input.json').write_text(json.dumps(value,indent=2)+'\n')
print(len(fixed),len(private),len(dictionary),len(expand(ax)),wp(ax),ap(s['original_ast']),len(decomp))
