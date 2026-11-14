from pathlib import Path
import json,sys
p=Path(sys.argv[1]); lines=(p.with_suffix(p.suffix+'.meta')).read_text().splitlines();R,P,N=map(int,lines[0].split());labels=[int(l.split()[0]) for l in lines[1:]]
positions=[0]+[i for j in range(1,R+1) for i in (-j,j)]
perm=[sum(((v>>(2*R-j))&1)<<(pos+R) for j,pos in enumerate(positions)) for v in range(P)]
data=p.read_bytes();out={};stats=[]
def rec(v,i):
 if 1 not in v:return False
 if 0 not in v:return True
 n=len(v)//2;a=rec(v[:n],i+1);b=rec(v[n:],i+1)
 if a==b:return a
 return positions[i],a,b
def cubes(node,path,result):
 if node is False:return
 if node is True:result.append(dict(path));return
 bit,a,b=node
 cubes(a,path+[(bit,0)],result);cubes(b,path+[(bit,1)],result)
for i,q in enumerate(labels):
 dat=data[i*P:(i+1)*P];ordered=bytes(dat[j] for j in perm);bdd=rec(ordered,0);out[q]=[];cubes(bdd,[],out[q]);stats.append((len(out[q]),q))
print('TOTAL',sum(x[0] for x in stats),'TOP',sorted(stats,reverse=True)[:20]);Path(str(p)+'.contexts.json').write_text(json.dumps(out))
