from pathlib import Path
import json,sys
sys.path.insert(0,str(Path(__file__).parent));import compile_eq as c
s=c.s
P='1110100101'
region=s.subtree(c.TREE,P);assert region[0]==('CI',6)
E=region[1][0][0];H=('CH',None);assert region[1][0][1]==H
D=('CD',5);Z=(D,('CC',1));J=(D,('CB',1))
S=((D,(J,H)),Z)
reuse=(D,(E,H))
out=Path(__file__).parent/'output/halt_specialization';out.mkdir(parents=True,exist_ok=True)
summary=[]
for name,replacement in [('six_leaf',(S,region[1][1])),('reuse_e',(reuse,region[1][1]))]:
 t=s.replace(c.TREE,P,replacement);d=out/name;d.mkdir(parents=True,exist_ok=True)
 (d/'sites.json').write_bytes(s.compact(s.sites(t)))
 (d/'tree.json').write_bytes(s.compact(t));(d/'replacement.json').write_bytes(s.compact(replacement))
 (d/'sites.in').write_text(''.join(f'{p} {o} {a if a is not None else -1}\n'for p,o,a in s.sites(t)))
 summary.append({'name':name,'metrics':s.metrics(t),'region_boundary':s.boundary(replacement),'replacement':replacement})
print(json.dumps(summary,indent=2));(out/'summary.json').write_text(json.dumps(summary,indent=2))
