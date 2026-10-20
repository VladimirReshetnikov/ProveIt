from pathlib import Path
import os,sys,json
ROOT=Path(__file__).resolve().parents[1]
base=ROOT/'k220_replay/baseline/K221_Construction_2026-10-20'
os.environ['K221_BASE']=str(base);sys.path.insert(0,str(base/'portable'))
import source_language as s,build221 as b
sys.path.insert(0,str(ROOT/'baseline220/K220_Construction_2026-10-20/research/encoding/scripts'));import recompile
rows=json.loads((ROOT/'baseline220/K220_Construction_2026-10-20/machine/sites220.json').read_text());old=s.tree(rows);T=b.read_table((ROOT/'baseline220/K220_Construction_2026-10-20/machine/k220.native.tm').read_bytes())
p='1110100101';n=s.subtree(old,p);assert n[0]==('CI',6);rest=n[1][1];assert s.boundary(rest)==(0,0,False)
D3=(('CD',5),('CC',4));D2=(('CD',5),D3);D1=(('CD',5),(D2,('CB',1)));D0=(('CD',5),(D1,('CH',None)))
new=s.replace(old,p,(D0,rest));assert s.boundary(D0)==(0,0,True)
print('source',s.metrics(new));nt,cm=recompile.compile_tree(T,old,new);print('compiled',cm)
out=ROOT/'theory_notes/membership_halt';out.mkdir(exist_ok=True);(out/'sites.json').write_bytes(s.compact(s.sites(new)));(out/'candidate.tm').write_bytes(b.table_bytes(nt));(out/'compile.json').write_text(json.dumps(cm,indent=2)+'\n')
