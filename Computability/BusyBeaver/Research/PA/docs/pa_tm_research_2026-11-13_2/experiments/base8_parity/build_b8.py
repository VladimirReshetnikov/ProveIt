#!/usr/bin/env python3
from pathlib import Path
import sys,json,re,time,hashlib
HERE=Path(__file__).resolve().parent
import symbolic as S, folds as F
from types import SimpleNamespace
B=SimpleNamespace(BASE={k:v for k,v in S.load_machine().items() if k[0]<134},
                  ATOM={'P': 19, 'H': 12, 'A': 86, 'D': 116, 'C': 78, 'R': 64, 'S': 126, 'G': 122, 'K': 129, 'i': 58},FREE={('i','i'):87,(('i','i'),('i','i')):121})
GFILE=HERE/'B8_AX_grammar.json'
data=json.loads(GFILE.read_text())
q=S.LITERAL
m=B.BASE.copy()
m[111,0]=(0,1,1999);m[1999,0]=(0,1,121);m[1999,1]=(1,1,121)
rules=data['rules']
def dec(x):return tuple(map(dec,rules[x])) if x in rules else x
grammar=dec(data['root']);new={}
def emit(x):
 if x in B.FREE:return B.FREE[x]
 if isinstance(x,str):return B.ATOM[x]
 if x in new:return new[x]
 a,b=x
 def row(t,bit):return (0,-1,131 if bit else 5) if t=='B' else(bit,1,emit(t))
 aa,bb=row(a,0),row(b,1);n=1000+len(new);new[x]=n;m[n,0]=aa;m[n,1]=bb;return n
entry=emit(grammar);m[89,1]=(1,1,entry)
# Parity sum prelude and acceptance, identical to the prior checked fragment.
m[q[68],0]=(0,1,q[108]);m[2000,0]=m[q[108],0];m[2000,1]=(1,1,q[68]);m[q[53],0]=(0,1,2000)
m[q[38],1]=(1,1,q[30]);m[q[310],1]=(0,-1,16)
# Longer return scan for changed root geometry.
m[q[34],0]=(0,-1,2001);m[2001,0]=(0,-1,q[75]);m[2001,1]=(1,-1,q[2])
reach={0};todo=[0]
for x in todo:
 for bit in(0,1):
  if(x,bit)not in m:continue
  z=m[x,bit][2]
  if z not in reach:reach.add(z);todo.append(z)
m={k:v for k,v in m.items()if k[0]in reach}
original,defs=S.source_tree()
def sub(t,a,b):
 if t==a:return b
 return t if t[0]=='leaf'else(sub(t[0],a,b),sub(t[1],a,b))
newC=sub(defs['node65'],defs['node62'],((defs['node61'],defs['node61']),defs['node62'][1]))
atoms={tok:sub(defs[n],defs['node65'],newC)for n,tok in data['tokens'].items()}
atoms.update(i=('leaf',('inc',1)),B=('leaf',('breakTo',1)))
def exp(t):return atoms[t]if isinstance(t,str)else(exp(t[0]),exp(t[1]))
ax=exp(grammar)
tree=sub(original,defs['x67'],ax);tree=sub(tree,defs['node65'],newC)
newguard=(('leaf',('dec',6)),(defs['node0'],('leaf',('halt',))))
tree=sub(tree,defs['node7'],newguard);tree=sub(tree,defs['node168'],(defs['node37'],defs['node56']))
tree=(tree[0],(tree[1][0],('leaf',('continueTo',2))))
ss=S.flatten(tree);S.all_sites=lambda:ss
recode=list(re.sub('C(i*)',lambda z:'C'+'i'*{3:4}.get(len(z[1]),len(z[1])),''.join(data['original_word'])))
assert recode==data['word']
protected={x for x,b in S.ENGINE_ROWS}|{m[k][2]for k in S.ENGINE_ROWS if k in m}|{0,S.ROOT}
opts=F.candidates(m,{x for x,b in m}-protected);selected,checks=F.select(m,opts);folded,mapping=F.fold(m,selected)
(HERE/'B8_source_sites.json').write_text(json.dumps(ss,separators=(',',':'))+'\n')
(HERE/'B8_source_tree.json').write_text(json.dumps(tree,separators=(',',':'))+'\n')
(HERE/'B8_AX_grammar.json').write_text(json.dumps(data,indent=2)+'\n')
receipts=[]
for name,table in [('raw',m),('folded',folded)]:
 p=HERE/f'B8_parity_{name}.tm';p.write_text(''.join(f'{x} {b} {w} {"R"if d==1 else"L"} {z}\n'for(x,b),(w,d,z)in sorted(table.items())))
 assert S.check_engine(table)
 fails=[];passed=0;maxsteps=0;start=time.time()
 for i,typ,br,initial,target in S.contracts():
  ans=S.execute(table,br,initial,target)
  if ans is None:fails.append([i,typ,list(ss[i][0]),list(ss[i][1])])
  else:passed+=1;maxsteps=max(maxsteps,ans[0])
 receipt=dict(name=name,states=len(table)//2,source_sites=len(ss),contracts=passed+len(fails),passed=passed,failures=fails,max_symbolic_steps=maxsteps,seconds=time.time()-start,sha256=hashlib.sha256(p.read_bytes()).hexdigest(),scope='Full constructor/tag/parity integration; source-site runtime contracts only, not a blank-start or consistency theorem.')
 receipts.append(receipt);print(json.dumps(receipt|{'failures':len(fails)}),flush=True)
(HERE/'B8_integration_receipt.json').write_text(json.dumps(dict(constructor_base=8,tags=dict(I=0,M=1,U=2,E=4),formula_word_length=len(recode),equality_tag_extensions=len(re.findall('Ciii(?!i)',''.join(data['original_word']))),selected_folds=selected,fold_mapping=mapping,results=receipts),indent=2)+'\n')
