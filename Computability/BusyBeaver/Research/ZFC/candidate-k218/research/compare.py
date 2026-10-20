from pathlib import Path
import json,hashlib
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
PK=Path('/tmp/zfc-intake188/drop-k218/extracted/K218_Construction_2026-10-20')
OUT=Path(__file__).resolve().parent
B=ROOT/'Computability/BusyBeaver/Research/ZFC/candidate-k219'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
 t={}
 for l in p.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,z=l.split();k=(int(q),int(b));assert k not in t;t[k]=(int(w),d,int(z))
 return t
def enc(t):return ('#! start 0\n'+''.join(f'{q} {b} {w} {d} {z}\n'for(q,b),(w,d,z)in sorted(t.items()))).encode()
def nodes(rows):
 tree={}
 for p,op,a in rows:
  n=tree
  for c in p:n=n.setdefault(c,{})
  assert not n;n['v']=(op,a)
 def build(n):return n['v'] if 'v'in n else (build(n['0']),build(n['1']))
 root=build(tree);seen=set()
 def visit(n):
  if n in seen:return
  seen.add(n)
  if not isinstance(n[0],str):visit(n[0]);visit(n[1])
 visit(root);return len(seen)
old=read(B/'k219.native.tm');new=read(PK/'machine/k218.native.tm')
delta={k:v for k,v in new.items()if old[k]!=v}
result={'status':'SOURCE_AND_LITERAL_COMPARISON','base':{'path':str(B/'k219.native.tm'),'sha256':sha(B/'k219.native.tm')},'k218':{'path':str(PK/'machine/k218.native.tm'),'sha256':sha(PK/'machine/k218.native.tm')},'deleted':sorted({q for q,b in old}-{q for q,b in new}),'changed_rows':[{'row':k,'old':old[k],'new':v}for k,v in sorted(delta.items())],'variant_conflicts':{}}
for name in ['zero_terminal','retagged','composed']:
 p=B/'alternatives/machine'/name/'k219.upstream-labels.tm';v=read(p)
 patch={k:x for k,x in v.items()if old[k]!=x}
 conflict=[{'row':k,'k218':new[k],'alternative':x}for k,x in patch.items()if k in delta and new[k]!=x]
 result['variant_conflicts'][name]={'sha256':sha(p),'rows':len(patch),'conflicts':conflict,'removed_references':[k for k,x in patch.items()if k[0]==212 or x[2]==212]}
assert new[157,1]==(1,'L',148)
stack=dict(new);stack[157,1]=(1,'L',187);(OUT/'row157.native.tm').write_bytes(enc(stack))
result['row157']={'path':str(OUT/'row157.native.tm'),'sha256':sha(OUT/'row157.native.tm'),'old':new[157,1],'new':stack[157,1]}
# The earlier delete301 three-row candidate retains its complete failed prefix.
core={k:x for k,x in new.items()if k[0]!=301}
core[87,0]=(0,'R',88);core[88,0]=(0,'L',51);core[51,0]=(0,'R',122)
f=json.loads((PK/'research/encoding/rejected_startup_receipt.json').read_text())
checks=[]
for tick,q,h,b,w,d,z in f['finite_trace']:
 checks.append(core[q,b]==(w,'R'if d==1 else'L',z))
assert len(checks)==85 and all(checks) and core[35,0]==(1,'R',35)
result['delete301_stack']={'states':len({q for q,b in core}),'all_85_prefix_rows_identical':True,'same_infinite_ray':True,'receipt_sha256':sha(PK/'research/encoding/rejected_startup_receipt.json'),'scope':'Literal transition equality transfers the full stored blank prefix and writing-ray induction; no new simulation or runtime proof.'}
rows=json.loads((PK/'machine/sites218.json').read_text());mod=json.loads(json.dumps(rows))
changes=[]
for i,op,oldarg,newarg in [(966,'CD',3,5),(971,'CI',3,5),(1144,'CD',3,5),(1149,'CI',3,5)]:
 assert mod[i][1:]==[op,oldarg];mod[i][2]=newarg;changes.append({'ordinal':i,'address':mod[i][0],'opcode':op,'old':oldarg,'new':newarg})
result['rho6_source_only']={'dag_before':nodes(rows),'dag_after':nodes(mod),'changes':changes,'scope':'Literal operand transport only; no table allocation or runtime claim.'}
(OUT/'rho6-sites.json').write_text(json.dumps(mod,separators=(',',':'))+'\n')
(OUT/'comparison.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in('changed_rows','base','k218')},indent=2))
