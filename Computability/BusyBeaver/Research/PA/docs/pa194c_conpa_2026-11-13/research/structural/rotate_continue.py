from pathlib import Path
import sys,json,itertools,time
PACKAGE=Path(__file__).resolve().parents[2]
ROOT=PACKAGE/'reference/pa194';OUT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'construction'));import compiler as c
original=c.raw_nodes();ax=c.read_grammar(ROOT/'construction/source/pa194.grammar.json')
oldsites,oldins,oldcs=c.source(ax)
newnodes=dict(original);newnodes['node170']=('node28',('node35','node169'));newnodes['node166']=(original['node166'][0],('leaf','continueTo',4))
c.raw_nodes=lambda:newnodes
sites,ins,contracts=c.source(ax)
assert ins==oldins
rows={}
for line in (ROOT/'construction/tables/pa194.native.tm').read_text().splitlines():
 q,b,w,d,n=line.split();rows[int(q),int(b)]=int(w),d=='R',int(n)
rows.update({(214,0):(0,True,95),(214,1):(1,True,188),(188,0):(0,True,111),(188,1):(1,True,312)})
cs=[x for x in contracts if x[0]==3660];assert len(cs)==1
print('NEW_SITE',sites[3660],ins[3660], 'ENTRY25',sites[25],flush=True)
results=[];states=sorted({q for q,b in rows});t=time.monotonic()
for w,d,n in itertools.product((0,1),(False,True),states):
 rows[18,1]=(w,d,n)
 length=c.run(rows,cs[0],fuel=2000)
 if length is not None:
  res={'action':[w,d,n],'length':length}
  res['full']=c.validate(rows,contracts)
  print('CANDIDATE',res,flush=True);results.append(res)
  if res['full']['ok']:
   out={k:v for k,v in rows.items()if k[0]!=34};out[23,0]=0,True,75
   res['scanner_delete']=c.validate(out,contracts);print('SCANNER',res['scanner_delete'],flush=True)
   (OUT/f'rotate_continue_{w}{int(d)}_{n}.native.tm').write_text(''.join(f'{q} {b} {ww} {"R"if dd else"L"} {nn}\n'for(q,b),(ww,dd,nn)in sorted(rows.items())))
(OUT/'rotate_continue_results.json').write_text(json.dumps({'results':results,'seconds':time.monotonic()-t,'site3660':sites[3660],'site25':sites[25],'source_graph_equal':True},indent=2)+'\n')
print('DONE',len(results),time.monotonic()-t,flush=True)
