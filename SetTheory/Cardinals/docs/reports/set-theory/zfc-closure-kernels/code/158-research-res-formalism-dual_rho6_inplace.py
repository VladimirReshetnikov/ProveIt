from pathlib import Path
import os
import sys,json,itertools
HERE=Path(__file__).resolve().parent;Z=Path(os.environ.get('PROVEIT_ZFC_ROOT', str(HERE.parent/'ProveIt/Computability/BusyBeaver/Research/ZFC'))).resolve();sys.path.insert(0,str(Z/'k218-quantifier-stability/pricing'))
import source_language as s,build221 as b,measure_pinned as m
root=s.tree(json.loads((Z/'candidate-k218/sites218.json').read_text()));tab=b.read_table((Z/'candidate-k218/k218.native.tm').read_bytes());g,_=b.decoder_map(tab,root);q=lambda k:b.sole(g,k)
macros={'a':q(98),'b':q(12),'c':q(166),'I':q(90),'Q':q(86),'F':q(184)[0]};rev={v:k for k,v in macros.items()};seq=[]
def find(t,lo=0,p=''):
 hi=lo+len(s.sites(t))
 if hi<=895 or lo>=1178:return
 if t in rev and lo>=895 and hi<=1178:seq.append((p,rev[t],lo,hi));return
 if s.leaf(t):raise ValueError((p,t,lo,hi))
 find(t[0],lo,p+'0');find(t[1],lo+len(s.sites(t[0])),p+'1')
find(root);print(seq,flush=True)
assert [x[1]for x in seq]==['a','a','c','Q','F','I','Q','F','I','c','I']
out=HERE/'dual-rho6-inplace';out.mkdir(exist_ok=True);records=[]
for kind in('old','dual'):
 for v,w in itertools.permutations('abc',2):
  word=(v,v,w,'Q','F','I','Q','F','I',w,'I')if kind=='old'else(w,v,v,w,'F','I','Q','F','I','Q','I')
  t=root
  for (p,_,_,_),x in zip(seq,word):t=s.replace(t,p,macros[x])
  rr=s.sites(t);assert s.graph_intervals(rr)==s.graph_arithmetic(rr)[0];met=s.metrics(t);d=out/f'{kind}-{v}{w}';d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(s.compact(rr));info=dict(kind=kind,binder=v,matrix=w,metrics=met)
  try:tt,cm=m.compile_tree(s,b,tab,root,t);info['compiler']=cm;(d/'raw.tm').write_bytes(b.table_bytes(tt))
  except(ValueError,KeyError,AssertionError)as e:info['compiler_error']=repr(e)
  (d/'result.json').write_text(json.dumps(info,indent=2));records.append(info);print(info,flush=True)
(out/'result.json').write_text(json.dumps(records,indent=2))
