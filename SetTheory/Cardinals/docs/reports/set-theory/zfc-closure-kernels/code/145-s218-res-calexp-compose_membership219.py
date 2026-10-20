from rho8_membership import *
sys.path.insert(0,str(ROOT/'K219_Construction_2026-10-20/portable'))
import build_source219 as eq
from collections import Counter

def compose(t):
 occurrences=[]
 def rec(n,path=''):
  if n==eq.OLD:occurrences.append(path);return eq.NEW
  return n if z.s.leaf(n)else(rec(n[0],path+'0'),rec(n[1],path+'1'))
 new=rec(t);assert len(occurrences)==4
 return new,occurrences

if __name__=='__main__':
 out=ROOT/'membership_from219';out.mkdir(exist_ok=True);rs=[]
 old=z.s.tree(json.loads((ROOT/'K219_Construction_2026-10-20/machine/sites219.json').read_text()));tab=z.b.read_table((ROOT/'K219_Construction_2026-10-20/machine/k219.native.tm').read_bytes())
 for a,b in itertools.permutations(['a','b','c'],2):
  for shape in['left','right']:
   t,paths=compose(makeU(a,b,shape));rows=z.s.sites(t);assert z.s.graph_arithmetic(rows)[0]==z.s.graph_intervals(rows)
   r={'U':[a,b],'shape':shape,'source_metrics':z.s.metrics(t),'equality_macro_replacements':paths,'status':'LOGICAL_CALIBRATION_OPEN'}
   d=out/f'{a}{b}_{shape}';d.mkdir(exist_ok=True);(d/'sites.json').write_bytes(z.s.compact(rows))
   try:tt,mm=z.compile_tree(tab,old,t);r['compiler']=mm;(d/'candidate.tm').write_bytes(z.b.table_bytes(tt))
   except Exception as e:r['error']=repr(e)
   rs.append(r);print(json.dumps(r),flush=True)
 (out/'summary.json').write_text(json.dumps(rs,indent=2)+'\n')
