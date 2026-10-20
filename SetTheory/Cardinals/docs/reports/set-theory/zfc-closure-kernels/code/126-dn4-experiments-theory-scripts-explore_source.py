from pathlib import Path
import sys,re,json,os,importlib.util
from functools import cache
ROOT=Path(os.environ.get('ZFC_EXPERIMENT_ROOT',Path(__file__).resolve().parents[1]))
BASE=Path(os.environ.get('ZFC225_BASE',ROOT/'baseline225/K225_Construction_2026-10-19/portable'))
BASELINE_SOURCE=Path(os.environ.get('ZFC_BASELINE_SOURCE',BASE/'results/sites225.json'))
BUILDER=Path(os.environ.get('ZFC_SOURCE_BUILDER',BASE/'baseline226/vendor/proveit/build_zfc235.py'))
DAG=Path(os.environ.get('ZFC_DAG230',ROOT/'k230-rocq/coq/prog/Dag230.v'))
OUTPUT_ROOT=Path(os.environ.get('ZFC_EXPERIMENT_OUTPUT',ROOT/'theory_work'))
DN4_SOURCE=Path(os.environ.get('ZFC_DN4_SOURCE',OUTPUT_ROOT/'full_dn/sites_full_dn4.json'))
spec=importlib.util.spec_from_file_location('experiment_source_builder',BUILDER)
b=importlib.util.module_from_spec(spec)
spec.loader.exec_module(b)
text=DAG.read_text()
alias={'ENode':'N','EInc':'CI','EDecnz':'CD','EBreak':'CB','EContinue':'CC','EHalt':'CH'}
nodes={}
for line in text.splitlines():
 m=re.search(r'\| (\d+) => \((.*), (.*)\)',line)
 if m:
  def edge(e):
   p=e.split();return (alias[p[0]],int(p[1]) if len(p)>1 else None)
  nodes[int(m[1])]=(edge(m[2]),edge(m[3]))
@cache
def expand(e):
 return tuple(map(expand,nodes[e[1]])) if e[0]=='N' else e
names={115:'unpair_pl',116:'unpair_ws',117:'times4',119:'im',121:'b',123:'eq_test',130:'ifeq_par1',131:'ifeq_clrtop',132:'ifeq_halt',133:'ifnot_pl',141:'dispatch',158:'read_s1',160:'pop_s1',162:'pair',166:'a',168:'c',170:'pop_b',171:'push',174:'read_c',175:'read_a',176:'read_b',177:'1',178:'and',180:'all',181:'mem',182:'eq',183:'ex',192:'ac_s1s2',193:'ac_tops1',194:'np_s1pl',197:'a_b',198:'a_tops1',199:'b_clear',200:'b_tops1',201:'s1_ac',203:'s1_np',205:'s1_a',207:'s1_b',208:'s1_top',209:'s2_pl',211:'s2_s1',212:'s2_ws',214:'top_clear',215:'top_s1s2',216:'top_s1',217:'ws_top',218:'neg'}
def flat(e):
 if e[0]=='N' and e[1] in names:return [names[e[1]]]
 if e[0]!='N':return [e]
 return flat(nodes[e[1]][0])+flat(nodes[e[1]][1])
if __name__=='__main__':
 print('Ax tokens:',flat(('N',236)))
 root=b.tree(json.loads(BASELINE_SOURCE.read_text()))
 for old,new in [(130,167),(171,216)]:
  t=expand(('N',old));r=expand(('N',new))
  matches=[]
  def walk(n,p=''):
   if n==t:matches.append(p)
   if not b.is_leaf(n):walk(n[0],p+'0');walk(n[1],p+'1')
  walk(root)
  print(old,'occurs',len(matches),matches)
 print('MP original',b.metrics(expand(('N',130))))
 old=expand(('N',130));new=(expand(('N',123)),expand(('N',167)))
 def repl(n):
  if n==old:return new
  return n if b.is_leaf(n) else (repl(n[0]),repl(n[1]))
 newroot=repl(root)
 print('Old stats',b.metrics(root),'MP without push stats',b.metrics(newroot))
