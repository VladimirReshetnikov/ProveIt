#!/usr/bin/env python3
"""Reject semantic and control-flow tampering, not merely an expected hash."""
from pathlib import Path
from functools import cache
import argparse,hashlib,json,subprocess,sys
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
sys.path.insert(0,str(ROOT))
import source_language as c
import check_combined_emitter as audit

@cache
def flat(t):return (t,) if c.leaf(t) else flat(t[0])+flat(t[1])
def seq(xs):
 t=xs[-1]
 for n in reversed(xs[:-1]):t=n,t
 return t
def replace_path(t,path,new):
 if not path:return new
 b=int(path[0]);x=replace_path(t[b],path[1:],new)
 return (t[0],x) if b else (x,t[1])
def splice(tree,lo,hi,new):
 def visit(t,start):
  end=start+len(flat(t))
  if end<=lo or start>=hi:return t
  if lo<=start and end<=hi:
   assert c.boundary(t)==(0,0,False)
   return new if start==lo else None
  left=visit(t[0],start);right=visit(t[1],start+len(flat(t[0])))
  return right if left is None else left if right is None else(left,right)
 return visit(tree,0)

def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--source',type=Path,required=True);p.add_argument('--output-dir',type=Path,required=True);a=p.parse_args()
 assert __debug__
 out=a.output_dir;out.mkdir(parents=True,exist_ok=True)
 assert not any(out.iterdir()),'Use an empty output directory'
 rows=json.loads(a.source.read_text());original=c.tree(rows);controls={}
 for label,lo,hi in [('unaffected_prefix',0,486),('changed_G',486,895),('changed_seed_bundle',2650,4563)]:
  mutated=json.loads(a.source.read_text());i=next(i for i in range(lo,hi) if mutated[i][1]=='CI')
  mutated[i][2]=(mutated[i][2]+1)%9
  controls[label]=(mutated,dict(kind='increment_register_mutation',ordinal=i))
 macros={int(k):audit.freeze(v) for k,v in json.loads((HERE/'macro_data.json').read_text())['macros'].items()}
 word=audit.postfix(audit.formulas()[1]);assert word[8]==181
 pos=486+sum(len(flat(macros[m])) for m in word[:9])-1
 assert rows[pos][1:]==['CI',1]
 changed=replace_path(original,rows[pos][0],(('CI',1),('CI',1)))
 controls['G_binder_R_to_Q']=(c.sites(changed),dict(kind='binder_constructor_changed_from_R_to_Q',ordinal=pos))
 seedword=json.loads((ROOT/'inputs/grammar_seed.json').read_text())['macro_word']
 restored=seq([macros[m] for m in seedword])
 changed=splice(original,2650,4563,restored)
 assert len(flat(changed))==len(rows)+327
 controls['restored_old_helper']=(c.sites(changed),dict(kind='restored_H_in_seed_bundle',interval=[2650,4563]))
 origgraph=c.graph_intervals(rows)
 def rotations(t,path=''):
  if c.leaf(t):return
  if not c.leaf(t[0]):
   x,y=t[0];z=t[1]
   if not all(c.boundary(v)==(0,0,False) for v in(x,y,z)):yield path,(x,(y,z))
  for bit in(0,1):
   for path2,r in rotations(t[bit],path+str(bit)):
    yield path2,(r,t[1]) if bit==0 else(t[0],r)
 for path,t in rotations(original):
  r=c.sites(t)
  if c.graph_intervals(r)!=origgraph:
   controls['nonclosed_reassociation']=(r,dict(kind='primitive_order_preserving_control_mutation',path=path));break
 assert 'nonclosed_reassociation' in controls
 results=[]
 for name,(r,description) in controls.items():
  target=out/(name+'.json');target.write_text(json.dumps(r,separators=(',',':'))+'\n')
  cmd=[sys.executable,'-B',str(HERE/'check_combined_emitter.py'),'--source',str(target),'--output',str(out/(name+'_unexpected_pass.json'))]
  result=subprocess.run(cmd,capture_output=True,text=True)
  assert result.returncode!=0,(name,'Tampered source accepted')
  why=result.stderr.splitlines()[-1]
  assert 'Candidate has unexpected primitive source changes' in why or 'Candidate control targets differ from direct closed replacement' in why,(name,why)
  results.append(dict(name=name,returncode=result.returncode,rejection=why,**description))
 report=dict(status='ALL_SIX_NEGATIVE_CONTROLS_REJECTED',controls=results,source_sha256=hashlib.sha256(a.source.read_bytes()).hexdigest(),scope='Semantic primitive and complete-CFG rejection; the checker does not pin the candidate source hash.')
 (out/'receipt.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
