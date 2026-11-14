import sys,json,os
sys.dont_write_bytecode = True
from pathlib import Path
BUNDLE=Path(__file__).resolve().parent
EXPECTED_REVISION='567266818aaeceb0f3a8f82debf303c8d84bddaf'
if not os.environ.get('PROVEIT_REPO'):
    raise SystemExit('Set PROVEIT_REPO to the pinned ProveIt checkout; see README.md.')
repo=Path(os.environ['PROVEIT_REPO']).expanduser().resolve()
if not repo.is_dir():
    raise SystemExit(f'PROVEIT_REPO is not a directory: {repo}')
base=repo/'Computability/BusyBeaver/Research/PA'
sys.path.insert(0,str(base/'docs/pa194_conpa_2026-11-13/construction'))
import compiler as c
import symbolic_runtime as sr
c.ROOT=sr.ROOT=base/'jamesyc-upstream/pa196'
nodes=c.raw_nodes()
orig=c.raw_nodes

def cfg(root):
    def rn():
        n=nodes.copy();n['node172']=(root,('leaf','halt',None));return n
    c.raw_nodes=rn
    sites,ins,_=c.source('node0')
    c.raw_nodes=orig
    return sites,ins

def run(root,rs,cap=10000000):
    sites,ins=cfg(root);rs=list(rs);pc=0
    for step in range(cap):
        op,*xs=ins[pc]
        if op=='halt':return step,rs
        if op=='inc':r,pc=xs;rs[r]+=1
        elif op=='dec':r,z,p=xs;pc=p if rs[r] else z;rs[r]=max(0,rs[r]-1)
        else:pc=xs[0]
    return 'limit',rs,pc
if __name__=='__main__':
  for name in ['node6','node17','node49','node55','node58','node142','node145','node146','node150']:
    for rs in [[0,7,32,3,5,8,0,0,0],[0,7,32,3,5,3,3,3,0]]:
      try:print(name,rs,run(name,rs))
      except Exception as e:print(name,type(e).__name__,str(e))
