#!/usr/bin/env python3
"""Offline deterministic AX11G constructor and universal contract replay.

Uses frozen PA194G raw table/source, the inherited seven folds, and one exact
terminal AX source change. Run with Python3 and assertions enabled.
"""
from pathlib import Path
import sys,json,hashlib,argparse,tempfile
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent/'machine'
INPUT=HERE/'inputs'
sys.path.insert(0,str(HERE/'vendor'))
import compiler as c, support as s
HASH='7e1c6442816e5df05e961f2057719252a1976c9a195a786978bf1e2d3c8e466d'
def tup(t):return tuple(map(tup,t))if isinstance(t,list)else t
def replace(t):
 if t==c.BREAK:return'node49'
 return tuple(map(replace,t))if c.isnode(t)else t
def build(output,full=True):
 if not __debug__ or sys.flags.optimize:raise RuntimeError('Run with assertions enabled.')
 INC=('leaf','inc',1)
 raw0=s.read_table(INPUT/'parent.raw.native.tm')
 ns={k:tup(v)for k,v in json.loads((ROOT/'nodes.json').read_text()).items()}
 c.machine=lambda:(raw0,[]);c.raw_nodes=lambda:ns
 c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
 old=tup(json.loads((INPUT/'parent_grammar.tree.json').read_text()))
 g=replace(old)
 assert json.loads(json.dumps(g))==json.loads((ROOT/'grammar.tree.json').read_text())
 raw,index,shape=c.build(g)
 assert len(raw)==402 and len(shape)==67
 folds=json.loads((ROOT/'folds.json').read_text());assert len(folds)==7
 rows,aliases=s.apply_folds(raw,folds)
 local=s.check_local_folds(raw,rows,aliases,folds)
 assert len(local['cases'])==28
 sites,ins,contracts=c.source(g)
 assert len(sites)==3672 and len(contracts)==4779
 assert json.loads(json.dumps(ins))==json.loads((ROOT/'instructions.json').read_text())
 assert [[''.join(map(str,p)),op,a]for p,op,a in sites]==json.loads((ROOT/'sites.json').read_text())
 for q in c.BOXSTATES:
  for bit in(0,1):assert rows[q,bit]==raw0[q,bit]
 valid=c.validate(rows,contracts)if full else None
 if full:assert valid=={'ok':True,'contracts':4779,'max_steps':470,'total_steps':1483363}
 startup=s.startup(rows,sites[25][0]);assert startup['steps']==58154
 dense,labels=s.dense_table(rows,194)
 digest=hashlib.sha256(s.table_text(dense).encode()).hexdigest();assert digest==HASH
 assert s.table_text(rows)==(ROOT/'machine.native.tm').read_text()
 assert s.table_text(dense)==(ROOT/'machine.tm').read_text()
 assert labels==json.loads((ROOT/'labels.json').read_text())
 output.mkdir(parents=True,exist_ok=True)
 for name,m in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw)]:
  (output/name).write_text(s.table_text(m))
 receipt={'family':'PA194AX11G','status':'PASS','working_states':194,'transition_rows':388,
  'fixed_controls':134,'raw_AX_readers':67,'simultaneous_folds':7,'local_fold_cases':28,
  'source_sites':3672,'source_outcomes':4779,'arithmetic_box_rows_unchanged':True,
  'universal_construction_replay_performed':full,'runtime':valid,'startup':startup,
  'dense_sha256':digest,'kernel_checked':False,
  'scope':'Source identity, complete positive symbolic contracts and whole blank startup; independent literal replay and logical calibration are separate obligations.'}
 (output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
 print(json.dumps(receipt,indent=2));return receipt
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=Path)
 p.add_argument('--quick',action='store_true',help='Skip universal construction replay, explicitly recorded.')
 a=p.parse_args();build(a.output or Path(tempfile.mkdtemp(prefix='pa194ax11g-')),not a.quick)
