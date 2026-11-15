#!/usr/bin/env python3
"""Compose the operand and MP reassociations, then check all local source outcomes."""
from pathlib import Path
import sys,json,hashlib,argparse
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import compiler as c,support as s
def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main(output=None):
 assert __debug__
 src=HERE/'inputs';out=output or HERE/'machine';out.mkdir(exist_ok=True,parents=True)
 raw=s.read_table(src/'or_raw.native.tm')
 nodes={k:tup(v) for k,v in json.loads((src/'or_nodes.json').read_text()).items()}
 grammar=c.read_grammar(src/'or_grammar.json')
 c.raw_nodes=lambda:nodes
 oldsites,oldins,_=c.source(grammar)
 assert json.loads(json.dumps(oldins))==json.loads((src/'parent_instructions.json').read_text())
 assert nodes['node164']==('node162','node163')
 assert nodes['node162']==('node75','node37') and nodes['node163']==('node6','node54')
 nodes['node164']=('node75',('node37',('node6','node54')))
 sites,ins,contracts=c.source(grammar)
 assert ins==oldins
 edits={(100,0):213,(100,1):174,(174,0):28,(174,1):164}
 for key,target in edits.items():
  w,d,_=raw[key];raw[key]=w,d,target
 folds=json.loads((src/'or_folds.json').read_text())
 rows,aliases=s.apply_folds(raw,folds)
 local=s.check_local_folds(raw,rows,aliases,folds)
 valid=c.validate(rows,contracts)
 assert valid['ok'],valid
 startup=s.startup(rows,sites[25][0])
 dense,labels=s.dense_table(rows)
 for name,table in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw)]:
  (out/name).write_text(s.table_text(table))
 for name,obj in [('nodes.json',nodes),('sites.json',[[''.join(map(str,p)),op,a] for p,op,a in sites]),('instructions.json',ins),('folds.json',folds),('local_folds.json',local),('labels.json',labels)]:save(out/name,obj)
 (out/'grammar.json').write_text((src/'or_grammar.json').read_text())
 receipt=dict(name='PA194ORMP',states=194,rows=388,raw=201,fixed=135,readers=66,folds=7,source_sites=len(sites),source_outcomes=len(contracts),source_instructions_identical=True,changed_source_addresses_from_ORH=sum(a[0]!=b[0] for a,b in zip(sites,oldsites)),max_path_length=max(len(p)for p,_,_ in sites),runtime=valid,startup=startup,sha256=hashlib.sha256(s.table_text(dense).encode()).hexdigest(),parent_sha256=hashlib.sha256((src/'parent.tm').read_bytes()).hexdigest())
 save(out/'receipt.json',receipt)
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path)
 main(parser.parse_args().output)
