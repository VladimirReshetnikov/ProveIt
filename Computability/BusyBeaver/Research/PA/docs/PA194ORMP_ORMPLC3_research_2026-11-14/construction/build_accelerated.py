#!/usr/bin/env python3
"""Compose the LC return and three exact shortcuts with PA194ORMP.

The construction is retained only after complete literal source verification;
the positive result never relies on adding state counts of separate packets.
"""
from pathlib import Path
import sys,json,hashlib,argparse
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'vendor'))
import compiler as c,support as s
def tup(x):return tuple(map(tup,x))if isinstance(x,list)else x
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def main(source=None,output=None):
 assert __debug__
 src=source or HERE/'machine';out=output or HERE/'accelerated';out.mkdir(exist_ok=True,parents=True)
 raw=s.read_table(src/'raw.native.tm')
 nodes={k:tup(v)for k,v in json.loads((src/'nodes.json').read_text()).items()}
 grammar=c.read_grammar(src/'grammar.json');c.raw_nodes=lambda:nodes
 oldsites,oldins,_=c.source(grammar)
 inc=('leaf','inc',1)
 nodes['node62']=((inc,inc),((inc,inc),('leaf','continueTo',3)))
 raw.update({(139,0):(0,True,99),(139,1):(1,True,190),(190,1):(1,False,73)})
 sites,ins,contracts=c.source(grammar)
 assert ins==oldins
 folds=json.loads((src/'folds.json').read_text())
 rows,aliases=s.apply_folds(raw,folds)
 local=s.check_local_folds(raw,rows,aliases,folds)
 lc=dict(rows)
 # The 124/127 selector transforms the caller discipline without changing
 # the number of states; the two independent one-row accelerations follow.
 selector={(q,b):(w,d,127 if n==124 else n)for(q,b),(w,d,n)in rows.items()}
 selector[127,0]=(0,False,124)
 selector[124,0]=(0,True,8)
 selector[124,1]=(1,True,59)
 rows=dict(selector)
 rows.update({(26,1):(1,True,91),(101,0):(0,True,17),(190,1):(0,False,42)})
 valid=c.validate(rows,contracts);assert valid['ok'],valid
 startup=s.startup(rows,sites[25][0])
 dense,labels=s.dense_table(rows)
 for name,table in [('machine.tm',dense),('machine.native.tm',rows),('raw.native.tm',raw),('lc.native.tm',lc),('selector.native.tm',selector)]:
  (out/name).write_text(s.table_text(table))
 for name,obj in [('nodes.json',nodes),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',ins),('folds.json',folds),('local_folds.json',local),('labels.json',labels)]:save(out/name,obj)
 (out/'grammar.json').write_text((src/'grammar.json').read_text())
 receipt=dict(name='PA194ORMPLC3',states=194,rows=388,source_sites=len(sites),source_outcomes=len(contracts),source_instructions_identical=True,changed_source_addresses_from_ORMP=sum(a[0]!=b[0]for a,b in zip(sites,oldsites)),max_path_length=max(len(p)for p,_,_ in sites),runtime=valid,startup=startup,sha256=hashlib.sha256(s.table_text(dense).encode()).hexdigest(),parent_sha256=hashlib.sha256((src/'machine.tm').read_bytes()).hexdigest(),proof_scope='Full literal source replays required; selector and accelerations are independently inherited transformations, not state savings.')
 save(out/'receipt.json',receipt)
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--source',type=Path);parser.add_argument('--output',type=Path)
 args=parser.parse_args();main(args.source,args.output)
