#!/usr/bin/env python3
from pathlib import Path
import json,hashlib
import compiler as c
import support as s
HERE=Path(__file__).resolve().parent
INC=('leaf','inc',1)
c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
grammar=c.read_grammar(HERE/'inputs/pa194.grammar.json')
raw,_,shape=c.build(grammar);folds=json.loads((HERE/'inputs/pa194.folds.json').read_text())
rows,aliases=s.apply_folds(raw,folds);local=s.check_local_folds(raw,rows,aliases,folds)
sites,instructions,contracts=c.source(grammar)
seed=s.startup(rows,sites[25][0]);assert seed['steps']==58154
dense,labels=s.dense_table(rows,194)
import argparse
parser=argparse.ArgumentParser(description='Rebuild the pinned primary PA194 table.')
parser.add_argument('--output',type=Path)
args=parser.parse_args()
out=args.output or HERE.parent/'baseline';out.mkdir(parents=True,exist_ok=True)
for name,table in [('machine.tm',dense),('machine.native.tm',rows),('raw201.native.tm',raw)]:
 (out/name).write_text(s.table_text(table))
for name,obj in [('labels.json',labels),('sites.json',[[''.join(map(str,p)),op,a]for p,op,a in sites]),('instructions.json',instructions),('folds.json',folds),('local_fold_cases.json',local),('receipt.json',dict(startup=seed,states=194,source_sites=len(sites),source_outcomes=len(contracts),dense_sha256=hashlib.sha256(s.table_text(dense).encode()).hexdigest(),scope='Primary table reconstructed; independent physical checker run separately.'))]:
 (out/name).write_text(json.dumps(obj,indent=2)+'\n')
assert hashlib.sha256((out/'machine.tm').read_bytes()).hexdigest()=='4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f'
print(json.dumps(json.loads((out/'receipt.json').read_text())|{'startup':'58,154 complete tape moves'},indent=2),flush=True)
