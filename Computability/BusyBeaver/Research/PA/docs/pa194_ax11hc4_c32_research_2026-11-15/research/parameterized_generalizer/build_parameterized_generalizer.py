#!/usr/bin/env python3
"""189-token AX prototype with a separate generalized-theorem offset field.

Discovery/replay artifact; this does not establish a sub-194 construction.
Its inherited arithmetic block contracts, inherited written weak-base
calibration, and unfinished Lean formalization are stated separately in
theory_note.tex.
"""
from pathlib import Path
import sys,json,hashlib,itertools,time
import compiler as c
import support as s
P=Path(__file__).resolve().parent
def tup(x):return tuple(map(tup,x)) if isinstance(x,list) else x
def flat(x):return flat(x[0])+flat(x[1]) if c.isnode(x) else [x]
def output(name,data):
    (OUT/name).write_text(json.dumps(data,indent=2)+'\n')
nodes={k:tup(v) for k,v in json.loads((P/'primary.nodes.json').read_text()).items()}
raw0=s.read_table(P/'primary.raw.native.tm')
c.machine=lambda:(raw0,[])
c.raw_nodes=lambda:nodes
inc=('leaf','inc',1)
c.MACROS[(inc,inc)]=99
c.MACROS[((inc,inc),(inc,inc))]=190
orig=c.read_grammar(P/'primary.grammar.json')
grammar=c.read_grammar(P/'newgen_189.grammar.json')
assert flat(orig)[:5]==['node58','node55','node65',inc,inc]
assert flat(grammar)==['node58','node75',inc,inc]+flat(orig)[5:]
assert len(flat(grammar))==189
raw,index,shape=c.build(grammar)
ops=c.opportunities_fast(raw,shape);pairs=c.max_matching(ops)
opmap={(a,b):v for a,b,v in ops}
choices=[[(a,b,act) for act in itertools.product(*opmap[a,b])] for a,b in pairs]
folds=None
for trial in itertools.product(*choices):
    try:
        child,aliases=s.apply_folds(raw,trial)
        cases=s.check_local_folds(raw,child,aliases,trial)
    except (AssertionError,KeyError):continue
    folds=list(trial);break
assert folds is not None
count=len(child)//2
print('states',count,'readers',len(shape),'folds',len(folds),flush=True)
sites,instructions,contracts=c.source(grammar)
print('sites',len(sites),'outcomes',len(contracts),flush=True)
runtime=c.validate(child,contracts)
print('runtime',runtime,flush=True)
assert runtime['ok']
startup=s.startup(child,sites[25][0])
dense,labels=s.dense_table(child,count)
OUT=P/'parameterized_generalizer';OUT.mkdir(exist_ok=True)
for name,rows in [('machine.tm',dense),('machine.native.tm',child),('raw.native.tm',raw)]:
    (OUT/name).write_text(s.table_text(rows))
output('labels.json',labels);output('folds.json',folds);output('local_fold_cases.json',cases)
output('sites.json',[[''.join(map(str,p)),op,a] for p,op,a in sites]);output('instructions.json',instructions)
receipt=dict(working_states=count,rows=len(child),AX_macro_tokens=189,source_sites=len(sites),source_outcomes=len(contracts),raw_readers=len(shape),fixed_states=134,folds=len(folds),runtime=runtime,startup=startup,dense_sha256=hashlib.sha256(s.table_text(dense).encode()).hexdigest(),kernel_checked=False,new_end_to_end_kernel_proof=False,scope='Construction-time symbolic source contracts using inherited arithmetic-block interfaces; not an independent literal-runtime audit.',written_calibration='Relative to inherited source-calculus/PA calibration; new source protocol proved by explicit offset-addition identity.')
output('receipt.json',receipt)
print(json.dumps(receipt,indent=2),flush=True)
