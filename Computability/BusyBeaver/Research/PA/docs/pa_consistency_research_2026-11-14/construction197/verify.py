#!/usr/bin/env python3
"""Regenerate/check the literal 197-state implementation of the new NEG18 macro.

All inputs are local. Python standard library only; use assertions enabled.
The symbolic runtime uses the unchanged inherited register-block contracts.
No Lean build or internal PA consistency-equivalence proof is claimed.
"""
from pathlib import Path
from collections import deque
import argparse,hashlib,importlib.util,json,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'code/search'));sys.path.insert(0,str(HERE/'code'))
from support import c,INC,tree_word,encode,apply,localvalid,raw
import source_language as independent

def need(x,message):
    if not x:raise ValueError(message)
def digest(data):return hashlib.sha256(data).hexdigest()
def compact(x):return (json.dumps(x,separators=(',',':'))+'\n').encode()
def norm(row,start):
    n=2 if row[0]in('inc','dec')else 1
    return tuple(row[:n])+tuple(x-start for x in row[n:])
def targets(row):
    return row[2:]if row[0]in('inc','dec')else row[1:]
def leaf_count(x):
    if isinstance(x,str):return leaf_count(raw[x])
    return sum(map(leaf_count,x))if c.isnode(x)else 1

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--check',action='store_true',help='Check existing outputs byte-for-byte without rewriting');args=ap.parse_args()
    need(__debug__,'Do not run Python with -O')
    ref=HERE/'code/reference'
    need(digest((ref/'data/pa196.tm').read_bytes())=='e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8','upstream literal hash')
    need(digest((ref/'PA196/Program.lean').read_bytes())=='8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872','upstream source hash')
    c.MACROS.update({'node37':28,'node64':106,('leaf','inc',7):82})
    c.MACROS[(INC,INC)]=99;c.MACROS[((INC,INC),(INC,INC))]=190
    original=c.read_grammar(HERE/'inputs/separate196.grammar.json')
    word=list(tree_word(original));newword=word[:];positions=[]
    for i in range(len(word)-2):
        if word[i:i+3]==['node49',INC,'node65']:
            newword[i:i+3]=[('leaf','inc',7),('leaf','inc',7),'node64'];positions.append(i)
    need(len(word)==190 and len(positions)==8,'exact eight negation replacements')
    it=iter(newword)
    def replace(x):return tuple(replace(y)for y in x)if c.isnode(x)else next(it)
    grammar=replace(original)
    rows,index,shape=c.build(grammar)
    chosen=json.loads((HERE/'inputs/folds.json').read_text())
    folded,aliases=apply(rows,chosen)
    need(localvalid(rows,folded,aliases,chosen),'simultaneous contextual fold certificate')
    need(len(shape)==68 and len(chosen)==5 and len(folded)==394,'state and row census')
    baseline,_=c.machine()
    need(all(folded[q,b]==baseline[q,b]for q in c.BOXSTATES for b in(0,1)),'unchanged abstract register engine')
    oldsites,oldgraph,_=c.source(original)
    sites,graph,contracts=c.source(grammar)
    need(len(oldsites)==3673 and len(sites)==3441,'exact source site census')
    # Independent arithmetic-path and interval CFG resolution of the new source.
    opmap={'inc':'CI','dec':'CD','breakTo':'CB','continueTo':'CC','halt':'CH'}
    flat=[[''.join(map(str,p)),opmap[op],arg]for p,op,arg in sites]
    g1,checks=independent.graph_arithmetic(flat);g2=independent.graph_intervals(flat)
    expected=[]
    for row in graph:
        if row[0]=='inc':expected.append([['increment',row[1]],[row[2]]])
        elif row[0]=='dec':expected.append([['decrement',row[1]],[row[2],row[3]]])
        elif row[0]=='jump':expected.append([['identity'],[row[1]]])
        else:expected.append([['halt'],[]])
    need(g1==g2==expected,'independent CFG resolvers')
    spec=importlib.util.spec_from_file_location('neg18_independent',HERE/'macro_proof/verify.py');proof=importlib.util.module_from_spec(spec);spec.loader.exec_module(proof)
    source_nodes=proof.parse_source(HERE/'macro_proof/reference/Program.lean')
    universal=proof.loop_certificate(proof.resolve(source_nodes['node64']))
    need(json.loads((HERE/'macro_proof/reference/seed18_197.grammar.json').read_text())==json.loads(json.dumps(encode(grammar))),'independent candidate grammar binding')
    need(json.loads((HERE/'macro_proof/reference/seed18_197.sites.json').read_text())==[[list(p),op,arg]for p,op,arg in sites],'independent candidate site binding')
    source_certificate=proof.candidate_source_binding(source_nodes,HERE/'macro_proof/reference/seed18_197.grammar.json',HERE/'macro_proof/reference/seed18_197.sites.json',proof.resolve(proof.sequence([('leaf','inc',7),('leaf','inc',7),source_nodes['node64']])))
    templates={47:proof.resolve(proof.sequence([source_nodes['node49'],('leaf','inc',1),source_nodes['node65']])),
               18:proof.resolve(proof.sequence([('leaf','inc',7),('leaf','inc',7),source_nodes['node64']]))}
    def entries(w):
        cursor=50;out=[]
        for i,x in enumerate(w):
            if i in positions:out.append(cursor)
            cursor+=leaf_count(x)
        return out
    oldentries,newentries=entries(word),entries(newword)
    for source,es,size in [(oldgraph,oldentries,47),(graph,newentries,18)]:
        for a in es:
            need([norm(row,a)for row in source[a:a+size]]==templates[size],'exact negation block CFG')
            for pc,row in enumerate(source):
                for dest in targets(row):
                    need(not(a<dest<a+size)or a<=pc<a+size,'external entry to negation block interior')
                    if a<=pc<a+size:need(a<=dest<=a+size,'nonlocal exit from negation block')
    def relocate(pc):
        need(not any(a<pc<a+47 for a in oldentries),'attempt to relocate block interior')
        return pc-29*sum(a+47<=pc for a in oldentries)
    outside=0
    for pc,row in enumerate(oldgraph):
        if any(a<=pc<a+47 for a in oldentries):continue
        n=2 if row[0]in('inc','dec')else 1
        translated=tuple(row[:n])+tuple(relocate(x)for x in row[n:])
        need(graph[relocate(pc)]==translated,'outside CFG relocation')
        need(sites[relocate(pc)]==oldsites[pc],'outside source paths/operations')
        outside+=1
    runtime=c.validate(folded,contracts);need(runtime['ok'],'all symbolic primitive contracts')
    need(runtime['contracts']==4468,'symbolic contract census')
    # Sound joint zero/positive reachability from the actual source seed.
    def successors(row,mask):
        if row[0]=='inc':yield row[2],mask|(1<<row[1])
        elif row[0]=='dec':
            bit=1<<row[1]
            if mask&bit:yield row[3],mask;yield row[3],mask^bit
            else:yield row[2],mask
        elif row[0]=='jump':yield row[1],mask
    seen={(25,1)};queue=deque(seen)
    while queue:
        pc,mask=queue.popleft()
        for state in successors(graph[pc],mask):
            if state not in seen:seen.add(state);queue.append(state)
    need(all(all(s in seen for s in successors(graph[pc],mask))for pc,mask in seen),'inductive abstract closure')
    entry_receipts=[]
    for pc in newentries:
        masks=sorted(m for p,m in seen if p==pc)
        need(masks and all(m&192==0 for m in masks),'both scratch registers zero at each replacement entry')
        entry_receipts.append({'site':pc,'mask_count':len(masks),'registers_6_and_7_forced_zero':True})
    need(len(seen)==245112,'joint-mask census')
    # Complete finite startup, including every nonzero cell and the absolute head.
    q=74;head=0;ones=set()
    for _ in range(58154):
        w,d,q=folded[q,int(head in ones)];(ones.add if w else ones.discard)(head);head+=1 if d else-1
    physical=[0,0,0,0,0,0,2,0,0]+[1]*26;target={head-1,head};pos=head+48;target.add(pos);pos+=1
    for v in physical:pos+=1;target.update(range(pos,pos+v+1));pos+=v+1
    need((q,head)==(84,-2)and ones==target,'complete blank-tape startup')
    reached={74};todo=[74]
    for state in todo:
        for bit in(0,1):
            nxt=folded[state,bit][2]
            if nxt!=254 and nxt not in reached:reached.add(nxt);todo.append(nxt)
    need(reached=={q for q,b in folded}and len(reached)==197,'graph-reachable working states')
    native=''.join(f'{q} {b} {w} {"R"if d else"L"} {n}\n'for(q,b),(w,d,n)in sorted(folded.items())).encode()
    labels=[74]+sorted(reached-{74})+[254];mapping={q:i for i,q in enumerate(labels)}
    dense=''.join(f'{mapping[q]} {b} {w} {"R"if d else"L"} {mapping[n]}\n'for q in labels[:-1]for b in(0,1)for w,d,n in[folded[q,b]]).encode()
    need(digest(native)=='06f0d712e0933e80c2a0e82c765dbf82b4a9645a4fb6556eb50f8fc79550519d','exact native table')
    need(digest(dense)=='15f8b3e96d6adae76236ab0960d288b9537e39294ef1ab65f8fdd2e16dc2a9b6','exact dense table')
    receipt={'status':'CHECKS_PASS_197_STATES_NOT_SUB196','working_states':197,'rows':394,'start':0,'halt':197,'native_start':74,'native_root':84,'native_halt':254,
      'source_sites':len(sites),'baseline_source_sites':len(oldsites),'grammar_readers':len(shape),'simultaneous_folds':len(chosen),
      'unchanged_register_engine_rows':2*len(c.BOXSTATES),'independent_cfg_resolvers_agree':True,'source_graph_no_stray_checks':checks,
      'replaced_blocks':8,'old_block_sites':47,'new_block_sites':18,'old_entries':oldentries,'new_entries':newentries,
      'outside_source_rows_bound':outside,'external_entry_exit_checks':True,'symbolic_loop_certificate':universal,'independent_complete_source_certificate':source_certificate,
      'runtime':runtime,'startup_steps':58154,'whole_startup_tape_exact':True,'graph_reachable_states':197,
      'joint_mask_site_pairs':len(seen),'joint_mask_sha256':digest(json.dumps(sorted(seen),separators=(',',':')).encode()),'scratch_entry_invariants':entry_receipts,
      'native_sha256':digest(native),'dense_sha256':digest(dense),
      'scope':'Executable primitive contracts use inherited unchanged register-block interfaces. The independent local NEG18 source argument is universal via terminating counter loops and exact polynomial identities. No Lean recheck, new PA-internal consistency biconditional, or machine below196 states is claimed.'}
    source=[{'ordinal':i,'path':''.join(map(str,p)),'op':op,'arg':a,'instruction':list(graph[i])}for i,(p,op,a)in enumerate(sites)]
    outputs={'machine.native.tm':native,'machine.tm':dense,'labels.json':compact(labels),'grammar.json':(json.dumps(encode(grammar),indent=2)+'\n').encode(),
             'folds.json':(json.dumps(chosen,indent=2)+'\n').encode(),'source.json':(json.dumps(source,indent=2)+'\n').encode(),'verification.json':(json.dumps(receipt,indent=2)+'\n').encode()}
    for name,data in outputs.items():
        path=HERE/name
        if args.check:need(path.read_bytes()==data,'saved output differs: '+name)
        else:path.write_bytes(data)
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
