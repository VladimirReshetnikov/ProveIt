#!/usr/bin/env python3
"""Replay the complete positive certificates, without network or proof assistants.

This is an ordinary mathematical certificate checker, not a Lean/Rocq kernel
endpoint. Large bounded optimization searches have separate replay commands.
No reference or candidate artifact is modified; --output is optional.
"""
from __future__ import annotations
import argparse,hashlib,json,sys,time
from pathlib import Path

ROOT=Path(__file__).resolve().parent
sys.path[:0]=[str(ROOT/'code/grammar'),str(ROOT/'code/proof'),str(ROOT/'reference/context246/code')]
import search246 as compiler
import rotate_search
import plateau_search
import leaf_cfg
import audit_guard_transport
import verify_blank
import check_macro_inductions as macro

def require(test,message):
    if not test:raise ValueError(message)

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def read_table(path):
    return {(str(q),b):(w,'L' if m<0 else 'R',str(t))
            for (q,b),(w,m,t) in verify_blank.read_table(path).items()}

class Tracked(dict):
    def __init__(self,T):super().__init__(T);self.used=set()
    def __getitem__(self,k):self.used.add(k);return super().__getitem__(k)

def macro_certificate(T):
    macro.TABLE=Tracked({(int(q),b):(w,m,int(t))for(q,b),(w,m,t)in T.items()})
    macro.BLOCK_PROOFS={};macro.DERIVED={};macro.WORD_IDENTITY_PROVED=False
    macro.prove_blocks();word=macro.prove_word_identity()
    operations=macro.prove_macros();marks=macro.prove_marks()
    rows={(str(q),b)for q,b in macro.TABLE.used}
    require(len(rows)==42,'Unexpected macro support')
    return rows,dict(status='PASS',block_inductions=len(macro.BLOCK_PROOFS),register_operations=len(operations),selectors=len(marks),literal_support_rows=len(rows),word_identity=word)

def check_manifest(path):
    if not path.exists():return None
    count=0
    for line in path.read_text().splitlines():
        if not line:continue
        wanted,name=line.split('  ',1);p=path.parent/name
        require(p.is_file(),f'Missing manifest file {name}')
        require(digest(p)==wanted,f'Manifest mismatch {name}');count+=1
    return count

def main():
    if not __debug__:raise SystemExit('Assertions are required; do not run with -O.')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path)
    ap.add_argument('--skip-manifest',action='store_true',help='For deliberate local edits only; skips top-level archive hashes.')
    a=ap.parse_args();begin=time.monotonic()
    result=dict(status='PASS',proof_status='Ordinary mathematical certificates; no new kernel endpoint',candidates=[])
    if not a.skip_manifest:result['manifest_files']=check_manifest(ROOT/'SHA256SUMS')
    result['reference_manifest_files']=check_manifest(ROOT/'reference/context246/SHA256SUMS')
    source=audit_guard_transport.parse_source(ROOT/'reference/context246/sources/Prog254.v')
    require(source.sites==compiler.sites(compiler.NODES,compiler.ROOT),'Decoder metadata differs from literal source')
    result['source_program_sha256']=audit_guard_transport.PIN
    product=json.loads((ROOT/'reference/guard-invariant/product-invariant.json').read_text())
    result['product_invariant']=audit_guard_transport.check_product(product,audit_guard_transport.cases(source))
    options=rotate_search.options(compiler.NODES)
    for index in (0,233,235,236,237):
        folder=ROOT/f'candidates/layout{index}';saved=json.loads((folder/'program.json').read_text())
        node,exp,kind=options[index];nodes,root=rotate_search.mutate(compiler.NODES,compiler.ROOT,node,exp)
        nn={int(k):tuple(map(tuple,v))for k,v in saved['nodes'].items()}
        require((nodes,root)==(nn,saved['root']),f'Rotation reconstruction differs: {index}')
        sites=compiler.sites(nodes,root)
        require(sites==[tuple(x)for x in saved['sites']],f'Saved sites differ: {index}')
        require(sites==[tuple(x)for x in json.loads((folder/'sites.json').read_text())],f'Site list differs: {index}')
        graph=leaf_cfg.Program(sites)
        mapping=dict(zip(sorted(source.by_address),sorted(graph.by_address)))
        cfg=leaf_cfg.check_map(source,graph,mapping)
        require(cfg['status']=='PASS',f'Source CFG rejected: {index}')
        require(cfg==json.loads((folder/'source-map-certificate.json').read_text()),f'CFG certificate differs: {index}')
        outcome=compiler.evaluate(nodes,root)
        require(outcome['outcome']=='PASS',f'Universal instructions rejected: {index}')
        live=set(outcome['used']);T=read_table(folder/'machine_old.tm')
        require(len(live)==246 and len(T)==492,f'State count differs: {index}')
        require(set(T)=={(q,b)for q in live for b in (0,1)},f'Pruned state set differs: {index}')
        require(all(outcome['table'][key]==row for key,row in T.items()),f'Literal emitter differs: {index}')
        macro_rows,macro_result=macro_certificate(T)
        affine_rows=set(map(tuple,outcome['rows_used']))
        require(macro_rows|affine_rows==set(T),f'Runtime support differs: {index}')
        require(all(T[key]==compiler.BASE246[key]for key in macro_rows),f'Macro row changed: {index}')
        reach=plateau_search.reach(T);bisim=plateau_search.minimize(T,reach)
        require(len(reach)==246 and bisim==246,f'Unexpected exact quotient: {index}')
        entry=dict(layout=index,status='PASS',working_states=246,binary_rows=492,source_leaves=6460,source_guarded_cases=cfg['guarded_cases'],universal_instruction_cases=outcome['symbolic_cases'],macro_certificate=macro_result,affine_support_rows=len(affine_rows),full_support_rows=len(macro_rows|affine_rows),bisimulation_classes=bisim,table_old_sha256=digest(folder/'machine_old.tm'),blank_initializer='not supplied')
        if index in (0,233):
            boot=json.loads((folder/'bootstrap.json').read_text())
            hit=dict(start=boot['start'],steps=boot['steps'],state=boot['dispatcher'],head=boot['head'],header=boot['header'],values=boot['physical_primaries']+boot['spare_values'],logical=boot['logical_primaries'])
            ints=verify_blank.read_table(folder/'machine_old.tm');proof=verify_blank.verify(ints,hit)
            require(json.loads(json.dumps(proof))=={k:v for k,v in boot.items()if k!='old_table_sha256'},f'Complete bootstrap differs: {index}')
            require(boot['old_table_sha256']==entry['table_old_sha256'],f'Bootstrap table binding differs: {index}')
            canonical,renumber=verify_blank.canonical(ints,95)
            require(canonical==(folder/'machine.tm').read_text(),f'Canonical table differs: {index}')
            require(renumber=={int(k):v for k,v in json.loads((folder/'renumbering.json').read_text()).items()},f'Renumbering differs: {index}')
            require(proof['logical_primaries']==[3,0,0,0,3,0,0,0,0],f'Unexpected logical root: {index}')
            entry.update(blank_initializer='PASS',blank_steps=proof['steps'],distance=proof['distance'],spare_count=len(proof['spare_values']),complete_one_count=proof['one_count'],canonical_sha256=digest(folder/'machine.tm'))
        result['candidates'].append(entry)
        print(f"layout {index}: 246 states, 8391 universal cases, source CFG, macros, full support; blank {entry['blank_initializer']}",file=sys.stderr,flush=True)
    result['seconds']=time.monotonic()-begin
    payload=json.dumps(result,indent=2)+'\n'
    if a.output:a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(payload)
    print(payload,end='')

if __name__=='__main__':main()
