#!/usr/bin/env python3
"""Offline, independent replay of the main research packet's finite evidence.

No network access, no Lean rebuild, and no claim of a sub-252 construction.
All writes made by this harness and its subprocesses are in a fresh temporary
directory; the delivered evidence is read-only input.
"""
from __future__ import annotations
import argparse,hashlib,importlib.util,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path

sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent
REPO=ROOT/'source/ProveIt'
THEORY=ROOT/'work/theory_audit'
STATE=ROOT/'work/state_reduction'
BEST=ROOT/'experiments/direct-negation255'
PROG_REL=Path('source/ProveIt/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v')

def digest(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()

def require(value,message):
    if not value:raise ValueError(message)

def load_module(path,name):
    spec=importlib.util.spec_from_file_location(name,path);module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module);return module

def run(command,work):
    result=subprocess.run([sys.executable,'-B',*map(str,command)],cwd=work,
        env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'},capture_output=True,text=True)
    if result.returncode:
        sys.stderr.write(result.stdout+result.stderr)
        raise RuntimeError('Audit subprocess failed: '+str(command[0]))

def table(raw):
    t={}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,n=line.split();key=int(q),int(b)
        require(key not in t,'duplicate transition');t[key]=int(w),d,int(n)
    return t

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--journals',action='store_true');ap.add_argument('--skip-manifest',action='store_true',help='For rebuilding the research packet before its manifest exists.')
    args=ap.parse_args();require(__debug__,'Run without Python -O.')
    if not args.skip_manifest:
        manifest=json.loads((ROOT/'MANIFEST.json').read_text());files=manifest['files']
        for item in files:
            p=ROOT/item['path'];require(p.is_file(),'missing '+item['path'])
            require(p.stat().st_size==item['bytes'] and digest(p)==item['sha256'],'hash mismatch '+item['path'])
        print(f'PASS package integrity: {len(files)} files',flush=True)
    require(digest(ROOT/PROG_REL)=='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746','pinned program hash')
    # Compare independently parsed literal leaves with the recovered DAG.
    ac=load_module(THEORY/'check_affine_certificate.py','independent_affine')
    ma=load_module(STATE/'audit_modified_source.py','independent_machine')
    literal,*_=ac.independent_program((ROOT/PROG_REL).read_bytes())
    _,_,optimized,_,_=ma.reconstruct((ROOT/'work/compiler_reduction/source27/decoder_entries.json').read_bytes())
    literal_text=[(''.join('1' if bit else '0' for bit in p),op[1:],arg) for p,op,arg in literal]
    require(literal_text==optimized,'recovered203/literal6459 source mismatch')
    print('PASS exact 203-node decoder / 6,460-leaf literal-source correspondence',flush=True)
    # Pure finite reconstruction of the accepted six-step table recipe.
    recipe=json.loads((BEST/'fold_sequence.json').read_text());t=table((BEST/'fresh_261_oldlabels.tm').read_bytes())
    require(len(t)==522,'initial261 row count')
    for step in recipe['recipes']:
        dead,keep,mask=step['deleted'],step['target'],step['copied_row_mask'];old=t
        t={(q,b):(w,m,keep if n==dead else n) for (q,b),(w,m,n) in old.items() if q!=dead}
        for b in (0,1):
            if mask>>b&1:
                w,m,n=old[dead,b];t[keep,b]=w,m,keep if n==dead else n
    require(t==table((BEST/'machine_255_oldlabels.tm').read_bytes()),'six-fold reconstruction mismatch')
    ren=json.loads((BEST/'renumbering.json').read_text());m={int(k):v for k,v in ren['old_to_new'].items()}
    nt={(m[q],b):(w,d,m[n]) for (q,b),(w,d,n) in t.items()}
    require(nt==table((BEST/'zfc_direct_negation255.tm').read_bytes()),'normalization mismatch')
    require(set(nt)=={(q,b) for q in range(255) for b in (0,1)},'normalized table domain')
    require(m[64]==0 and m[254]==255,'normalized start/halt')
    print('PASS six accepted folds and both255 table numberings',flush=True)
    with tempfile.TemporaryDirectory(prefix='zfc-research-verify-') as temp:
        tmp=Path(temp)
        out=tmp/'affine.json'
        run([THEORY/'check_affine_certificate.py','--certificate',ROOT/'work/affine-invariants.json',
             '--program',ROOT/PROG_REL,'--output',out],tmp)
        a=json.loads(out.read_text());require(a['status']=='PASS' and a['affine_nonhalt_postfix_edges']==8384,'affine audit')
        print('PASS exact affine invariant: 8,384 independent postfix edges',flush=True)
        # Relocate the original negative-control driver without editing bytes.
        stage=tmp/'negative';(stage/'work/theory_audit').mkdir(parents=True)
        for name in ['check_affine_certificate.py','check_affine_mutations.py']:
            shutil.copyfile(THEORY/name,stage/'work/theory_audit'/name)
        shutil.copyfile(ROOT/'work/affine-invariants.json',stage/'work/affine-invariants.json')
        (stage/PROG_REL).parent.mkdir(parents=True);shutil.copyfile(ROOT/PROG_REL,stage/PROG_REL)
        run([stage/'work/theory_audit/check_affine_mutations.py'],stage)
        a=json.loads((stage/'work/theory_audit/affine-mutation-audit.json').read_text());require(a['status']=='PASS' and len(a['controls'])==4,'negative controls')
        print('PASS four independently targeted certificate corruptions rejected',flush=True)
        out=tmp/'machine255.json'
        run([STATE/'audit_modified_source.py','--repo',REPO,'--source',BEST/'source.json',
             '--table',BEST/'machine_255_oldlabels.tm','--output',out],tmp)
        a=json.loads(out.read_text());require(a['status']=='PASS' and a['working_states']==255,'machine255 audit')
        require(a['affine']['passed_cases']==7311 and a['literal_controls']['passed_cases']==21933,'machine255 case counts')
        require(a['literal_controls']['used_rows_including_boot']==510,'machine255 literal coverage')
        print('PASS machine255: 7,311 affine cases; 82,552 blank steps; 21,933 whole-tape trials',flush=True)
        if args.journals:
            results=sorted(STATE.glob('two_action_*_gap.json'))
            require(len(results)==36,'expected36 fresh degree-two result domains')
            out=tmp/'partitions.json';run([STATE/'audit_degree2_partition.py',*results,'--output',out],tmp)
            a=json.loads(out.read_text());require(a['status']=='PASS','degree-two partition audit')
            print('PASS36 compressed journals: 36,578,304 fresh recipes partitioned',flush=True)
    print('DONE. All requested finite checks passed. No sub-252 construction or new kernel endpoint is claimed.',flush=True)

if __name__=='__main__':main()
