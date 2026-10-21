"""Whole-primitive generalized-frame search after certified source rotations.

All negative results are finite search results. Source CFGs and baseline
primitive frames are independently checked before the mutation screen.
"""
from pathlib import Path
import sys,os,json,struct,time,hashlib,subprocess,shutil
import search_rotations as z
sys.path.insert(0,str(z.BASE/'portable/runtime/vendor'))
import independent_runtime as r

OUT=Path(os.environ.get('WHOLE_ROT_OUT',z.PACKET/'regenerated/rotations' if z.PACKAGED else z.ROOT/'whole_rotations'));OUT.mkdir(parents=True,exist_ok=True)
DEFAULT_FIXTURES=z.PACKET/'fixtures/ordinary' if z.PACKAGED else z.ROOT/'whole_primitive'
META=json.loads(Path(os.environ.get('ROT_FRAME_META',DEFAULT_FIXTURES/'frame_metadata.json')).read_text())
WITNESSES=Path(os.environ.get('ROT_WITNESSES',DEFAULT_FIXTURES/'witnesses.txt'))
SOLVER=Path(os.environ.get('ROT_SOLVER',z.ROOT/'whole_primitive_folds'))
if not SOLVER.is_file():
    raise SystemExit('Compile src/whole_primitive_folds.c first, or set ROT_SOLVER to the compiled solver path; see README.md.')
SREF=z.s.sites(z.S0);SZ=512;OFF=128
receipt_path=OUT/'results.json'
results=json.loads(receipt_path.read_text()) if receipt_path.exists() else []
done={x['key'] for x in results};seen=set();start=time.time()
env=os.environ.copy();env.update(GENERAL_FRAMES='1',FRAME_ANCHOR='75')

def tape_bytes(ones):
    tape=bytearray(SZ)
    for x in ones:
        assert 0<=x+OFF<SZ
        tape[x+OFF]=1
    return tape

def write_frames(rows,path):
    with path.open('wb') as out:
        out.write(struct.pack('<3i',len(META),SZ,OFF))
        for m in META:
            i=m['ordinal'];pc,op,arg=rows[i]
            assert [op,arg]==SREF[i][1:]
            regs=m['registers'];spares=m['spares'];initial=r.frame(pc,regs,spares)
            if op=='CH':q,h,ones=254,0,initial
            else:
                e,_=r.expected(rows[i],regs,spares);q,h,ones=84,e[1],e[2]
            out.write(struct.pack('<5i',i,int(m['positive'])|(2 if op=='CI' else 0),q,h+OFF,m['steps']))
            out.write(tape_bytes(initial));out.write(tape_bytes(ones))

def visit(table,tree,chain,depth):
    rows=z.s.sites(tree);tb=z.b.table_bytes(table);sb=z.s.compact(rows)
    key=hashlib.sha256(tb+sb).hexdigest()
    if key in seen:return
    seen.add(key)
    if key not in done:
        assert z.s.graph_arithmetic(rows)[0]==z.CFG0==z.s.graph_intervals(rows)
        (OUT/'current.tm').write_bytes(tb);(OUT/'current.sites.json').write_bytes(sb)
        write_frames(rows,OUT/'current.frames.bin')
        record=dict(key=key,chain=chain,source_sha256=hashlib.sha256(sb).hexdigest(),table_sha256=hashlib.sha256(tb).hexdigest(),screens={})
        for mode in ('pair','sole'):
            args=[str(SOLVER.resolve()),str(OUT/'current.tm'),str(OUT/'current.frames.bin'),str(WITNESSES),str(OUT/'current.hits.txt')]
            if mode=='sole':args.append('sole')
            with (OUT/'current.log').open('w') as log:
                res=subprocess.run(args,stdout=log,stderr=subprocess.STDOUT,env=env)
            lines=(OUT/'current.log').read_text().splitlines()
            hits=(OUT/'current.hits.txt').read_text().splitlines()
            record['screens'][mode]=dict(returncode=res.returncode,summary=lines[-1] if lines else '',hits=hits)
            if hits or res.returncode:
                prefix=OUT/f"case_{len(results):04d}_{mode}"
                prefix.with_suffix('.tm').write_bytes(tb);prefix.with_suffix('.sites.json').write_bytes(sb)
                prefix.with_suffix('.log').write_text('\n'.join(lines)+'\n')
                prefix.with_suffix('.hits.txt').write_text('\n'.join(hits)+'\n')
                print('ATTENTION',mode,prefix.name,record['screens'][mode],flush=True)
        results.append(record);done.add(key);receipt_path.write_text(json.dumps(results,indent=2)+'\n')
        print('TABLE',len(results),'chain',[(x[0],x[1],x[2]) for x in chain], 'seconds',round(time.time()-start,1),flush=True)
    if len(chain)<depth:
        for tag,new_table,new_tree in z.rotations(table,tree):visit(new_table,new_tree,chain+[tag],depth)

visit(z.T0,z.S0,[],int(sys.argv[1]) if len(sys.argv)>1 else 1)
print('DONE',len(seen),'tables_this_traversal',len(results),'total_receipts',time.time()-start,flush=True)
