#!/usr/bin/env python3
"""Fresh portability adversaries. Run only inspected adapter/pinned independent checkers.
All mutation is confined to newly created test copies, never original sources.
"""
import argparse,hashlib,json,os,shutil,stat,subprocess,sys,tempfile
from pathlib import Path

def require(ok,message):
    if not ok:raise RuntimeError(message)

def snapshot(root):
    d={}
    for p in [root,*sorted(root.rglob('*'))]:
        s=p.lstat();row=[stat.S_IMODE(s.st_mode),s.st_size,s.st_mtime_ns,s.st_ctime_ns,s.st_ino,s.st_dev,s.st_uid,s.st_gid]
        if p.is_symlink():row+=['symlink',os.readlink(p)]
        elif p.is_file():row+=['file',hashlib.sha256(p.read_bytes()).hexdigest()]
        else:row+=['directory']
        d[str(p.relative_to(root))]=row
    return d

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ('packet-dir','audit-dir','adapter','receipt'):ap.add_argument('--'+name,required=True)
    a=ap.parse_args();packet=Path(a.packet_dir);audit=Path(a.audit_dir);adapter=Path(a.adapter)
    before_original=[snapshot(packet),snapshot(audit)]
    root=Path(tempfile.mkdtemp(prefix='report58-portability-tests-'))
    p=root/'relocated corpus with spaces'/'packet';q=root/'relocated corpus with spaces'/'audit'
    p.parent.mkdir();shutil.copytree(packet,p);shutil.copytree(audit,q)
    cases=[]
    def invoke(name,pval=None,qval=None,outval=None,flags=None,env=None,expect=True,extras=None):
        pp=str(p) if pval is None else str(pval);qq=str(q) if qval is None else str(qval)
        out=root/('out-'+name) if outval is None else Path(outval)
        command=[sys.executable,*(flags if flags is not None else ['-I','-S','-B']),str(adapter),
                 '--packet-dir',pp,'--audit-dir',qq,'--output-dir',str(out)]
        if extras:command+=extras
        snap=[snapshot(p),snapshot(q)]
        out_existed=os.path.lexists(out)
        before_out=snapshot(out) if out.is_dir() and not out.is_symlink() else None
        proc=subprocess.run(command,cwd=root,env=env,stdin=subprocess.DEVNULL,capture_output=True,text=True,timeout=120)
        passed=proc.returncode==0
        require(passed==expect,f'{name}: expected success={expect}, got {proc.returncode}: {proc.stderr}')
        require(snap==[snapshot(p),snapshot(q)],name+': relocated baseline sources changed')
        if before_out is not None:require(snapshot(out)==before_out,name+': existing output changed')
        if expect:
            report=json.loads((out/'REPLAY_RECEIPT.json').read_text())
            require(report['status']=='PASS' and report['original_inputs_preserved'],name+': missing pass/preservation')
            require(report['replay']['isolation']=={'isolated':1,'no_site':1,'optimize':0,'dont_write_bytecode':True},name+': isolation wrong')
            for result in ('exact-source-receipt.json','POWER_DAG_RECEIPT.json','arithmetic-receipt.json','full-positive-witnesses.json'):
                require((out/'results'/result).read_bytes()==(audit/result).read_bytes(),name+': exact receipt mismatch')
            require((out/'audit_arithmetic.py.stdout.txt').read_bytes()==(audit/'arithmetic-run.stdout.json').read_bytes(),name+': stdout mismatch')
        else:
            if not out_existed:require(not out.exists(),name+': invalid preflight created output')
        cases.append({'case':name,'expected':'PASS' if expect else 'REFUSE','returncode':proc.returncode,
                      'passed':True,'stderr':proc.stderr.strip()[:500]})
        return out
    first=invoke('relocated-spaces')
    invoke('output-reuse',outval=first,expect=False)
    # Pure read-only source copies; permission modes must stay unchanged.
    for tree in (p,q):
        for item in tree.rglob('*'):
            item.chmod(0o555 if item.is_dir() else 0o444)
        tree.chmod(0o555)
    invoke('readonly-relocated')
    polluted=root/'import-traps';polluted.mkdir();marker=root/'IMPORT_TRAP_EXECUTED'
    trap="from pathlib import Path\nPath("+repr(str(marker))+").write_text('bad')\nraise RuntimeError('import trap')\n"
    (polluted/'sitecustomize.py').write_text(trap);(polluted/'json.py').write_text(trap)
    polluted_env=dict(os.environ,PYTHONPATH=str(polluted),PYTHONOPTIMIZE='2',PYTHONDONTWRITEBYTECODE='0',PYTHONSTARTUP=str(polluted/'sitecustomize.py'))
    invoke('isolated-polluted-environment',env=polluted_env)
    require(not marker.exists(),'isolated invocation loaded an import trap')
    invoke('optimized-O',flags=['-I','-S','-B','-O'],expect=False)
    invoke('optimized-OO',flags=['-I','-S','-B','-OO'],expect=False)
    invoke('missing-isolation',flags=['-S','-B'],expect=False)
    invoke('missing-no-site',flags=['-I','-B'],expect=False)
    invoke('missing-no-bytecode',flags=['-I','-S'],expect=False)
    invoke('relative-input',pval='relative/packet',expect=False)
    invoke('missing-input',pval=root/'does-not-exist',expect=False)
    invoke('dotdot-input',pval=str(p.parent)+'/../'+p.parent.name+'/packet',expect=False)
    invoke('trailing-slash-input',pval=str(p)+'/',expect=False)
    invoke('double-leading-slash',pval='/'+str(p),expect=False)
    invoke('same-inputs',qval=p,expect=False)
    invoke('nested-output',outval=p/'new-results',expect=False)
    invoke('relative-output',outval=Path('relative-results'),expect=False)
    invoke('missing-output-parent',outval=root/'missing-parent'/'results',expect=False)
    existing=root/'existing-output-file';existing.write_text('keep')
    invoke('output-file',outval=existing,expect=False);require(existing.read_text()=='keep','output file changed')
    link=root/'packet-link';link.symlink_to(p,target_is_directory=True)
    invoke('input-root-symlink',pval=link,expect=False)
    ancestor=root/'ancestor-link';ancestor.symlink_to(p.parent,target_is_directory=True)
    invoke('input-ancestor-symlink',pval=ancestor/'packet',expect=False)
    outlink=root/'output-link';outlink.symlink_to(root/'nonexistent')
    invoke('dangling-output-symlink',outval=outlink,expect=False)
    output_parent_link=root/'output-parent-link';output_parent_link.symlink_to(root,target_is_directory=True)
    invoke('output-ancestor-symlink',outval=output_parent_link/'new',expect=False)
    # Independent writable mutations copied afresh from authenticated originals.
    def mutated(name,which,change):
        destination=root/('mutant-'+name);shutil.copytree(packet if which=='packet' else audit,destination)
        change(destination)
        frozen=snapshot(destination)
        invoke(name,pval=destination if which=='packet' else None,qval=destination if which=='audit' else None,expect=False)
        require(snapshot(destination)==frozen,name+': refused input was modified')
    def append_file(tree,rel):
        with (tree/rel).open('a') as f:f.write('\n')
    mutated('tampered-science','packet',lambda tree:append_file(tree,'PROOF.md'))
    mutated('tampered-DAG','packet',lambda tree:append_file(tree,'evidence/three-input-linear.dag.json'))
    mutated('tampered-checker','audit',lambda tree:append_file(tree,'audit_exact_source.py'))
    mutated('tampered-reference-receipt','audit',lambda tree:append_file(tree,'arithmetic-receipt.json'))
    mutated('missing-pinned-file','packet',lambda tree:(tree/'PROOF.md').unlink())
    mutated('extra-file','packet',lambda tree:(tree/'extra.txt').write_text('unexpected'))
    mutated('extra-empty-directory','packet',lambda tree:(tree/'extra').mkdir())
    def symlink_file(tree):
        (tree/'PROOF.md').unlink();(tree/'PROOF.md').symlink_to(packet/'PROOF.md')
    mutated('symlink-file','packet',symlink_file)
    def symlink_directory(tree):
        shutil.rmtree(tree/'sources');(tree/'sources').symlink_to(packet/'sources',target_is_directory=True)
    mutated('symlink-directory','packet',symlink_directory)
    # Missing required argument: argparse must refuse and make no output.
    proc=subprocess.run([sys.executable,'-I','-S','-B',str(adapter)],cwd=root,capture_output=True,text=True)
    require(proc.returncode!=0,'missing arguments accepted')
    cases.append({'case':'missing-required-arguments','expected':'REFUSE','returncode':proc.returncode,'passed':True})
    require(before_original==[snapshot(packet),snapshot(audit)],'original frozen sources changed')
    receipt={'status':'PASS','adapter_sha256':hashlib.sha256(adapter.read_bytes()).hexdigest(),
      'test_harness_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
      'case_count':len(cases),'cases':cases,'original_frozen_inputs_preserved':True,
      'relocated_readonly_inputs_preserved':True,'import_trap_executed':False,
      'exact_regenerated_receipts_verified':True,'test_workspace':str(root),
      'limits':'No hostile concurrent filesystem-writer test or OS/network sandbox claim. Isolated Python plus authenticated trusted checkers and read-only private copies.'}
    target=Path(a.receipt);require(not target.exists(),'test receipt path must be fresh');target.write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'PASS','cases':len(cases),'receipt':str(target),'workspace':str(root)},sort_keys=True))
if __name__=='__main__':main()
