#!/usr/bin/env python3
"""Fresh portable QA for replay_audit.py. Mutates only its own NEW test workspace."""
import argparse,hashlib,json,os,pathlib,shutil,stat,subprocess,sys,zipfile
P=pathlib.Path
def need(c,m):
    if not c:raise RuntimeError(m)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root):
    values={}
    for p in [root,*sorted(root.rglob('*'))]:
        s=p.lstat();rel=str(p.relative_to(root))
        values[rel]=(s.st_mode,s.st_size,s.st_mtime_ns,s.st_ino,digest(p) if p.is_file() else None)
    return values
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ['packet','audit','adapter','work']:ap.add_argument('--'+name,required=True)
    a=ap.parse_args();packet=P(a.packet);audit=P(a.audit);adapter=P(a.adapter);work=P(a.work)
    need(all(p.is_absolute() for p in [packet,audit,adapter,work]),'absolute paths required')
    need(not work.exists() and not work.is_symlink() and work.parent.is_dir(),'work must be a NEW directory with existing parent')
    need(not (packet==work or audit==work or packet in work.parents or audit in work.parents),'work must be external')
    need(adapter.is_file(),'adapter missing')
    before_packet=snapshot(packet);before_audit=snapshot(audit)
    work.mkdir();fixture=work/'fixture';fixture.mkdir()
    science=fixture/'science';independent=fixture/'independent_audit';replay=fixture/'audit_replay';replay.mkdir()
    shutil.copytree(packet,science);shutil.copytree(audit,independent);shutil.copy2(adapter,replay/'replay_audit.py')
    # Only fixture copies become writable, so QA also accepts read-only release inputs.
    for root in [science,independent]:
        for path in [root,*root.rglob('*')]:path.chmod(0o755 if path.is_dir() else 0o644)
    logs=work/'logs';logs.mkdir();rejections=[]
    exe=str(P(sys.executable).resolve())
    def invoke(args,opt=False,program=None):
        return subprocess.run([exe,'-I','-S',*(['-O'] if opt else []),str(program or adapter),*args],cwd=work,
                              stdin=subprocess.DEVNULL,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=360)
    def common(out,pp=None,aa=None):return ['--packet',str(pp or science),'--audit',str(aa or independent),'--output',str(out)]
    def bad(label,needle,args,out=None):
        result=invoke(args)
        need(result.returncode!=0,'guard admitted '+label)
        need(needle.encode() in result.stderr,'unexpected failure for '+label+': '+result.stderr.decode())
        if out is not None:need(not out.exists() and not out.is_symlink(),'invalid request created output '+label)
        (logs/(label+'.stderr.txt')).write_bytes(result.stderr);rejections.append(label)
    def out(label):return work/('reject-'+label)
    bad('required_arguments','required',[])
    o=out('relative_input');bad('relative_input','absolute',common(o,pp=P('science')),o)
    o=out('missing_input');bad('missing_input','missing path',common(o,pp=work/'absent'),o)
    o=out('file_input');bad('file_input','not a directory',common(o,pp=science/'ARCHITECTURE.md'),o)
    o=out('same_inputs');bad('same_inputs','disjoint',common(o,aa=science),o)
    o=out('swapped_inputs');bad('swapped_inputs','No such file',common(o,pp=independent,aa=science),o)
    o=out('traversal');bad('traversal','parent traversal',common(o,pp=fixture/'x'/'..'/'science'),o)
    link=work/'linked-science';link.symlink_to(science,target_is_directory=True)
    o=out('root_symlink');bad('root_symlink','symlink path',common(o,pp=link),o)
    parentlink=work/'linked-fixture';parentlink.symlink_to(fixture,target_is_directory=True)
    o=out('ancestor_symlink');bad('ancestor_symlink','symlink path',common(o,pp=parentlink/'science'),o)
    def mutate_file(label,path,change,needle):
        old=path.read_bytes();mode=path.stat().st_mode
        try:
            change(path)
            o=out(label);bad(label,needle,common(o),o)
        finally:
            if path.is_symlink():path.unlink()
            path.write_bytes(old);path.chmod(stat.S_IMODE(mode))
    for label,path,needle in [
        ('dag_tamper',science/'evidence/polynomial-dag.json','tampered input'),
        ('science_manifest_tamper',science/'evidence/frozen-manifest.json','science manifest pin'),
        ('checker_tamper',independent/'check_source.py','tampered input'),
        ('receipt_tamper',independent/'source-audit-receipt.json','tampered input'),
        ('audit_manifest_tamper',independent/'audit-manifest.json','audit manifest pin')]:
        mutate_file(label,path,lambda p:p.write_bytes(p.read_bytes()+b' '),needle)
    external=work/'same-architecture';external.write_bytes((science/'ARCHITECTURE.md').read_bytes())
    def link_replace(p):p.unlink();p.symlink_to(external)
    mutate_file('input_file_symlink',science/'ARCHITECTURE.md',link_replace,'not a regular nonsymlink')
    manifestcopy=work/'same-audit-manifest';manifestcopy.write_bytes((independent/'audit-manifest.json').read_bytes())
    def manifest_link(p):p.unlink();p.symlink_to(manifestcopy)
    mutate_file('manifest_symlink',independent/'audit-manifest.json',manifest_link,'not a regular nonsymlink')
    evidence=science/'evidence';hold=work/'held-evidence';evidence.rename(hold);evidence.symlink_to(hold,target_is_directory=True)
    try:
        o=out('input_directory_symlink');bad('input_directory_symlink','symlink path',common(o),o)
    finally:evidence.unlink();hold.rename(evidence)
    missing=science/'ARCHITECTURE.md';hold=work/'held-architecture';missing.rename(hold)
    try:
        o=out('missing_file');bad('missing_file','missing input files',common(o),o)
    finally:hold.rename(missing)
    for label,parent in [('extra_science_file',science),('extra_audit_file',independent)]:
        extra=parent/'unexpected.txt';extra.write_text('unexpected')
        try:
            o=out(label);bad(label,'unmanifested input file',common(o),o)
        finally:extra.unlink()
    extra=science/'unexpected-empty-directory';extra.mkdir()
    try:
        o=out('extra_directory');bad('extra_directory','unmanifested or missing input directories',common(o),o)
    finally:extra.rmdir()
    for label,parent in [('output_inside_science',science),('output_inside_audit',independent)]:
        o=parent/'forbidden-output';bad(label,'external',common(o),o)
    existing=work/'existing-output';existing.mkdir();(existing/'sentinel').write_text('preserve me')
    previous=snapshot(existing);bad('existing_output','already exists',common(existing));need(snapshot(existing)==previous,'existing output changed')
    fileout=work/'existing-file';fileout.write_text('preserve me');original=fileout.read_bytes()
    bad('file_output','not a directory',common(fileout));need(fileout.read_bytes()==original,'file output changed')
    linkedout=work/'linked-output';linkedout.symlink_to(existing,target_is_directory=True)
    bad('output_symlink','symlink path',common(linkedout));need(snapshot(existing)==previous,'symlink target changed')
    linkedparent=work/'linked-parent';linkedparent.symlink_to(existing,target_is_directory=True)
    bad('output_ancestor_symlink','symlink path',common(linkedparent/'new'))
    o=work/'missing-parent'/'new';bad('missing_output_parent','missing path',common(o),o)

    # Archive the pristine-bytes copies, extract manually, then move the entire release.
    archive=work/'portable-release.zip'
    with zipfile.ZipFile(archive,'x',compression=zipfile.ZIP_DEFLATED) as z:
        for p in sorted(fixture.rglob('*')):
            if p.is_file():z.write(p,p.relative_to(fixture).as_posix())
    extracted=work/'extracted';extracted.mkdir()
    with zipfile.ZipFile(archive) as z:
        for info in z.infolist():
            relative=pathlib.PurePosixPath(info.filename)
            need(not relative.is_absolute() and '..' not in relative.parts,'unsafe archive member')
            target=extracted/relative;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(z.read(info))
    moveparent=work/'moved elsewhere';moveparent.mkdir();moved=moveparent/'read only extracted release';extracted.rename(moved)
    ms=moved/'science';ma=moved/'independent_audit';mp=moved/'audit_replay/replay_audit.py'
    need(digest(mp)==digest(adapter),'adapter archive byte drift')
    for root in [ms,ma]:
        for p in root.rglob('*'):
            if p.is_file():p.chmod(0o444)
        for p in sorted([root,*[p for p in root.rglob('*') if p.is_dir()]],key=lambda p:len(p.parts),reverse=True):p.chmod(0o555)
    ms_before=snapshot(ms);ma_before=snapshot(ma);positive=[]
    for label,opt in [('normal_adapter',False),('optimized_adapter',True)]:
        output=work/label
        result=invoke(common(output,pp=ms,aa=ma),opt=opt,program=mp)
        (logs/(label+'.stdout.json')).write_bytes(result.stdout);(logs/(label+'.stderr.txt')).write_bytes(result.stderr)
        need(result.returncode==0 and not result.stderr,'valid moved replay failed: '+result.stderr.decode())
        receipt=(output/'replay-receipt.json').read_bytes();need(result.stdout==receipt,'stdout/receipt mismatch')
        need(json.loads(receipt)['status']=='PASS','replay did not pass')
        outputmanifest=json.loads((output/'replay-manifest.json').read_text())
        for f in outputmanifest['files']:
            p=output/f['path'];need(p.stat().st_size==f['bytes'] and digest(p)==f['sha256'],'output manifest drift')
        positive.append(receipt)
    need(positive[0]==positive[1],'normal/optimized adapter receipt drift')
    need(snapshot(ms)==ms_before and snapshot(ma)==ma_before,'readonly extracted inputs changed')
    need(snapshot(packet)==before_packet and snapshot(audit)==before_audit,'original input changed')
    result={'status':'PASS','adapter_sha256':digest(adapter),'rejection_cases':rejections,'rejection_count':len(rejections),
            'valid_replays':['moved_zip_extracted_readonly_normal_adapter','moved_zip_extracted_readonly_optimized_adapter'],
            'both_independent_checkers_run_normal_and_optimized_per_replay':True,'all_core_receipts_match_frozen_bytes':True,
            'portable_replay_receipt_sha256':hashlib.sha256(positive[0]).hexdigest(),'moved_readonly_inputs_preserved':True,
            'original_science_and_audit_bytes_modes_mtimes_preserved':True,'author_or_upstream_code_executed':False,
            'saved_accepting_schedules_executed':False}
    data=(json.dumps(result,sort_keys=True,indent=2)+'\n').encode();(work/'qa-receipt.json').write_bytes(data);sys.stdout.buffer.write(data)
if __name__=='__main__':main()
