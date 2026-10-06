"""Replay finite checks, selected mutations, immutable builds, and archive round trips."""
import sys
sys.dont_write_bytecode=True
import argparse,hashlib,json,os,shutil,subprocess,tempfile,zipfile
from pathlib import Path
from check import ROOT,FILES,require,integrity
from package import seal,pack
from build import build
from safe_output import preflight,write_new

def hashes(root):
    return {p.relative_to(root).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in root.rglob('*') if p.is_file()}

def run(cmd,cwd,expected=0):
    cp=subprocess.run(cmd,cwd=cwd,capture_output=True,text=True,timeout=180)
    if expected==0:require(cp.returncode==0,cp.stdout+'\n'+cp.stderr)
    else:require(cp.returncode!=0,'mutation escaped: '+repr(cmd))
    return cp.stdout.strip()

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True,help='QA receipt outside the immutable bundle')
    args=p.parse_args()
    args.output=preflight(args.output,ROOT)
    integrity();before=hashes(ROOT);receipts=[]
    with tempfile.TemporaryDirectory(prefix='report132-qa-') as tmp:
        temp=Path(tmp)
        work=temp/'copy';shutil.copytree(ROOT,work)
        for opt in [[],['-O']]:
            receipts.append(run([sys.executable,'-B',*opt,'check.py'],work))
            run([sys.executable,'-B',*opt,'derive_general.py','0'],work)
            run([sys.executable,'-B',*opt,'derive_general.py','-1'],work,expected=1)
        run([sys.executable,'-B','derive.py'],work)
        diagnostic=json.loads(run([sys.executable,'-B','validate.py','--max-n','100'],work))
        saved=json.loads((work/'diagnostics_3200.json').read_text())
        for current in diagnostic['checks']:
            prior=next(v for v in saved['checks'] if v['n']==current['n'])
            for key in current:
                require(current[key]==prior[key],'stored diagnostic mismatch: '+key)
        receipts.append('PASS direct symbolic script and stored numerical diagnostics through n=100')
        require(hashes(work)==before,'finite checks changed the copy')
        mutations=[('fixture','fixtures.json','"344"','"345"',True),
                   ('coefficient','formulas.py','167*L**3','168*L**3',True),
                   ('recurrence','exact.py','(2*k+1)*B[k]','(2*k+2)*B[k]',True),
                   ('hash','sources.md','# Sources','# Changed sources',False)]
        for label,name,old,new,reseal in mutations:
            victim=temp/('mutation-'+label);shutil.copytree(ROOT,victim)
            source=(victim/name).read_text();require(old in source,'mutation target missing '+label)
            (victim/name).write_text(source.replace(old,new,1))
            if reseal:seal(victim)
            for opt in [[],['-O']]:run([sys.executable,'-B',*opt,'check.py'],victim,expected=1)
            receipts.append('PASS selected mutation: '+label+' (normal and -O)')
        for kind in ['empty_directory','fifo','nested_fifo','symlink']:
            victim=temp/('inventory-'+kind);shutil.copytree(ROOT,victim)
            if kind=='empty_directory':(victim/'extra').mkdir()
            elif kind=='fifo':os.mkfifo(victim/'extra')
            elif kind=='nested_fifo':
                (victim/'extra').mkdir();os.mkfifo(victim/'extra'/'MANIFEST.json')
            else:(victim/'extra').symlink_to(temp/'nonexistent')
            for opt in [[],['-O']]:run([sys.executable,'-B',*opt,'check.py','--integrity-only'],victim,expected=1)
            receipts.append('PASS inventory rejection: '+kind+' (normal and -O)')
        existing=temp/'existing';existing.write_text('preserve')
        linked=temp/'symlink-parent';linked.symlink_to(temp,target_is_directory=True)
        broken=temp/'broken-output';broken.symlink_to(temp/'missing-target')
        for script in ['build.py','package.py','qa.py']:
            targets=[work/'README.md',work/'new-output',existing,linked/'output',broken]
            for target in targets:
                for opt in [[],['-O']]:
                    run([sys.executable,'-B',*opt,script,'--output',str(target)],work,expected=1)
            require(existing.read_text()=='preserve','existing output was changed')
            require(hashes(work)==before,'output-path rejection changed source copy')
            receipts.append('PASS output guards: '+script+' (normal and -O)')
        victim=temp/'mutation-inventory';shutil.copytree(ROOT,victim)
        (victim/'unexpected.txt').write_text('unexpected payload')
        for opt in [[],['-O']]:run([sys.executable,'-B',*opt,'check.py'],victim,expected=1)
        receipts.append('PASS selected mutation: added inventory file (normal and -O)')
        # Build from the immutable copy, never from a different source tree.
        first=temp/'build-one.pdf';second=temp/'build-two.pdf'
        run([sys.executable,'-B','build.py','--output',str(first)],work)
        run([sys.executable,'-B','build.py','--output',str(second)],work)
        require(first.read_bytes()==second.read_bytes(),'clean PDF builds differ')
        require(first.read_bytes()==(ROOT/'Report132.pdf').read_bytes(),'rebuilt PDF differs from supplied PDF')
        require(hashes(work)==before,'PDF builds changed source copy')
        receipts.append('PASS two clean byte-identical PDF builds matching supplied PDF')
        archive=temp/'first.zip';pack(archive)
        extracted=temp/'extract';extracted.mkdir()
        with zipfile.ZipFile(archive) as z:z.extractall(extracted)
        replay=extracted/'Report132_bundle'
        require(hashes(replay)==before,'fresh archive inventory differs')
        for opt in [[],['-O']]:run([sys.executable,'-B',*opt,'check.py'],replay)
        rebuilt=temp/'replay.pdf';run([sys.executable,'-B','build.py','--output',str(rebuilt)],replay)
        require(rebuilt.read_bytes()==first.read_bytes(),'fresh archive PDF replay differs')
        repacked=temp/'second.zip';run([sys.executable,'-B','package.py','--output',str(repacked)],replay)
        require(repacked.read_bytes()==archive.read_bytes(),'archive repack differs')
        require(hashes(replay)==before,'fresh replay changed extracted inputs')
        receipts.append('PASS fresh ZIP extraction, finite checks, PDF rebuild, and byte-identical repack')
        require(hashes(ROOT)==before,'original bundle changed during QA')
        receipts.append('PASS original, immutable copy, and extracted inputs unchanged')
    write_new(args.output,(json.dumps({'status':'PASS','scope':'Finite checks and reproducibility only; does not certify the analytic proof or effective onset.','receipts':receipts,'pdf_sha256':before['Report132.pdf'],'files':len(before),'python':sys.version.split()[0]},indent=2)+'\n').encode(),ROOT)
    print('\n'.join(receipts))
if __name__=='__main__':main()
