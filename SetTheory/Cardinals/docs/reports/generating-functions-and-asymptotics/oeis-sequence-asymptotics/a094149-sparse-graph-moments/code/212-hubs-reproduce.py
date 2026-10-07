#!/usr/bin/env python3
"""Rebuild Report212 exact data, PDF and deterministic ZIP without network access."""
import argparse, ast, hashlib, json, os, shutil, subprocess, sys, zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
ADDITIONAL=['Report212.tex','reproduce.py','README.txt','requirements.txt','SOURCES.txt']
PDF='Report212.pdf'
MANIFEST='MANIFEST.json'

def require(ok,message):
    if not ok: raise RuntimeError('CHECK_FAILED[package]: '+message)

def sha(data): return hashlib.sha256(data).hexdigest()

def read_json_unique(path):
    def object_pairs(pairs):
        result={}
        for key,value in pairs:
            require(key not in result,'duplicate JSON key '+str(key))
            result[key]=value
        return result
    return json.loads(path.read_text(),object_pairs_hook=object_pairs)

def write_json(path,value):
    path.write_text(json.dumps(value,indent=2,sort_keys=True)+'\n',encoding='utf-8')

def run(cmd,cwd,log,env=None):
    result=subprocess.run(cmd,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    log.write_text(result.stdout,encoding='utf-8')
    require(result.returncode==0,'command failed; inspect '+str(log))
    return result.stdout

def source_names():
    names=(ROOT/'CODE_INVENTORY.txt').read_text().splitlines()+ADDITIONAL
    require(len(names)==len(set(names)),'duplicate source inventory entries')
    for name in names:
        require(name and not Path(name).is_absolute() and '..' not in Path(name).parts,'unsafe source inventory path')
        require((ROOT/name).is_file() and not (ROOT/name).is_symlink(),'missing or linked source member '+name)
        if name.endswith('.py'):
            require(not any(isinstance(n,ast.Assert) for n in ast.walk(ast.parse((ROOT/name).read_text()))),'assert statement in '+name)
    return sorted(names)

def verify_manifest(root,names):
    obj=read_json_unique(root/MANIFEST)
    require(obj.get('format')=='Report212 SHA256 manifest v1','manifest format')
    require(set(obj.get('files',{}))==set(names),'manifest inventory mismatch')
    for name in names:
        require(obj['files'][name]==sha((root/name).read_bytes()),'manifest byte mismatch '+name)

def make_pdf(stage,logs):
    env=os.environ.copy();env.update(SOURCE_DATE_EPOCH='1791072000',FORCE_SOURCE_DATE='1',TZ='UTC',LC_ALL='C')
    # Always use a private format and explicit installed font maps.
    dist=Path(run(['kpsewhich','-var-value=TEXMFDIST'],stage,logs/'texdist.log',env).strip())
    require(dist.is_dir(),'installed TeX tree missing')
    trees=[dist];sibling=dist.parent.parent/'texmf'
    if sibling.is_dir():trees.append(sibling)
    env['TEXMF']='{'+','.join(map(str,trees))+'}'
    env['TEXFORMATS']=str(stage)+os.pathsep
    run(['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','pdflatex.ini'],stage,logs/'format.log',env)
    require((stage/'pdflatex.fmt').is_file(),'private format missing')
    maps=[]
    for name in ['cm.map','cmextra.map','latxfont.map','symbols.map','euler.map','lm.map']:
        path=Path(run(['kpsewhich',name],stage,logs/(name+'.log'),env).strip())
        require(path.is_file(),'font map missing '+name);maps.append(path.read_bytes())
    (stage/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n')
    previous=None;stable=False
    for i in range(1,7):
        run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','Report212.tex'],stage,logs/f'latex{i}.log',env)
        current=(stage/PDF).read_bytes()
        if i>=3 and current==previous:stable=True;break
        previous=current
    require(stable,'PDF did not reach byte stability')
    latex=(logs/f'latex{i}.log').read_text()
    for phrase in ['Overfull \\hbox','Overfull \\vbox','undefined references','undefined citations']:
        require(phrase not in latex,'TeX diagnostic '+phrase)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--quick',action='store_true',help='Read fixture32; do not regenerate public256 table')
    ap.add_argument('--initialize',action='store_true',help='Authoring only: allow missing PDF/manifest baselines')
    ap.add_argument('--self-test-failure',action='store_true',help='Intentionally fail before any output writes')
    args=ap.parse_args()
    if args.self_test_failure:require(False,'intentional failure before writes')
    out=args.out.resolve()
    require(out!=ROOT and ROOT not in out.parents and out not in ROOT.parents,'output must be outside the source tree')
    require(not out.exists(),'output already exists; choose a fresh directory')
    names=source_names();members=names+[PDF]
    if not args.initialize:
        require((ROOT/MANIFEST).is_file(),'release manifest missing')
        verify_manifest(ROOT,members)
    out.mkdir(parents=True);stage=out/'Report212';stage.mkdir();logs=out/'logs';logs.mkdir()
    for name in names:
        (stage/name).parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/name,stage/name)
    flags=['-O'] if sys.flags.optimize else []
    mode='quick' if args.quick else 'regenerate'
    run([sys.executable,*flags,'code/reproduce.py',mode,'--max-k','256','--work-dir',str(out/'computation')],stage,logs/'computation.log')
    evidence=read_json_unique(out/'computation/replay_metadata.json')
    require(evidence['all_checks_passed'],'code replay status')
    require(evidence['scope']['public_table_exact_regeneration_checked']==(not args.quick),'code replay scope')
    if not args.quick:
        for name in ['table_values.json','numeric_table.tsv','numeric_table_quarter.tex','numeric_table_log_squared.tex']:
            actual=(out/'computation/tables'/name).read_bytes()
            require(actual==(ROOT/'tables'/name).read_bytes(),'fresh table baseline mismatch '+name)
            (stage/'tables'/name).write_bytes(actual)
    make_pdf(stage,logs)
    if (ROOT/PDF).exists():require((stage/PDF).read_bytes()==(ROOT/PDF).read_bytes(),'PDF baseline mismatch; verify the TeX/font toolchain')
    else:require(args.initialize,'PDF baseline missing')
    manifest={'format':'Report212 SHA256 manifest v1','files':{name:sha((stage/name).read_bytes()) for name in sorted(members)}}
    write_json(stage/MANIFEST,manifest)
    if not args.initialize:require((stage/MANIFEST).read_bytes()==(ROOT/MANIFEST).read_bytes(),'rebuilt manifest mismatch')
    verify_manifest(stage,members)
    allmembers=sorted(members+[MANIFEST]);archive=out/'Report212-reproducibility.zip'
    with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_STORED) as z:
        for name in allmembers:
            info=zipfile.ZipInfo('Report212/'+name,(2026,10,4,0,0,0));info.create_system=3;info.external_attr=0o100644<<16
            z.writestr(info,(stage/name).read_bytes())
    with zipfile.ZipFile(archive) as z:
        require(z.namelist()==['Report212/'+n for n in allmembers],'actual ZIP inventory mismatch')
        require(z.testzip() is None,'ZIP CRC failure')
        for name in allmembers:require(z.read('Report212/'+name)==(stage/name).read_bytes(),'ZIP member byte mismatch '+name)
    receipt={'all_checks_passed':True,'fresh_public256_regeneration':not args.quick,'source_baselines_verified':not args.initialize,
             'pdf_rebuilt_to_byte_stability':True,'python_optimization':sys.flags.optimize,
             'code_replay_scope':evidence['scope'],'zip_member_count':len(allmembers),
             'actual_zip_members_verified':True,'archive_sha256':sha(archive.read_bytes()),
             'members':{name:sha((stage/name).read_bytes()) for name in allmembers}}
    write_json(out/'reproduction.json',receipt);print(json.dumps(receipt,indent=2,sort_keys=True))
if __name__=='__main__':main()
