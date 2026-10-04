#!/usr/bin/env python3
"""Build the authenticated Report60 manuscript with fresh TeX format and render every page.
Use python3 -I -S -B tools/build_report60.py --output-dir /fresh/external/directory
No scientific source program, checker, collision schedule, or Lean file is executed.
"""
import argparse, hashlib, json, os, re, stat, struct, subprocess, sys, tempfile, zlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
EPOCH = '1791072000'
DEPENDENCY_LOCK_SHA256 = 'e17fae69b920a561de81fd06b53eba171ac9aaf557d8bbf6bf2e64a41a226ca3'
SYSTEM_ROOTS = ('/usr/share/texlive/', '/usr/share/texmf/', '/etc/texmf/', '/var/lib/texmf/')
MANUSCRIPT_NAMES = ('Report60.tex', 'physical.tex', 'geometry.tex', 'arithmetic.tex', 'evidence.tex')
# Updated only after explicit manuscript inspection; this binds the full input map.
INPUT_PINS_SHA256 = '331e5276ac4375faa6aed52766b762dad28135e37d16361cf376d5bef1ff0615'
REVIEWED_PINS_SHA256 = '9d0853622da5004c6d3f435fcd3a04d2762c6032514c1debeb4bb8636c35ca5f'

def require(test, message):
    if not test: raise ValueError(message)
def sha(data): return hashlib.sha256(data).hexdigest()
def encoded(value): return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()
def read_file(path):
    first = path.lstat()
    require(stat.S_ISREG(first.st_mode) and first.st_nlink == 1, 'Expected single-link regular file: '+str(path))
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    with os.fdopen(fd, 'rb') as stream:
        before = os.fstat(stream.fileno()); data = stream.read(); after = os.fstat(stream.fileno())
    last = path.lstat()
    def identity(st): return (st.st_dev, st.st_ino, st.st_mode, st.st_nlink, st.st_size, st.st_mtime_ns, st.st_ctime_ns)
    require(identity(first) == identity(before) == identity(after) == identity(last), 'Input changed while reading: '+str(path))
    return data
def inventory():
    result = {}
    require(stat.S_ISDIR(ROOT.lstat().st_mode), 'Release root must be a directory')
    for path in sorted(ROOT.rglob('*')):
        st = path.lstat()
        require(stat.S_ISDIR(st.st_mode) or stat.S_ISREG(st.st_mode), 'Nonregular release entry: '+str(path))
        if stat.S_ISREG(st.st_mode):
            result[str(path.relative_to(ROOT))] = {'sha256':sha(read_file(path)), 'bytes':st.st_size, 'mode':stat.S_IMODE(st.st_mode), 'mtime_ns':st.st_mtime_ns}
    observed_dirs={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if stat.S_ISDIR(p.lstat().st_mode)}
    expected_dirs={parent.as_posix() for name in result for parent in Path(name).parents if parent.as_posix()!='.'}
    require(observed_dirs==expected_dirs, 'Unexpected empty directory in release')
    return result

def destination(raw):
    require(raw.startswith('/') and not raw.startswith('//'), 'Canonical absolute output path required')
    path = Path(raw)
    require(str(path) == raw and all(p not in ('.','..') for p in raw.split('/')), 'Noncanonical output path')
    for part in reversed([path, *path.parents]):
        if os.path.lexists(part):
            st = part.lstat()
            require(not stat.S_ISLNK(st.st_mode), 'Symlink destination component')
            require(part == path or stat.S_ISDIR(st.st_mode), 'Output ancestor is not a directory')
        else: require(part == path, 'Output parent must already exist')
    require(not os.path.lexists(path), 'Output must not exist')
    require(path != ROOT and ROOT not in path.parents and path not in ROOT.parents, 'Output must be outside release')
    return path

def command(argv, cwd, env, timeout=240):
    return subprocess.run(argv, cwd=cwd, env=env, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=timeout)

def main():
    require(sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode and not sys.flags.optimize, 'Use python3 -I -S -B without optimization')
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output-dir', required=True)
    ap.add_argument('--render-dpi',type=int,default=120)
    ap.add_argument('--require-packaged-match',action='store_true')
    a=ap.parse_args()
    require(72 <= a.render_dpi <= 200, 'Render DPI must be 72 through 200')
    require(Path(__file__).absolute() == Path(__file__).resolve(), 'Tool path must have no symlink components')
    before=inventory()
    input_pin_data=read_file(ROOT/'INPUT_PINS.json')
    require(sha(input_pin_data)==INPUT_PINS_SHA256, 'Frozen input-pin map differs from inspected version')
    frozen=json.loads(input_pin_data)
    scopes={Path(base).parts[0] for base in frozen['roots']}
    observed={name:{'bytes':row['bytes'],'sha256':row['sha256']} for name,row in before.items() if any(name.startswith(base+'/') for base in scopes)}
    require(observed==frozen['files'], 'Frozen science, audit, or dependency bytes differ')
    rawpins=read_file(ROOT/'manuscript/MANUSCRIPT_PINS.json')
    require(sha(rawpins)==REVIEWED_PINS_SHA256, 'Manuscript pin-map differs from inspected version')
    pins=json.loads(rawpins)
    require(set(pins)==set(MANUSCRIPT_NAMES), 'Unexpected manuscript input names')
    require(set(p.name for p in (ROOT/'manuscript').iterdir())==set(MANUSCRIPT_NAMES)|{'MANUSCRIPT_PINS.json'}, 'Unexpected manuscript entry')
    sources={name:read_file(ROOT/'manuscript'/name) for name in MANUSCRIPT_NAMES}
    require(all(sha(sources[name])==pins[name] for name in sources), 'Manuscript hash mismatch')
    flat=sources['Report60.tex']
    for name in MANUSCRIPT_NAMES[1:]:
        token=('\\input{'+name+'}\n').encode()
        require(flat.count(token)==1, 'Expected one modular input: '+name)
        flat=flat.replace(token,sources[name])
    require(read_file(ROOT/'Report60.tex')==flat, 'Standalone LaTeX differs from modular flattening')
    out=destination(a.output_dir)
    binaries={}
    for name in ('pdftex','pdflatex','kpsewhich','pdftotext','pdftoppm','pdfinfo'):
        path=Path('/usr/bin',name).resolve(strict=True)
        binaries[name]={'path':str(path),'sha256':sha(path.read_bytes())}
    rawlock=read_file(ROOT/'tools/BUILD_DEPENDENCIES_LOCK.json')
    require(sha(rawlock)==DEPENDENCY_LOCK_SHA256, 'Toolchain lock-map mismatch')
    lock=json.loads(rawlock)
    require(binaries==lock['executables'], 'Installed executable differs from toolchain lock')
    for filename,row in lock['system_inputs'].items():
        path=Path(filename)
        require(path.is_absolute() and str(path.resolve(strict=True))==filename and any(filename.startswith(base) for base in SYSTEM_ROOTS), 'Invalid locked TeX path')
        data=path.read_bytes()
        require({'bytes':len(data),'sha256':sha(data)}==row, 'Installed TeX input differs from toolchain lock: '+filename)
    out.mkdir(mode=0o700)
    try:
        with tempfile.TemporaryDirectory(prefix='report60-typeset-') as temp:
            work=Path(temp); cache=work/'cache'; home=work/'home'; cache.mkdir();home.mkdir()
            (work/'Report60.tex').write_bytes(flat)
            env={'PATH':'/usr/bin:/bin','LANG':'C.UTF-8','LC_ALL':'C.UTF-8','TZ':'UTC','HOME':str(home),
                 'SOURCE_DATE_EPOCH':EPOCH,'FORCE_SOURCE_DATE':'1','TEXMF':'{/usr/share/texlive/texmf-dist,/usr/share/texmf}',
                 'TEXMFVAR':str(cache),'TEXMFCONFIG':str(cache),'TEXMFHOME':str(home),'TEXFORMATS':str(cache)+':',
                 'openin_any':'p','openout_any':'p','shell_escape':'f','MKTEXPK':'0','MKTEXTFM':'0','MKTEXMF':'0'}
            run=command(['/usr/bin/pdftex','-ini','-etex','-no-shell-escape','-recorder','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','-progname=pdflatex','pdflatex.ini'],cache,env)
            (out/'format.log').write_text(run.stdout)
            require(run.returncode==0,'Fresh TeX format generation failed')
            system={}
            def system_input(path):
                path=path.resolve(strict=True)
                require(any(str(path).startswith(prefix) for prefix in SYSTEM_ROOTS),'Unexpected external TeX input: '+str(path))
                data=path.read_bytes();system[str(path)]={'sha256':sha(data),'bytes':len(data)};return data
            maps=[]
            for name in ('lm.map','cm.map','cmextra.map','symbols.map','latxfont.map'):
                run=command(['/usr/bin/kpsewhich',name],work,env,30)
                require(run.returncode==0 and run.stdout.strip(),'Missing font map '+name)
                maps.append(system_input(Path(run.stdout.strip())))
            (cache/'pdftex.map').write_bytes(b'\n'.join(maps)+b'\n');env['TEXFONTMAPS']=str(cache)+':'
            for pass_number in range(3):
                run=command(['/usr/bin/pdflatex','-no-shell-escape','-recorder','-halt-on-error','-interaction=nonstopmode','-file-line-error','Report60.tex'],work,env)
                (out/f'compile-{pass_number+1}.log').write_text(run.stdout)
                require(run.returncode==0,'LaTeX compilation failed')
            warnings=('Overfull \\hbox','Overfull \\vbox','undefined references','undefined citations','Rerun to get cross-references right','Label(s) may have changed','rerunfilecheck Warning')
            require(not any(w in run.stdout for w in warnings),'Final layout/reference warning')
            for recorder,base in ((cache/'pdflatex.fls',cache),(work/'Report60.fls',work)):
                for line in recorder.read_text().splitlines():
                    if line.startswith('INPUT '):
                        path=Path(line[6:]);path=(path if path.is_absolute() else base/path).resolve()
                        if path!=work and work not in path.parents:system_input(path)
            require(system==lock['system_inputs'], 'Executed TeX input set differs from locked set')
            pdf=read_file(work/'Report60.pdf');require(pdf.startswith(b'%PDF-'),'Invalid PDF output')
            match=(ROOT/'Report60.pdf').exists() and read_file(ROOT/'Report60.pdf')==pdf
            require(not a.require_packaged_match or match,'Packaged PDF differs')
            (out/'Report60.pdf').write_bytes(pdf);(out/'Report60.log').write_bytes(read_file(work/'Report60.log'))
            run=command(['/usr/bin/pdftotext','-layout',str(out/'Report60.pdf'),str(out/'Report60.txt')],work,env)
            require(run.returncode==0,'Text extraction failed')
            run=command(['/usr/bin/pdfinfo',str(out/'Report60.pdf')],work,env)
            require(run.returncode==0,'PDF info failed');(out/'pdfinfo.txt').write_text(run.stdout)
            page_match=re.search(r'^Pages:\s+([1-9][0-9]*)\s*$',run.stdout,re.M)
            require(page_match is not None, 'PDF page count missing'); page_count=int(page_match.group(1))
            pages=out/'pages';pages.mkdir()
            run=command(['/usr/bin/pdftoppm','-r',str(a.render_dpi),'-png',str(out/'Report60.pdf'),str(pages/'page')],work,env)
            require(run.returncode==0,'Page rendering failed')
            rendered=list(pages.iterdir())
            names=[re.fullmatch(r'page-([0-9]+)\.png',p.name) for p in rendered]
            require(all(names) and sorted(int(m.group(1)) for m in names)==list(range(1,page_count+1)), 'Rendered page inventory differs from PDF page count')
            for path in rendered:
                data=read_file(path);require(data[:8]==b'\x89PNG\r\n\x1a\n','Invalid PNG header')
                offset=8;seen=[]
                while offset<len(data):
                    require(offset+12<=len(data),'Truncated PNG chunk')
                    length=struct.unpack('>I',data[offset:offset+4])[0];kind=data[offset+4:offset+8];end=offset+12+length
                    require(end<=len(data),'Truncated PNG payload')
                    require(zlib.crc32(data[offset+4:offset+8+length])&0xffffffff==struct.unpack('>I',data[offset+8+length:end])[0],'PNG CRC mismatch')
                    if kind==b'IHDR': require(length==13 and all(struct.unpack('>II',data[offset+8:offset+16])),'Invalid PNG dimensions')
                    seen.append(kind);offset=end
                require(seen and seen[0]==b'IHDR' and seen[-1]==b'IEND' and b'IDAT' in seen,'Incomplete PNG')
            for name,row in binaries.items():
                path=Path('/usr/bin',name).resolve(strict=True)
                require({'path':str(path),'sha256':sha(path.read_bytes())}==row, 'Installed executable changed during build: '+name)
            require(before==inventory(),'Release contents changed during build')
            (out/'BUILD_DEPENDENCIES.json').write_bytes(encoded({'executables':binaries,'system_inputs':system,'scope':'Executable bytes and recorded TeX/font-map inputs; dynamic libraries not inventoried'}))
            receipt={'status':'PASS','source_date_epoch':int(EPOCH),'manuscript_pins':pins,'pdf_sha256':sha(pdf),
                     'render_dpi':a.render_dpi,'render_pages':len(list(pages.glob('page-*.png'))),'fresh_format':True,'toolchain_lock_verified':True,'png_crc_verified':True,
                     'shell_escape':False,'release_preserved':True,'packaged_pdf_match':match,
                     'standalone_sha256':sha(flat),'scope':'Typesetting and analytic geometry only; no scientific executable'}
            (out/'BUILD_RECEIPT.json').write_bytes(encoded(receipt));print(encoded(receipt).decode())
    except BaseException as error:
        (out/'BUILD_FAILURE.json').write_bytes(encoded({'status':'FAIL','error':str(error)}));raise
if __name__=='__main__':
    try:main()
    except (ValueError,OSError,subprocess.SubprocessError) as error:
        print('BUILD REFUSED: '+str(error),file=sys.stderr);raise SystemExit(2)
