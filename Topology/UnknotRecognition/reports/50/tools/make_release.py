"""Build the inventory and ZIP; exclude caches and LaTeX intermediates."""
from pathlib import Path
import argparse,hashlib,shutil,zipfile
ROOT=Path(__file__).resolve().parents[1]


def files():
    bad_suffixes={'.pyc','.aux','.out','.toc','.fls','.fdb_latexmk','.synctex.gz'}
    for p in sorted(ROOT.rglob('*')):
        if not p.is_file() or '__pycache__' in p.parts:continue
        if p.name=='MANIFEST.sha256' or p.suffix in bad_suffixes:continue
        if p.parent.name=='paper' and p.suffix=='.log':continue
        if p.name.startswith('latex_') and p.name!='latex_final.log':continue
        yield p


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path)
    args=parser.parse_args();out=args.output or ROOT.parent/(ROOT.name+'.zip')
    selected=list(files())
    manifest=['# SHA-256 inventory; this manifest is intentionally not self-hashed.']
    for p in selected:manifest.append(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(ROOT).as_posix())
    (ROOT/'MANIFEST.sha256').write_text('\n'.join(manifest)+'\n')
    selected.append(ROOT/'MANIFEST.sha256')
    with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for p in sorted(selected):
            name=ROOT.name+'/'+p.relative_to(ROOT).as_posix()
            info=zipfile.ZipInfo(name,date_time=(2026,10,8,0,0,0))
            info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o644<<16
            z.writestr(info,p.read_bytes())
    digest=hashlib.sha256(out.read_bytes()).hexdigest()
    out.with_suffix(out.suffix+'.sha256').write_text(digest+'  '+out.name+'\n')
    pdf=ROOT.parent/(ROOT.name+'.pdf');shutil.copy2(ROOT/'paper/article.pdf',pdf)
    print(f'{len(selected)} files; ZIP {out.stat().st_size} bytes')
    print('ZIP SHA256',digest)
    print('PDF',pdf,'SHA256',hashlib.sha256(pdf.read_bytes()).hexdigest())
if __name__=='__main__':main()
