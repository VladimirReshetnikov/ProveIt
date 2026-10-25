#!/usr/bin/env python3
"""Make a self-contained TeX attachment from an approved report source tree.

Only whole-line local input/include directives are expanded. The multi-file
source remains authoritative and the exact source-file hashes are retained.
"""
from pathlib import Path
import argparse,hashlib,json,re
PAT=re.compile(r'^\\(?:input|include)\{([^{}]+)\}[ \t]*(?:%.*)?$',re.M)

def need(ok,msg):
    if not ok:raise ValueError(msg)
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--source',required=True,type=Path)
    ap.add_argument('--output',required=True,type=Path)
    ap.add_argument('--receipt',required=True,type=Path)
    a=ap.parse_args();root=a.source.resolve().parent;seen={}
    def expand(p,stack):
        p=p.resolve();need(p.is_relative_to(root),'input outside report source tree')
        need(p not in stack,'recursive TeX input')
        raw=p.read_bytes();seen[p.relative_to(root).as_posix()]=hashlib.sha256(raw).hexdigest()
        def sub(m):
            name=m.group(1);child=root/name
            if not child.suffix:child=child.with_suffix('.tex')
            body=expand(child,stack+[p])
            return '% BEGIN '+name+'\n'+body+('' if body.endswith('\n') else '\n')+'% END '+name
        return PAT.sub(sub,raw.decode('utf-8'))
    text=expand(a.source,[])
    need(not re.search(r'(?m)^\s*\\(?:input|include)\b',text),'unexpanded input directive')
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(text,encoding='utf-8')
    a.receipt.write_text(json.dumps({'schema':'self_contained_tex_source_v1','sources':seen,
      'output_sha256':hashlib.sha256(a.output.read_bytes()).hexdigest(),
      'scope':'Whole-line local TeX inclusions expanded; no mathematical changes.'},indent=2)+'\n')
    print(json.dumps({'status':'PASS','source_files':len(seen),'output_bytes':a.output.stat().st_size}))
if __name__=='__main__':main()
