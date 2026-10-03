#!/usr/bin/env python3
"""Read-only integration audit; no source execution, TeX build or theorem checking."""
import argparse, collections, hashlib, io, json, pathlib, re, subprocess, zipfile

REPORT = 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates'
ARCHIVES = {
 13: ('Exact_Wiring_Diophantine_Report.zip','Exact_Wiring_Diophantine/','5115e76cf01577b7348cc7b987260d4ec166ba61b746dc7601625adad00fcf08'),
 14: ('Topology_Is_Not_Free_Interaction_Nets.zip','Interaction_Net_Diophantine/','d0d7405ec4e572f1542b8a618815f5de99498cc385ccd9cdcdbd5d8080ebd5b8'),
 15: ('no_ghost_wires.zip','no_ghost_wires/','5df354ceed72357e5b61233535052e424e56a5646f8afafcdc26c981a902419a'),
 16: ('sandpile_diophantine_research.zip','sandpile_diophantine_certificates/','2022a5d4986621045e2d9e25ac7edb79d90d8a13c3112e24fa6ee3f4ddffb14e'),
}
def sha(b): return hashlib.sha256(b).hexdigest()
def git(root,spec): return subprocess.check_output(['git','-C',str(root),'show',spec])
def norm(s):
    s=re.sub(r'(?m)(?<!\\)%.*$', '', s)
    s=s.replace('cdc:sp:','').replace(r'\indset',r'\ind')
    s=s.replace(r'\Ccmp',r'\mathcal C').replace(r'\Poly',r'\mathcal P').replace(r'\diag',r'\operatorname{diag}')
    s=s.replace(r'{\mathcal P}',r'\mathcal P').replace(r'{\mathcal C}',r'\mathcal C')
    s=s.replace(r'\pi_{\mathrm S}',r'\pi')
    return re.sub(r'\s+', '', s)
def formulas(s):
    # Named displays only: each equation/aligned display retained literally after documented renamings.
    return re.findall(r'\\begin\{(equation\*?|align\*?)\}([\s\S]*?)\\end\{\1\}',s)
def verify(root):
    root=pathlib.Path(root).resolve()
    tex=git(root,'cb8238b64:'+REPORT+'/article.tex').decode()
    readme=git(root,'cb8238b64:'+REPORT+'/README.md').decode()
    result={'scope':'Part XVI revision plus source/data and integration spot checks for Part XV; no fresh author execution', 'revision':'cb8238b64', 'integration_hashes': {'article.tex':sha(tex.encode()),'README.md':sha(readme.encode())},'archives':{},'file_comparisons':[]}
    for number,(archive,prefix,pin) in ARCHIVES.items():
        raw=git(root,'1977e6ea6:docs/incoming/'+archive)
        if sha(raw)!=pin: raise ValueError('archive pin mismatch')
        with zipfile.ZipFile(io.BytesIO(raw)) as z:
            files={p.filename:z.read(p) for p in z.infolist() if not p.is_dir()}
        for p in files:
            q=pathlib.PurePosixPath(p)
            if q.is_absolute() or '..' in q.parts: raise ValueError('unsafe archive name')
        section=readme.split('**Manuscript '+str(number)+'** (package root',1)[1]
        section=section.split('**Manuscript ',1)[0]
        mapping=re.findall(r'^\| `([^`]+)` \| `([^`]+)` \|$',section,re.M)
        if not mapping: raise ValueError('no mappings')
        for old,new in mapping:
            if not re.match(r'(?:code/|data/)?'+str(number)+'-',new): continue
            src=files[prefix+old]
            dst=git(root,'cb8238b64:'+REPORT+'/'+new)
            equality='byte' if src==dst else 'line_ending'
            if src.replace(b'\r\n',b'\n')!=dst.replace(b'\r\n',b'\n'): raise ValueError('source drift '+new)
            result['file_comparisons'].append({'archive':archive,'member':prefix+old,'shipped':new,'sha256_source':sha(src),'sha256_shipped':sha(dst),'equality':equality})
        result['archives'][archive]={'sha256':pin,'members':len(files),'mapped_files':sum(x['archive']==archive for x in result['file_comparisons'])}
        if number==16:
            original=files[prefix+'article.tex'].decode()
            expected=[norm(s) for _,s in formulas(original)]
            observed=collections.Counter(norm(s) for _,s in formulas(tex))
            missing=[]
            for s in expected:
                if observed[s]: observed[s]-=1
                else: missing.append(s)
            result['sandpile_named_displays']={'original':len(expected),'matched':len(expected)-len(missing),'unmatched':missing}
            if missing: raise ValueError('changed named sandpile display: '+repr(missing))
            oldlabels=set(re.findall(r'\\label\{([^}]+)\}', original))
            newlabels=set(re.findall(r'\\label\{cdc:sp:([^}]+)\}', tex))
            if oldlabels-newlabels: raise ValueError('lost source labels')
            result['sandpile_source_labels']=len(oldlabels)
            result['sandpile_editorial_labels']=len(newlabels-oldlabels)
    stripped=re.sub(r'(?m)(?<!\\)%.*$', '',tex)
    # Ignore literal listings and \verb examples for the reference syntax audit.
    stripped=re.sub(r'\\begin\{(?:lstlisting|verbatim|Verbatim)\}[\s\S]*?\\end\{(?:lstlisting|verbatim|Verbatim)\}','',stripped)
    stripped=re.sub(r'\\verb(.).*?\1','',stripped)
    labels=re.findall(r'\\label\{([^{}]+)\}',stripped)
    refs=[x.strip() for group in re.findall(r'\\(?:[Cc]ref|ref|eqref|pageref)\*?\{([^{}]+)\}',stripped) for x in group.split(',')]
    addedrefs=[x for x in refs if x.startswith(('cdc:sp:','cdc:ew:','cdc:nt:','cdc:ng:','cdc:ic:'))]
    result['reference_audit']={'integration_refs':len(addedrefs),'missing':sorted(set(addedrefs)-set(labels)),'duplicate_labels':sorted(x for x,n in collections.Counter(labels).items() if n>1)}
    if result['reference_audit']['missing'] or result['reference_audit']['duplicate_labels']: raise ValueError('bad integration references')
    result['findings']=[{'priority':3,'path':REPORT+'/article.tex','line':266,'issue':'Organization says fifteen Parts and the table ending at line 287 omits XVI, although the new Part and sixteen-manuscript descriptions are present.'}]
    result['status']='PASS_WITH_EDITORIAL_FINDING'
    return result
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--output',type=pathlib.Path)
    a=p.parse_args(); data=json.dumps(verify(a.root),indent=2,sort_keys=True)+'\n'
    if a.output:a.output.write_text(data)
    else:print(data,end='')
