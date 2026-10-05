#!/usr/bin/env python3
"""Fresh read-only Git/ZIP metadata audit; no supplied program is imported/run."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import zipfile

REPO = Path('/home/codex/.codex/worktrees/2a71/Proofs')
COMMIT = 'eea1598182ea39da39d594fcc3370e6e143c7648'
PARENT = '81553ad2ccbdcf295842da96b5f56c6a1421562d'
ARRIVAL = 'e88ed8bf6b349e63c0bb3e3ab146c582275ec0d9'
HOST = 'SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a189281-path-forest-expansions/'
STEM = Path('/tmp/review_path_forest_publication_eea159818')
ARTICLE_SPANS = [(3600,3740),(4042,4206),(4985,5060),(5315,5407),
                 (5465,5558),(5607,5793),(5890,5906),(6010,6089),
                 (6190,6249),(6282,6297),(6671,6739),(7115,7365),(7498,7600),(7635,7740)]

def ck(ok, message):
    if not ok:
        raise ValueError(message)

def git(*args):
    return subprocess.check_output(['git', '-C', str(REPO), *args])

def sha(data):
    return hashlib.sha256(data).hexdigest()

def blob(commit, path):
    return git('show', commit + ':' + path)

def desc(data):
    return {'bytes':len(data), 'sha256':sha(data)}

def file_record(commit, path):
    data=blob(commit,path)
    return {'commit':commit,'path':path,'blob':git('rev-parse',commit+':'+path).decode().strip(),**desc(data)},data

def spans(data, selected):
    lines=data.splitlines(keepends=True)
    out=[]
    for lo,hi in selected:
        ck(1<=lo<=hi<=len(lines),'span range')
        out.append({'first_line':lo,'last_line':hi,**desc(b''.join(lines[lo-1:hi]))})
    return out

def labels(data):
    text=data.decode()
    return [{'name':m.group(1),'line':text.count('\n',0,m.start())+1}
            for m in re.finditer(r'\\label(?:\[[^]]*\])?\{([^}]*)\}',text)]

def collect():
    ck(git('rev-parse',COMMIT+'^').decode().strip()==PARENT,'parent')
    changed=git('diff','--name-only',PARENT,COMMIT).decode().splitlines()
    ck(sorted(changed)==sorted(HOST+n for n in ['README.md','article.tex','article.pdf']),'changed paths')
    files=[]
    contents={}
    for name in ['README.md','article.tex','article.pdf']:
        old,od=file_record(PARENT,HOST+name)
        new,nd=file_record(COMMIT,HOST+name)
        rec={'before':old,'after':new,'read_scope':'hash only'}
        contents[name]=nd
        if name!='article.pdf':
            diff=git('diff','--no-ext-diff','--unified=3',PARENT,COMMIT,'--',HOST+name)
            rec['diff']={**desc(diff),'lines':len(diff.splitlines()),'read_scope':'full diff' if name=='README.md' else 'hash only; selected resulting-source spans read'}
            if name=='README.md':
                rec['diff']['read_spans']=spans(diff,[(1,len(diff.splitlines()))])
                rec['read_scope']='full textual diff; unchanged lines not separately read'
            else:
                rec['read_scope']='selected source spans'
                rec['read_spans']=spans(nd,ARTICLE_SPANS)
        files.append(rec)
    old_article=blob(PARENT,HOST+'article.tex')
    newlabels=labels(contents['article.tex'])
    oldlabels=labels(old_article)
    names=[v['name'] for v in newlabels]
    oldnames=[v['name'] for v in oldlabels]
    ck(len(names)==len(set(names)),'duplicate article labels')
    ck(set(oldnames)<=set(names),'lost old label')
    refs=[]
    text=contents['article.tex'].decode()
    for m in re.finditer(r'\\(?:[Cc]ref|eqref|ref|autoref|pageref)\*?\{([^}]*)\}',text):
        for name in m.group(1).split(','):
            refs.append({'name':name.strip(),'line':text.count('\n',0,m.start())+1})
    missing=sorted(set(v['name'] for v in refs)-set(names))
    ck(not missing,'missing literal references: '+str(missing))
    archives=[]
    total_placements=0
    for archive,root,prefix,labelprefix in [
        ('ProveIt_Moving_Gap_Permutations.zip','Moving_Gap_Permutations/','04-moving-gaps-','spf:mg:'),
        ('ProveIt_A189281_Borel_Completion.zip','ProveIt_A189281_Borel_Completion/','05-borel-completion-','spf:bc:')]:
        rec,raw=file_record(ARRIVAL,'docs/incoming/'+archive)
        z=zipfile.ZipFile(io.BytesIO(raw))
        members=[]
        byrel={}
        for inf in z.infolist():
            if not inf.is_dir():
                ck(inf.filename.startswith(root),'archive root')
                rel=inf.filename[len(root):]
                ck(rel not in byrel,'duplicate member')
                data=z.read(inf.filename)
                byrel[rel]=data
                members.append({'path':inf.filename,**desc(data),'coverage':'metadata only'})
        manifest=[]
        for line in byrel['SHA256SUMS.txt'].decode().splitlines():
            expected,rel=line.split(None,1)
            rel=rel.lstrip('*')
            ck(rel in byrel and sha(byrel[rel])==expected,'manifest member '+rel)
            manifest.append({'path':rel,'sha256':expected})
        ck(set(v['path'] for v in manifest)==set(byrel)-{'SHA256SUMS.txt'},'manifest coverage')
        placements=[]
        for rel,data in byrel.items():
            if rel in ['README.md','article.tex','article.pdf','SHA256SUMS.txt']:
                continue
            if rel.startswith('code/') or rel.startswith('data/'):
                folder,name=rel.split('/',1)
                target=HOST+folder+'/'+prefix+name
            elif rel in ['Makefile','build.sh']:
                target=HOST+'code/'+prefix+rel
            elif rel=='SOURCES.md':
                target=HOST+prefix+rel
            elif rel=='requirements-optional.txt':
                target=HOST+'data/'+('02-fixed-gap-requirements.txt' if prefix.startswith('04') else prefix+rel)
            else:
                raise ValueError('unmapped '+rel)
            placed,pdata=file_record(COMMIT,target)
            ck(data==pdata,'placement byte mismatch '+target)
            placements.append({'member':root+rel,'placed':placed,'byte_identical':True,
                               'reused_older_requirements':rel=='requirements-optional.txt' and prefix.startswith('04')})
        total_placements+=len(placements)
        routes=[]
        for v in labels(byrel['article.tex']):
            newname=labelprefix+v['name']
            ck(newname in names,'source label missing '+newname)
            routes.append({'source_label':v['name'],'source_line':v['line'],
                           'host_label':newname,'host_line':newlabels[names.index(newname)]['line']})
        if prefix.startswith('05'):
            for v in members:
                if v['path']==root+'article.tex':
                    v['coverage']='only lines 481–492 newly read; other coverage inherited from pinned intake'
                    v['read_spans']=spans(byrel['article.tex'],[(481,492)])
        rec.update({'members':members,'manifest':manifest,'manifest_entries':len(manifest),
                    'placements':placements,'label_routes':routes,'source_article_body_equivalence_verified':False})
        archives.append(rec)
    inherited_path='Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/triage_discrete_e88ed8bf6.md'
    inherited,idata=file_record(COMMIT,inherited_path)
    inherited['read_spans']=spans(idata,[(1,len(idata.splitlines()))])
    rule,rdata=file_record(COMMIT,'docs/incoming/README.md')
    rule['read_spans']=spans(rdata,[(420,446)])
    ck(b'Unproved and wrong claims are never dropped' in b'\n'.join(rdata.splitlines()[419:446]),'retention locator')
    source_pins=[]
    for c in ['d1680cdfa40c44abf0825416b6f36a3e9ec2662c','79e7aab60ee856862b36c38cf32cfdb1be95313f']:
        s,data=file_record(c,HOST+'article.tex')
        ck(data==old_article,'source pin not parent article')
        source_pins.append(s)
    return {'schema':'bounded-publication-review/v1','review_commit':COMMIT,'parent':PARENT,
            'source_sha256':sha(Path(__file__).read_bytes()),'changed_files':files,
            'inherited_intake_read':inherited,'retention_rule_read':rule,
            'archives':archives,'prior_article_pins_match_parent':source_pins,
            'labels':{'before_count':len(oldlabels),'after_count':len(newlabels),
                      'new_count':len(set(names)-set(oldnames)),
                      'old_labels_retained':True,'host_labels':newlabels,
                      'references':refs,'missing_references':missing,
                      'compiled_numbering_verified':False},
            'totals':{'changed_blobs':3,'archives':len(archives),
                      'archive_members':sum(len(a['members']) for a in archives),
                      'manifest_entries':sum(a['manifest_entries'] for a in archives),
                      'byte_identical_placements_including_reuse':total_placements,
                      'source_label_routes':sum(len(a['label_routes']) for a in archives),
                      'article_lines_read':sum(hi-lo+1 for lo,hi in ARTICLE_SPANS),
                      'full_guide_diff_lines':len(git('diff','--no-ext-diff','--unified=3',PARENT,COMMIT,'--',HOST+'README.md').splitlines())},
            'limitations':['No supplied, archived, frozen or predecessor code executed or imported.',
                           'No TeX build, PDF rendering, analytic test replay, or numerical sign certification.',
                           'Only declared article spans read; no full manuscript or transformed-body equivalence audit.',
                           'Literal label/reference routes do not verify compiled numbering or external literature.']}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--write',action='store_true')
    args=ap.parse_args()
    result=collect()
    data=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
    target=STEM.with_suffix('.json')
    if args.write:
        target.write_bytes(data)
    else:
        ck(target.read_bytes()==data,'receipt mismatch')
    print(json.dumps({'status':'PASS','totals':result['totals'],'receipt_sha256':sha(data)},sort_keys=True))

if __name__=='__main__':
    main()
