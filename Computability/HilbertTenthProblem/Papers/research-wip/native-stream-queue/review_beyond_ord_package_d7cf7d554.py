#!/usr/bin/env python3
"""Fresh metadata collector; no delivered or predecessor program execution."""
import argparse
import hashlib
import io
import json
import re
import subprocess
import zipfile
from collections import Counter
from pathlib import Path

ROOT = Path('/home/codex/.codex/worktrees/2a71/Proofs')
ARRIVAL = 'd7cf7d5547a50a6cf372f2cfaad96e950a68c03a'
OLD = 'e3839ad2c6be32ac5c6fdc422507da07f85f4fb6'
SOURCE = 'e1d2f3048b947801873a6e9ddc4e03736234b328'
PATH = 'docs/incoming/Beyond_Ord_Research_Package.zip'
WIP = 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/'
HOST = 'Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/'
TEX_SPANS = [(83,134),(206,326),(329,467),(469,938),(939,1093),
             (1104,1165),(1677,1772),(1774,1886),(1888,2078),
             (2252,2370),(2424,2514),(2516,2785)]

def git(*args):
    return subprocess.check_output(['git','-C',str(ROOT),*args])

def sha(b):
    return hashlib.sha256(b).hexdigest()

def meta(b):
    return {'bytes':len(b),'sha256':sha(b),
            'git_blob_sha1':hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()}

def blob(commit,path):
    b=git('show',commit+':'+path)
    return b, dict(meta(b),commit=commit,path=path,
                   blob=git('rev-parse',commit+':'+path).decode().strip())

def spans(b, intervals):
    lines=b.decode('utf-8').splitlines()
    if intervals == 'all':
        intervals=[(1,len(lines))]
    result=[]
    for lo,hi in intervals:
        if not 1<=lo<=hi<=len(lines):
            raise ValueError('invalid span')
        x=('\n'.join(lines[lo-1:hi])+'\n').encode()
        result.append({'first':lo,'last':hi,'lines':hi-lo+1,
                       'normalized_utf8_sha256':sha(x)})
    return result

def archive(commit,path):
    b,m=blob(commit,path)
    with zipfile.ZipFile(io.BytesIO(b)) as z:
        entries=[i for i in z.infolist() if not i.is_dir()]
        if len(set(i.filename for i in entries))!=len(entries):
            raise ValueError('duplicate archive member')
        data={i.filename:z.read(i) for i in entries}
        m['members']=[dict(meta(data[i.filename]),path=i.filename,
                            compressed_bytes=i.compress_size,crc32=f'{i.CRC:08x}',
                            coverage='hash only',read_spans=[])
                      for i in entries]
    return m,data

def census(b):
    s=b.decode('utf-8')
    labels=re.findall(r'\\label(?:\[[^]]*\])?\{([^{}]+)\}',s)
    refs=[v.strip() for m in re.findall(
        r'\\(?:ref|eqref|pageref|autoref|cref|Cref)\*?(?:\[[^]]*\])?\{([^{}]+)\}',s)
          for v in m.split(',')]
    cites=[v.strip() for m in re.findall(
        r'\\cite\w*\*?(?:\[[^]]*\])*\{([^{}]+)\}',s) for v in m.split(',')]
    bib=re.findall(r'\\bibitem(?:\[[^]]*\])?\{([^{}]+)\}',s)
    return {'labels':labels,'duplicate_labels':[k for k,v in Counter(labels).items() if v>1],
            'references':refs,'unresolved_references':sorted(set(refs)-set(labels)),
            'citations':cites,'bibliography_keys':bib,
            'unresolved_citations':sorted(set(cites)-set(bib)),
            'question_environments':s.count('\\begin{question}'),
            'scope':'Literal regex only; no TeX expansion, build or PDF inspection.'}

def collect():
    current,data=archive(ARRIVAL,PATH)
    if current['sha256']!='a598178e496417cdaf982e387d72aad9ca954778296ea70c51e684f69d3acd12':
        raise ValueError('unexpected delivery bytes')
    full=['Beyond_Ord/README.txt','Beyond_Ord/SOURCE_AUDIT.txt',
          'Beyond_Ord/code/README.md','Beyond_Ord/DOCUMENT_CHECKS.json',
          'Beyond_Ord/code/verification.json']
    for m in current['members']:
        if m['path'] in full:
            m['coverage']='full guide/status/data read'
            m['read_spans']=spans(data[m['path']],'all')
        elif m['path']=='Beyond_Ord/beyond_ord.tex':
            m['coverage']='selected interfaces and local proof challenges only'
            m['read_spans']=spans(data[m['path']],TEX_SPANS)
        elif m['path'].endswith(('.py','.sh')):
            m['coverage']='hash only; source not read or executed/imported'
        else:
            m['coverage']='hash only; PDF not rendered/read'
    document=json.loads(data['Beyond_Ord/DOCUMENT_CHECKS.json'])
    bound=[]
    for relative,pin in document['sha256'].items():
        name='Beyond_Ord/'+relative
        if sha(data[name])!=pin:
            raise ValueError('delivered checksum failure')
        bound.append({'path':name,'sha256':pin,'match':True})
    old_archives=[]
    identical=[]
    for name in ['Beyond_Ord_Class_Well_Orders.zip','Beyond_Ord_Research.zip',
                 'beyond_ord.zip','class_orders_beyond_ord.zip']:
        old, prior=archive(OLD,'docs/incoming/'+name)
        for x,b in data.items():
            for y,c in prior.items():
                if b==c:
                    identical.append({'new_member':x,'old_archive':name,'old_member':y,
                                      'sha256':sha(b)})
        old_archives.append(old)
    context_specs=[
      (ARRIVAL,'Algebra/SurrealNumbers/AGENTS.md','all'),
      (ARRIVAL,'docs/incoming/README.md',[(390,450)]),
      (ARRIVAL,WIP+'review_beyond_ord_e3839ad2c.md','all'),
      (SOURCE,HOST+'29-birthdays-PROOF_STATUS.txt','all'),
      (SOURCE,'Logic/PeanoArithmetic/ListCoding/README.md',[(248,359)])]
    contexts=[]
    for commit,path,reads in context_specs:
        b,m=blob(commit,path)
        m['read_spans']=spans(b,reads)
        contexts.append(m)
    claimed_source_paths=['README.md',HOST+'README.md',HOST+'29-birthdays-PROOF_STATUS.txt',
                          'Logic/PeanoArithmetic/ListCoding/README.md']
    source_routes=[blob(SOURCE,p)[1] for p in claimed_source_paths]
    parent=git('rev-parse',ARRIVAL+'^').decode().strip()
    diff=git('diff','--no-ext-diff','--binary',parent,ARRIVAL,'--',PATH)
    notation=json.loads(data['Beyond_Ord/code/verification.json'])
    count=notation['independent_oracle']['distinct_total_samples']
    pairs=notation['independent_oracle']['unordered_pair_checks']
    if count*(count-1)//2!=pairs:
        raise ValueError('inconsistent pair-count metadata')
    c=census(data['Beyond_Ord/beyond_ord.tex'])
    if c['duplicate_labels'] or c['unresolved_references'] or c['unresolved_citations']:
        raise ValueError('literal TeX locator failure')
    all_spans=[s for m in current['members'] for s in m['read_spans']]
    ctx_spans=[s for m in contexts for s in m['read_spans']]
    return {'schema':'beyond-ord-package-intake-v1','arrival':ARRIVAL,'parent':parent,
      'archives':[current], 'addition_diff':dict(meta(diff),human_read='status only; binary diff hashed'),
      'delivered_hash_bindings':bound,'tex_census':c,
      'prior_archive_comparison':{'archives':old_archives,'identical_members':identical,
           'scope':'Byte comparison only; previous mathematical/read scope is not enlarged.'},
      'contexts':contexts,'claimed_source_routes':source_routes,
      'delivered_status':{'document':document,'notation':notation,
                          'pair_count_arithmetic_checked':True,'supplied_checks_replayed':False},
      'totals':{'archives':1,'members':len(current['members']),
          'delivered_hashes':len(bound),'archive_read_spans':len(all_spans),
          'archive_read_lines':sum(s['lines'] for s in all_spans),
          'article_read_lines':sum(b-a+1 for a,b in TEX_SPANS),
          'context_read_spans':len(ctx_spans),'context_read_lines':sum(s['lines'] for s in ctx_spans),
          'labels':len(c['labels']),'references':len(c['references']),
          'bibliography_entries':len(c['bibliography_keys']),
          'prior_archives':len(old_archives),'prior_members':sum(len(x['members']) for x in old_archives),
          'byte_identical_prior_members':len(identical)},
      'scope':{'full_manuscript_certification':False,'external_literature_audit':False,
          'actual_Lean_Rocq_source_audit':False,'supplied_program_execution':False,
          'supplied_program_import':False,'predecessor_execution_import':False,
          'supplied_program_source_read':False,'build_execution':False,
          'pdf_rendering':False,'repository_mutation':False},
      'reviewer_helper_sha256':sha(Path(__file__).read_bytes())}

def main():
    p=argparse.ArgumentParser()
    g=p.add_mutually_exclusive_group(required=True)
    g.add_argument('--output',type=Path)
    g.add_argument('--expect',type=Path)
    a=p.parse_args(); result=collect()
    if a.output:
        with a.output.open('x',encoding='utf-8') as f:
            json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    elif json.loads(a.expect.read_text())!=result:
        raise ValueError('receipt mismatch')
    print('PASS',json.dumps(result['totals'],sort_keys=True))

if __name__=='__main__':
    main()
