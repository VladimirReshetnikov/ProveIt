#!/usr/bin/env python3
"""Pinned source-only transfer review of canonical J3 commit 0ac86bb58.

No author modules/suites, PDF build, repository writes or history-wide review.
Source occurrences are matched in order with distinct source-scoped targets.
"""
import argparse
from collections import Counter
import difflib
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import tempfile
import zipfile

COMMIT = '0ac86bb582bf7074ec9005bf5883f1df36b0b73c'
PARENT = '7ea09b76b91abe18da6b36ee93466b1351b83662'
ARCHIVE_REF = 'b2e7981f580bfef323bacb3e3168c6f6c877e431'
REPORT = 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates'
WIP = 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue'
PINS = {
 'article.tex':'225a9ae16f4e0bf71e9e0a017cd9e24b7659ef7d4a2d2f4cf2ea546ce32bd7d4',
 'README.md':'861ec6c65b1714a84bab4957afd1892f02222d36e7af3904e7d157e117a4054d',
 'article.pdf':'1096ec4611f399976dbe63894685a636550c9e6434b8e233ed1df592ee19f015',
}
BASIS = {
 'placement_bbaf322e5_inventory.json':'d98403f9b1c0c4b75a91502daf0423fcda24cf423bddaa94d1a36b67f7b520ae',
 'review_boundary_sandpile_060e08a07.md':'745b1786d9e8c0eaf8960a29ead88e2ce04dde10e933dfd10fcab3e4575b1ee3',
 'review_compressed_queue_aebfa.md':'e2257697367c244da377241016d7ef8b656407ed3610bf7fac0797ac15c49cf6',
}
ARCHIVES = {
 'nb':('docs/incoming/no_borrowed_firings.zip','390c4c9a6dbe9a7701de8e0b6689a21d60b35c577aa11a9977989c088a8d0d45',16,'no_borrowed_firings','19-no-borrowed-firings-'),
 'cq':('docs/incoming/Compressed_Queue_Diophantine_Research.zip','cd3cfe40497cca4a3b4781a25b37405f5452e0dae26b70163245d80b53ad0a20',13,'Compressed_Queue_Diophantine','20-compressed-queue-'),
}
PATCH_NAME = 'canonical_j3_0ac86bb58_queue_guards.patch'
REPAIRS = {'article.tex': [('Part~XVIII (manuscript~20) accelerates a \\emph{prescribed} closed FIFO macro exactly: the number of executable copies is $\\min(N_{\\rm len},\\lfloor M/a\\rfloor)$ (\\cref{cdc:cq:thm:maxrepeat}), indefinite repetition is the finite word equation $U^{b/d}q=qV^{a/d}$ (\\cref{cdc:cq:thm:conjugacy}), and a supplied infinite loop has an ordinary quartic with unique witnesses (\\cref{cdc:cq:thm:infinitequartic}).', 'Part~XVIII (manuscript~20) accelerates a \\emph{prescribed} closed FIFO macro exactly: for $a=|U|>0$, the number of executable copies is $\\min(N_{\\rm len},\\lfloor M/a\\rfloor)$ (\\cref{cdc:cq:thm:maxrepeat}); indefinite repetition holds exactly when $L\\ge R$, $b\\ge a$ and $U^{b/d}q=qV^{a/d}$, where $d=\\gcd(a,b)$ (\\cref{cdc:cq:thm:conjugacy}). Read-free closed macros ($a=0$) repeat indefinitely from every queue. A supplied infinite loop has an ordinary quartic with unique witnesses (\\cref{cdc:cq:thm:infinitequartic}).'), (", and its elimination at the level of existence is Part~IX's exponentiation boundary (\\cref{cdc:pt:prop:exponential-boundary}).", ". Its ordinary existential elimination follows MRDP; preserving unique fibres in a fixed-dimensional ordinary replacement meets Part~IX's exponentiation boundary (\\cref{cdc:pt:prop:exponential-boundary})."), ('the queue clause is answered by Part~XVIII', 'the queue clause is answered in part by Part~XVIII'), ('The Part answers the queue clause of \\cref{cdc:q:storage}', 'The Part answers the queue clause of \\cref{cdc:q:storage} in part'), ('This answers the queue clause of \\cref{cdc:q:storage}', 'This answers the queue clause of \\cref{cdc:q:storage} in part'), ('\\cref{cdc:q:storage} (queue clause answered)', '\\cref{cdc:q:storage} (queue clause answered in part)')], 'README.md': [('  closed macro; infinite repeatability as the word equation\n  `U^{b/d} q = q V^{a/d}`; a Fine–Wilf pumping threshold', '  closed macro with `a = |U| > 0`; infinite repeatability exactly when\n  `L >= R`, `b >= a > 0`, and `U^{b/d} q = q V^{a/d}`, with\n  `d = gcd(a,b)`; read-free closed macros repeat from every queue;\n  a Fine–Wilf pumping threshold'), ('and answers nothing else. 20 answers\nthe queue clause', 'and answers nothing else. 20 answers in part\nthe queue clause'), ('after `cdc:q:storage` (queue clause\n  answered)', 'after `cdc:q:storage` (queue clause\n  answered in part)')]}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def exact(a, b):
    if type(a) is not type(b):
        return False
    if type(a) is dict:
        return a.keys() == b.keys() and all(exact(a[k], b[k]) for k in a)
    if type(a) in (list, tuple):
        return len(a) == len(b) and all(exact(x, y) for x, y in zip(a, b))
    return a == b


def git(repo, *args):
    return subprocess.run(['git','-C',str(repo),*args],check=True,capture_output=True,timeout=90).stdout


def remove_macro(text, name):
    while True:
        m = re.search(r'\\'+name+r'\{', text)
        if not m:
            return text
        i, depth = m.end(), 1
        while depth:
            need(i < len(text), 'unterminated annotation')
            if text[i] == '{' and text[i-1] != '\\': depth += 1
            if text[i] == '}' and text[i-1] != '\\': depth -= 1
            i += 1
        text = text[:m.start()]+text[i:]


def normalize(text, package, old):
    text = re.sub(r'(?<!\\)%[^\n]*','',text)
    text = remove_macro(text, 'srcnote')
    text = text.replace('cdc:nb:','').replace('cdc:cq:','')
    text = re.sub(r'\\label(?:\[[^]]*\])?\{[^}]*\}', '', text)
    if package == 'nb' and old:
        # Simultaneous declared token renaming, including braced scripts.
        # Repair the single documented malformed subscript before tokenization.
        text = text.replace('\\deg_{\nm adj}', r'\deg_{\mathrm{adj}}')
        text = re.sub(r'([_^])E(?![A-Za-z])', r'\1{\\mathcal R}', text)
        text = re.sub(r'(?<![A-Za-z\\])E(?![A-Za-z])', r'\\mathcal R', text)
        text = re.sub(r'(?<![A-Za-z\\])m(?![A-Za-z])', 'E', text)
    if package == 'cq':
        text = text.replace(r'\qval',r'\code').replace('sec:subtrates','sec:substrates')
    text = text.replace('proveit-mrdp','repo-mrdp')
    return re.sub(r'\s+','',text)


def blocks(text, kind):
    if kind == 'formal':
        rx = r'\\begin\{(theorem|lemma|proposition|corollary|definition|remark|proof)\}(.*?)\\end\{\1\}'
    elif kind == 'display':
        # Negative lookbehind avoids interpreting table row \\[4pt] as \[.
        rx = r'(?<!\\)\\\[(.*?)\\\]|\\begin\{(equation\*?|align\*?|gather\*?|multline\*?)\}(.*?)\\end\{\2\}'
    else:
        need(kind == 'inline', 'unknown kind')
        rx = r'(?<!\\)\$(.*?)(?<!\\)\$'
    out=[]
    for m in re.finditer(rx,text,re.S):
        env = m.group(1) if kind=='formal' else (m.group(2) or 'display') if kind=='display' else 'inline'
        out.append(dict(start=m.start(), environment=env, body=m.group(0)))
    return out


def ordered_match(needles, haystack):
    cursor, result = 0, []
    for i, needle in enumerate(needles):
        found = next((j for j in range(cursor,len(haystack)) if haystack[j]==needle),None)
        need(found is not None, f'missing distinct ordered occurrence {i}')
        result.append(found)
        cursor=found+1
    need(len(set(result)) == len(result), 'reused occurrence')
    return result


def question_bodies(text, package, old):
    if package == 'cq' and old:
        starts=list(re.finditer(r'\\paragraph\{\d+\. [^}]+\}',text))
        end=text.index('\\section{Conclusion}',starts[-1].end())
        return [text[m.end():(starts[i+1].start() if i+1<len(starts) else end)].strip() for i,m in enumerate(starts)]
    return [m.group(1).strip() for m in re.finditer(r'\\begin\{question\}\[[^]]*\](.*?)\\end\{question\}',text,re.S)]


def verify(repo, patch):
    repo=Path(repo).resolve()
    need(git(repo,'rev-parse',COMMIT+'^').decode().strip()==PARENT,'commit parent differs')
    source={n:git(repo,'show',COMMIT+':'+REPORT+'/'+n) for n in PINS}
    need({n:sha(b) for n,b in source.items()}==PINS,'typeset source pin differs')
    basis={n:git(repo,'show',COMMIT+':'+WIP+'/'+n) for n in BASIS}
    need({n:sha(b) for n,b in basis.items()}==BASIS,'review basis pin differs')
    inventory=json.loads(basis['placement_bbaf322e5_inventory.json'])
    archive_records, members, placements = {}, {}, []
    for package,(name,pin,count,inner,prefix) in ARCHIVES.items():
        data=git(repo,'show',ARCHIVE_REF+':'+name)
        need(sha(data)==pin,'archive pin differs')
        payload={}
        with zipfile.ZipFile(io.BytesIO(data)) as z:
            for info in z.infolist():
                path=PurePosixPath(info.filename)
                need(not path.is_absolute() and '..' not in path.parts and '\\' not in info.filename and not stat.S_ISLNK(info.external_attr>>16),'unsafe archive member')
                if info.is_dir(): continue
                need(info.filename not in payload and path.parts[0]==inner,'duplicate/wrong-root member')
                payload[info.filename]=z.read(info)
        need(len(payload)==count,'member count differs')
        for entry in inventory['matched_files']:
            target=entry['path']
            if not (target.startswith(REPORT+'/') and PurePosixPath(target).name.startswith(prefix)): continue
            matches=[m for m in entry['source_matches'] if m['archive']==name and PurePosixPath(m['member']).name == PurePosixPath(target).name.removeprefix(prefix)]
            need(len(matches)==1,'ambiguous source-aware mapping')
            m=matches[0]; b=payload[m['member']]
            need(m['archive_sha256']==pin and sha(b)==entry['sha256'] and len(b)==entry['bytes'],'placement provenance differs')
            need(git(repo,'show',COMMIT+':'+target)==b,'placed companion differs')
            placements.append(dict(package=package,member=m['member'],target=target,sha256=sha(b)))
        members[package]=payload
        archive_records[package]=dict(path=name,git_ref=ARCHIVE_REF,sha256=pin,member_sha256={n:sha(b) for n,b in sorted(payload.items())})
    # Describe omitted artifact identities and same-package byte aliases explicitly.
    unplaced, aliases = {}, []
    for package,payload in members.items():
        selected={v['member'] for v in placements if v['package']==package}
        unplaced[package]=sorted(set(payload)-selected)
        for name in unplaced[package]:
            for v in placements:
                if v['package']==package and payload[name]==payload[v['member']]:
                    aliases.append(dict(package=package,unplaced_member=name,placed_member=v['member'],target=v['target'],sha256=sha(payload[name])))
    need(len(placements)==20 and sum(map(len,unplaced.values()))==9 and len(aliases)==2,'companion identity accounting')
    text=source['article.tex'].decode()
    parent_text=git(repo,'show',PARENT+':'+REPORT+'/article.tex').decode()
    citation_maps={
        'nb':{'dhar':'dhar1998','cairns':'cairns','proveit-h10':'repo-h10','proveit-mrdp':'repo-mrdp','proveit-routing':'repo-rtsources'},
        'cq':{'repo':'repo-cdc','queueprior':'repo-qcint','hkz':'hkz','kocher':'kocher','rankin':'rankin','jez':'jez','cook':'cook','woodsneary':'woods-neary'},
    }
    bib_target=re.findall(r'\\bibitem\{([^}]+)\}',text)
    bib_parent=re.findall(r'\\bibitem\{([^}]+)\}',parent_text)
    for package,mapping in citation_maps.items():
        inner=ARCHIVES[package][3]
        bib_source=re.findall(r'\\bibitem\{([^}]+)\}',members[package][inner+'/article.tex'].decode())
        need(set(mapping)==set(bib_source) and len(mapping)==len(bib_source),'incomplete bibliography map')
        need(all(bib_target.count(v)==1 for v in mapping.values()),'missing/duplicate bibliography target')
    merged=sum(v in bib_parent for m in citation_maps.values() for v in m.values())
    need(merged==7 and sum(map(len,citation_maps.values()))-merged==6,'bibliography merge count')
    # Restrict nb to its own front matter, M19 body, and own appendices;
    # explicitly exclude the neighboring source16 appendix.
    ranges={
      'nb':[(text.index('\\subsection{Manuscript 19:'),text.index('\\subsection{Manuscript 20:')),
            (text.index('\\section{Manuscript 19: a quadratic'),text.index('\\section{Certificate coordinate dictionary\\srctag{16}}')),
            (text.index('\\section{Dependency and audit map\\srctag{19}}'),text.index('\\part{Exponential trajectories:'))],
      'cq':[(text.index('\\subsection{Manuscript 20:'),text.index('\\part{Exact commutation and resource algebra}')),
            (text.index('\\part{Compressed queue traces:'),text.index('\n\\appendix\n',text.index('\\part{Compressed queue traces:')))]}
    transfer={}
    for package,(_,_,_,inner,_) in ARCHIVES.items():
        old=members[package][inner+'/article.tex'].decode()
        old=old[old.index('\\begin{document}'):old.index('\\begin{thebibliography}')]
        scope='\n'.join(text[a:b] for a,b in ranges[package])
        kinds={}
        for kind in ('formal','display','inline'):
            src=blocks(old,kind)
            dst=[dict(v,start=v['start']+a) for a,b in ranges[package] for v in blocks(text[a:b],kind)]
            match=ordered_match([normalize(v['body'],package,True) for v in src],[normalize(v['body'],package,False) for v in dst])
            kinds[kind]=dict(source_count=len(src),matched_distinct_occurrences=len(match),environment_counts=dict(Counter(v['environment'] for v in src)),occurrence_map=[dict(source_occurrence=i,target_occurrence=j,target_line=text.count('\n',0,dst[j]['start'])+1,normalized_sha256=sha(normalize(src[i]['body'],package,True).encode())) for i,j in enumerate(match)])
        qsrc=question_bodies(old,package,True); qdst=question_bodies(scope,package,False)
        qmap=ordered_match([normalize(s,package,True) for s in qsrc],[normalize(s,package,False) for s in qdst])
        labels=re.findall(r'\\label(?:\[[^]]*\])?\{([^}]+)\}',old)
        target_labels=re.findall(r'\\label(?:\[[^]]*\])?\{([^}]+)\}',scope)
        prefix='cdc:'+package+':'
        need(len(set(labels))==len(labels),'duplicate original label')
        mapped=[prefix+x.replace('sec:subtrates','sec:substrates') for x in labels]
        need(all(target_labels.count(v)==1 for v in mapped),'missing/duplicate label')
        transfer[package]=dict(blocks=kinds,source_labels=len(labels),source_label_map=dict(zip(labels,mapped)),questions=dict(source_count=len(qsrc),distinct_target_indices=qmap),source_scope_lines=[[text.count('\n',0,a)+1,text.count('\n',0,b)+1] for a,b in ranges[package]])
    need([transfer[p]['blocks'][k]['source_count'] for p in ('nb','cq') for k in ('formal','display','inline')]==[40,54,409,32,63,549],'coverage census differs: '+repr([transfer[p]['blocks'][k]['source_count'] for p in ('nb','cq') for k in ('formal','display','inline')]))
    need([transfer[p]['questions']['source_count'] for p in ('nb','cq')]==[9,10],'question census differs')
    # Verify the two host macros whose typography/meaning is declared changed.
    need(r'\newcommand{\qval}{\mathsf C}' in text and r'\newcommand{\code}{\mathsf C}' in members['cq']['Compressed_Queue_Diophantine/article.tex'].decode(),'radix macro differs')
    need(r'\newcommand{\Pow}{\operatorname{Pow}}' in text,'host Pow definition differs')
    regressions=0
    for ns,hs in ((['x','x'],['x']),(['a','b'],['b','a']),(['x'],[])):
        try: ordered_match(ns,hs)
        except ValueError: regressions+=1
        else: raise ValueError('ordered matcher accepted missing/reused occurrence')
    need(ordered_match(['x','x'],['x','y','x'])==[0,2],'repeated positive control')
    need(not exact(True,1) and not exact({'v':1},{'v':True}),'typed comparison regression')
    # Two independent, literal queue counterexamples to omitted summary guards.
    def step(q,u,v):
        return q[len(u):]+v if q.startswith(u) else None
    ghost=dict(U='a',V='a',q='',a=1,b=1,d=1,L=0,R=1)
    need(ghost['U']+ghost['q']==ghost['q']+ghost['V'] and step('', 'a', 'a') is None,'resource counterexample')
    shrinking=dict(U='aa',V='a',q='aa',a=2,b=1,d=1,L=2,R=2)
    need('aa'+'aa'=='aa'+'a'*2 and step('aa','aa','a')=='a' and step('a','aa','a') is None,'drift counterexample')
    need(step('','', 'a')=='a' and step('a','', 'a')=='aa','read-free branch')
    # Count comparisons on fixed graph shapes; operations are intentionally uncharged.
    counts=[]
    for n,e in ((2,1),(10,15)):
        counts.append(dict(n=n,E=e,nb_w=11*n+12*e,nb_r=12*n+16*e,projected_w=8*n+12*e,projected_r=9*n+16*e,baseline16_w=13*n+12*e,compact16_w=10*n+6*e))
    need([(v['nb_w'],v['projected_w'],v['baseline16_w'],v['compact16_w']) for v in counts]==[(34,28,38,26),(290,260,310,190)],'sandpile comparison counts')
    need(6*17+3*16+1==151 and 6*1+9*16+3==153,'queue doubling count')
    expected_patch='';repaired={}
    for n,changes in REPAIRS.items():
        original=source[n].decode(); s=original
        for old,new in changes:
            need(s.count(old)==1,'repair context differs'); s=s.replace(old,new)
        repaired[n]=s
        expected_patch+=''.join(difflib.unified_diff(original.splitlines(True),s.splitlines(True),fromfile='a/'+REPORT+'/'+n,tofile='b/'+REPORT+'/'+n))
    need(Path(patch).read_bytes()==expected_patch.encode(),'patch bytes differ')
    with tempfile.TemporaryDirectory(prefix='j3-typesetting-patch-') as temp:
        target=Path(temp)/REPORT;target.mkdir(parents=True)
        for n,b in source.items():(target/n).write_bytes(b)
        subprocess.run(['patch','--batch','--forward','-p1','-i',str(Path(patch).resolve())],cwd=temp,check=True,capture_output=True,timeout=60)
        need(all((target/n).read_text()==s for n,s in repaired.items()),'private patch result differs')
        need((target/'article.pdf').read_bytes()==source['article.pdf'],'PDF mutated')
    changed=git(repo,'diff-tree','--no-commit-id','--name-status','-r',COMMIT).decode().splitlines()
    need(changed==[f'M\t{REPORT}/README.md',f'M\t{REPORT}/article.pdf',f'M\t{REPORT}/article.tex'],'unexpected changes')
    return dict(status='PASS_BOUNDED_SOURCE_TRANSFER_WITH_QUEUE_SUMMARY_GUARD_REPAIR',review_helper_sha256=sha(Path(__file__).read_bytes()),commit=COMMIT,parent=PARENT,typeset_sha256=PINS,review_basis_sha256=BASIS,archives=archive_records,companion_member_placements=placements,distinct_companion_files=len({v['target'] for v in placements}),companion_member_identities=len(placements),unplaced_members=unplaced,unplaced_same_package_byte_aliases=aliases,bibliography_map=citation_maps,bibliography_counts=dict(merged=7,new_source_entries=6,new_review_entries=2),transfer=transfer,normalization=['comments/whitespace and labels','balanced source annotations','cdc:nb:/cdc:cq: prefixes','source19 token m->E and old E->mathcal R simultaneously, including scripts','one documented deg adjacency subscript repair','source20 code->qval, identical mathsf C glyph','source20 sec:subtrates spelling correction','proveit-mrdp citation->repo-mrdp'],matcher_regressions=dict(rejections=regressions,repeated_positive_control=True,exact_type_comparison=True),changed_files=changed,counterexamples=dict(missing_resource_guard=ghost,missing_nondecreasing_length_guard=shrinking,read_free_branch_checked=True),sandpile_comparisons=counts,queue_counts=dict(l=1,c=16,g=17,parent_w=151,parent_r=153,projected_w=97,projected_r=99),patch=dict(filename=PATCH_NAME,sha256=sha(expected_patch.encode()),before_sha256={n:PINS[n] for n in repaired},after_sha256={n:sha(s.encode()) for n,s in repaired.items()},private_application='PASS',pdf_rebuild_required=True),scope='Pinned source19/source20 transfer, new editorial relations and summary-guard counterexamples only. No unchanged author suites or modules, old whole-book proof rereview, PDF build/layout audit, historical novelty judgment, universal arithmetic bound, or future-commit review.')


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,default=Path.cwd())
    p.add_argument('--patch',type=Path,default=Path(__file__).with_name(PATCH_NAME))
    p.add_argument('--expect',type=Path)
    p.add_argument('--output',type=Path)
    a=p.parse_args(); result=verify(a.repo,a.patch)
    if a.expect: need(exact(result,json.loads(a.expect.read_text())),'saved receipt differs')
    if a.output: a.output.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status=result['status'],formal_blocks=sum(result['transfer'][p]['blocks']['formal']['source_count'] for p in ('nb','cq')),companion_files=result['distinct_companion_files']),sort_keys=True))
