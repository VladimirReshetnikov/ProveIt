#!/usr/bin/env python3
"""Recheck the connector-observed Git blobs against a local clone's pinned commit.
No network access is performed. The source manifest records observed blob IDs,
not the output of running this script (a clone was unavailable here).
"""
import argparse, csv, hashlib, pathlib, re, subprocess
PIN='ee10f937fedac0955d28b7b860f4c44fab508204'
BASE='Analysis/GeneralizedRiemannHypothesis/'
TERMS=re.compile(r'coinvariant|same[- ]section|MatchingPartners|EquivariantDifference|coset representative|primitive frame|orbital integral|Haar|exchange identity',re.I)
HERE=pathlib.Path(__file__).resolve().parent

def rows(name):
    with (HERE/name).open(encoding='utf-8',newline='') as f:
        yield from csv.DictReader(f,delimiter='\t')

def git(repo,*args):
    return subprocess.check_output(['git','-C',str(repo),*args])

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('repository',type=pathlib.Path)
    args=ap.parse_args(); repo=args.repository
    git(repo,'cat-file','-t',PIN)
    n=0; hits=[]
    for name,subdir in [('source-audit.tsv',''),('proposal-audit.tsv','docs/proposals/')]:
        for r in rows(name):
            path=BASE+subdir+r['path']
            data=git(repo,'show',f'{PIN}:{path}')
            sha=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            assert sha==r['git_blob_sha1'],(path,sha,r['git_blob_sha1'])
            n+=1
            if subdir:
                for i,line in enumerate(data.decode('utf-8').splitlines(),1):
                    if TERMS.search(line): hits.append((path,i,line[:180]))
            else:
                lines=data.splitlines()
                assert all(1<=int(i)<=len(lines) for i in r['anchors'].split(',')),path
    expected={r['path'].split('/')[0] for r in rows('proposal-audit.tsv')}
    listing=git(repo,'ls-tree','--name-only',f'{PIN}:{BASE}docs/proposals').decode().splitlines()
    assert set(listing)==expected,(listing,expected)
    print(f'{n} Git blobs verified at {PIN}; {len(expected)} proposal directories.')
    print(f'{len(hits)} lexical matches for exchange-related terms in inspected TeX files.')
    for h in hits: print(*h,sep=': ')
    print('A lexical scan is not a mathematical novelty proof; see the report for topic comparison.')
if __name__=='__main__': main()
