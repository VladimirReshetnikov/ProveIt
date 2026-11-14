#!/usr/bin/env python3
"""Exact, offline graph-novelty replay; no consistency theorem is proved here.

Matches even a 194-state reachable component of a larger supplied table. Allows
arbitrary state renaming/root, reflection and global symbol exchange, ignoring
the final halt transition's write/move. Symbol exchange is a conservative
structural screen, not an assertion about preserving the zero-blank run.
"""
import argparse,hashlib,json,pathlib
from inventory import parse,rooted

def main():
    here=pathlib.Path(__file__).resolve().parent
    ap=argparse.ArgumentParser()
    ap.add_argument('candidate',nargs='?',type=pathlib.Path,default=here.parent/'artifacts/pa194_tdy.tm')
    ap.add_argument('--corpus',type=pathlib.Path,default=here/'corpus_tables.json')
    a=ap.parse_args();cb=a.candidate.read_bytes();m=parse(cb)
    assert m is not None
    n=len(m[1]);forms=set()
    for q in m[1]:
        for mirror in (False,True):
            for flip in (False,True):
                size,key=rooted(m,q,mirror,flip,True)
                if size==n:forms.add(key)
    assert forms,'Candidate has no spanning root'
    tested=0;components=0;matches=[]
    corpus=json.loads(a.corpus.read_text())
    for r in corpus:
        data=r['text'].encode('ascii')
        assert hashlib.sha256(data).hexdigest()==r['sha256']
        p=parse(data);assert p is not None;tested+=1
        if len(p[1])<n:continue
        for q in p[1]:
            size,key=rooted(p,q,False,False,True)
            if size!=n:continue
            components+=1
            if key in forms:matches.append({'sha256':r['sha256'],'root':q,'paths':r['paths']});break
    result={'candidate_sha256':hashlib.sha256(cb).hexdigest(),'candidate_states':n,
            'frozen_byte_forms_checked':tested,'reachable_components_of_candidate_size':components,
            'exact_matches':matches,'comparison':'literal canonical tuple equality; no hash-only identity inference',
            'symmetries':['state renaming','any spanning root','reflection','global symbol exchange','ignore terminal write/move'],
            'scope':'All recognized tables frozen in corpus_tables.json, including same-size reachable components of larger tables.'}
    print(json.dumps(result,indent=2))
    assert not matches,'Candidate occurs in the frozen corpus'
if __name__=='__main__':main()
