#!/usr/bin/env python3
"""Pinned finite algebra supporting the U15 faithful-parabolic obstruction.
The surface theorem is proved in the companion note, not by matrix sampling.
"""
import argparse
import hashlib
import json
from math import gcd
from pathlib import Path

PINS = {
 'u15_unary_block_interface.py': '07c19ad5a37267fa31391186ad041297ab99e8bf2739905443658a04aa37440a',
 'u15_unary_block_interface.json': 'a08e400d61ae5df0a25916f899d7e1e9e0225bc1d1d40052d4dc89ed435c30a0',
 'u15_unary_block_interface.md': 'cdc686700af3545609796034e0a2c906bd0438b6bcabc0c0b267954cc9d20452',
 'group_directed_semigroup193.json': 'c802f1ca0fde3cfcc856dd0f14ea2bf6270e1a9a924fe9743ee00c4336891639',
 'group_directed_semigroup193.md': '75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e',
 'matrix193_power_block_obstruction.md': '60f442caa77c68f11c73a4995fbebc4582a0ef64b3a9e41dfd68c27d8782d978',
}
KEEN = {'title':'Canonical polygons for finitely generated Fuchsian groups',
        'author':'Linda Keen','volume':'Acta Mathematica 115, pages 1-16',
        'doi':'10.1007/BF02392200','used_sections':'3 (Theorem 2), 4 (standard peripheral presentation)',
        'reading_pdf_sha256':'0b00afd3ed83b9412489544a980b59cb5068e896f25406b26ceb926f7d6a7e1a',
        'pdf_url':'https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6002-11511_2006_Article_BF02392200.pdf',
        'replay_fetches_or_requires_pdf':False}


def need(ok, message):
    if not ok: raise ValueError(message)


def sha(raw): return hashlib.sha256(raw).hexdigest()


def exact(a,b):
    if type(a) is not type(b): return False
    if isinstance(a,dict): return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,list): return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


def reduce(word):
    out=[]
    for a in word:
        if out and out[-1]==-a: out.pop()
        else: out.append(a)
    return out


def inverse(word): return [-a for a in reversed(word)]


def substitute(word, images):
    out=[]
    for a in word: out.extend(images[a] if a>0 else inverse(images[-a]))
    return reduce(out)


def abelianize(word):
    return [sum(1 if a==i else -1 if a==-i else 0 for a in word) for i in (1,2)]


def perm_mul(a,b): return tuple(a[b[j]] for j in range(len(a)))


def perm_power(a,n):
    out=tuple(range(len(a)))
    for _ in range(n): out=perm_mul(out,a)
    return out


def mm(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def det(a): return a[0][0]*a[1][1]-a[0][1]*a[1][0]


def E(j): return [[1+4*j,2],[-8*j*j,1-4*j]]


def matrix_word(word, letters):
    out=[[1,0],[0,1]]
    for a in word: out=mm(out,letters[a])
    return out


def verify(root):
    for name,pin in PINS.items(): need(sha((root/name).read_bytes())==pin,'pin '+name)
    ancestor=json.loads((root/'u15_unary_block_interface.json').read_text())
    packet=json.loads((root/'group_directed_semigroup193.json').read_text())['packet']
    codes=packet['top_codes']; W='01010111'
    need(ancestor['encoded_block']['word']==W,'actual universal block')
    old=[1,2]*3+[2,2]
    new=substitute(old,{1:[1,-2],2:[2]})
    need(new==[1,1,1,2,2],'W=c^3 b^2')
    need(substitute(new,{1:[1,2],2:[2]})==old,'inverse Nielsen substitution')
    need(abelianize(old)==[3,5] and abelianize(new)==[3,2],'exact homology')
    need(gcd(*abelianize(old))==1,'proper power exclusion by homology')
    c=(1,2,0); b=(1,0,2); identity=(0,1,2)
    need(perm_mul(perm_power(c,3),perm_power(b,2))==identity,'relator killed in S3')
    need(perm_mul(c,b)!=perm_mul(b,c),'nonabelian relator quotient')
    group={identity}; pending=[identity]
    while pending:
        a=pending.pop()
        for generator in (c,b):
            value=perm_mul(a,generator)
            if value not in group: group.add(value); pending.append(value)
    need(len(group)==6,'quotient image is entire S3')
    blocks=[]
    for i in range(1,17):
        r=8*i-5; word=[1,2]*r+[2,2]
        image=substitute(word,{1:[1,-2],2:[2]})
        need(image==[1]*r+[2,2] and gcd(r,r+2)==1,'ordinary symbol algebra')
        cycle=tuple(list(range(1,r))+[0]); flip=tuple([1,0]+list(range(2,r)))
        need(perm_mul(perm_power(cycle,r),perm_power(flip,2))==tuple(range(r)), 'ordinary symbol quotient relator')
        need(perm_mul(cycle,flip)!=perm_mul(flip,cycle),'ordinary symbol quotient nonabelian')
        blocks.append({'i':i,'c_exponent':r,'b_exponent':2,'old_abelianization':[r,r+2],
                       'finite_nonabelian_quotient_degree':r})
    orientable=[[g,boundary] for g in range(3) for boundary in range(1,5) if 2*g+boundary-1==2]
    nonorientable=[[k,boundary] for k in range(1,4) for boundary in range(1,4) if k+boundary-1==2]
    need(orientable==[[0,3],[1,1]] and nonorientable==[[1,2],[2,1]],'rank-two core inventory')
    # In the one-crosscap, two-boundary case, b -> a^2 b is a Nielsen automorphism.
    need(substitute([1,1,2],{1:[1],2:[-1,-1,2]})==[2], 'nonorientable primitive peripheral')
    need(abelianize([1,1,2,2])==[2,2] and any(x%2 for x in abelianize(old)), 'Klein peripheral homology exclusion')
    current=matrix_word(W,{letter:E(codes[letter]) for letter in ('0','1')})
    need(current==ancestor['encoded_block']['matrix'] and det(current)==1,'pinned current matrix')
    need(current[0][0]+current[1][1]==-8942,'current trace')
    # Faithfulness is essential: collapsing both letters to P makes W unipotent.
    P=[[1,2],[0,1]]; collapsed=matrix_word(W,{'0':P,'1':P})
    need(collapsed==[[1,16],[0,1]],'explicit nonfaithful parabolic boundary')
    return {'status':'PASS','source_sha256':sha(Path(__file__).read_bytes()),'dependency_pins':PINS,
      'primary_reading':KEEN,'W':W,'old_basis_word':old,'new_basis_word':new,
      'old_abelianization':[3,5],'new_abelianization':[3,2],
      'nonprimitive_certificate':{'c_permutation':list(c),'b_permutation':list(b),'image_order':6,
         'image_elements':[list(v) for v in sorted(group)],'relator_maps_to_identity':True,'image_nonabelian':True},
      'orientable_core_types':orientable,'nonorientable_core_types':nonorientable,
      'ordinary_symbol_checks':blocks,'current_matrix':current,'current_trace':-8942,
      'nonfaithful_boundary':{'letter_0':P,'letter_1':P,'W_matrix':collapsed,'group_injective':False},
      'theorem':'Every faithful F2-to-SL2(Z) representation maps W to a hyperbolic matrix; no positive power is parabolic. The note also proves the GL2(Z) extension.',
      'checked_scope':'Finite word/permutation/matrix ingredients only; rank-two surface and full obstruction proofs are in the note.',
      'uniform_theorem_inferred_from_matrix_search':False,'matrix_search_performed':False,
      'new_full_alphabet_embedding_emitted':False,'new_semigroup_array_emitted':False,
      'unbounded_membership_certificate_emitted':False,'new_Diophantine_bound_claim':False,
      'predecessor_or_archived_Python_executed':False}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    mode=parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--output',type=Path); mode.add_argument('--expect',type=Path)
    args=parser.parse_args(); result=verify(args.root.resolve())
    serialized=json.dumps(result,sort_keys=True,indent=2)+'\n'
    need(exact(result,json.loads(serialized)),'typed JSON roundtrip')
    if args.expect: need(exact(result,json.loads(args.expect.read_text())),'exact saved receipt')
    else: args.output.write_text(serialized)
    print('PASS: exact W=c^3 b^2, nonabelian S3 quotient, rank-two core inventory, 16 ordinary-symbol cases, current trace -8942.')


if __name__=='__main__': main()
