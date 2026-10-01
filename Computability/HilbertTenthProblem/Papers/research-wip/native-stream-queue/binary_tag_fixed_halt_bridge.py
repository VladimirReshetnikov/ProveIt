"""Fixed CTS-to-binary-tag rules on the valid clockwise-TM input slice.

Literal local tracks and the unique pending halt event are checked separately.
The TM-to-CTS power-of-two counter is retained, not arithmetically loaded.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import random


THETA = {'e': 'b'*4+'c'+'b'*6,
         '0': 'b'*6+'c'+'b'*4,
         '1': 'b'*8+'c'+'b'*2}


def build_tracks(appendants, halt, s=None):
    """Interleave this fixed table to obtain the one production u."""
    appendants=tuple(appendants);p=len(appendants);beta=10*p;M=beta-1
    assert p>=2 and 0<halt<p and all(set(a)<=set('01') for a in appendants)
    minimum=11*max(p,max(map(len,appendants)))+3
    if s is None:s=minimum+(1-minimum)%M
    assert s>=minimum and s%M==1
    tracks=['b'*s for _ in range(beta)]
    for m,alpha in enumerate(appendants):
        z=(beta-10*m+1)%beta
        tracks[z]='c'*s
        garbage=(THETA['e'][1:]+THETA['e']*(p-1)+'c'*(s-11*p+1)
                 if m==0 else THETA['e']*p+'c'*(s-11*p))
        tracks[(z-4)%beta]=tracks[(z-6)%beta]=garbage
        bits=''.join(THETA[a] for a in alpha);v=len(alpha)
        if m==halt:row='b'+'c'*(s-1)
        elif m==0 and not v:row=garbage
        elif m==0:row=bits[1:]+'c'*(s-11*v+1)
        else:row=bits+'c'*(s-11*v)
        tracks[(z-8)%beta]=row
    assert all(len(row)==s for row in tracks)
    assert all(tracks[i]=='b'*s for i in range(0,beta,2))
    assert all(tracks[i]=='b'*s for i in range(9,beta,10))
    return dict(appendants=appendants,halt=halt,p=p,beta=beta,s=s,
                padding_u_copies=(-11)%M,tracks=tracks)


def materialize(packet):
    tracks=packet['tracks'];s=packet['s'];beta=packet['beta']
    u=''.join(tracks[j][i] for i in range(s) for j in range(beta))
    assert u[0]==u[-1]=='b' and len(u)==beta*s
    return u


def objects(u):return {key:word.replace('c',u) for key,word in THETA.items()}


def initial_word(packet,word):
    assert word and set(word)<=set('01')
    u=materialize(packet);phi=objects(u);k=packet['padding_u_copies']
    return u[1:]+''.join(phi[a]+u*k for a in word)+u


def local_audit(packet):
    u=materialize(packet);phi=objects(u);beta=packet['beta'];s=packet['s']
    p=packet['p'];h=packet['halt'];checks=0
    for m,alpha in enumerate(packet['appendants']):
        z=(beta-10*m+1)%beta
        assert u[z::beta]=='c'*s
        checks+=1
        for a in ('e','0','1'):
            if a!='1' or (m==0 and not alpha):semantic='e'*p
            else:semantic=alpha
            if a=='1' and m==h:
                expected='b'+'c'*(s-1);output='b'+u*(s-1)
            else:
                tail=s-11*len(semantic)+(m==0)
                expected=''.join(THETA[c] for c in semantic)+'c'*tail
                output=''.join(phi[c] for c in semantic)+u*tail
                assert tail>=3
            read=phi[a][z::beta]
            assert read==expected
            assert ''.join(u if c=='c' else 'b' for c in read)==output
            assert (z-len(phi[a]))%beta==(beta-10*((m+1)%p)+1)%beta
            checks+=1
    # Every normal block has even length. On every even entry shift its
    # actually read letters are b, independently of the simulation phase.
    for a in (u,*phi.values()):
        assert len(a)%2==0
        for z in range(0,beta,2):assert set(a[z::beta])<=set('b');checks+=1
    H='b'+u*(s-1)
    for z in range(1,beta,2):
        assert set(H[z::beta])<=set('b')
        assert (z-len(H))%beta%2==0
        checks+=1
    return checks


def active_index_rows(Q):
    """Indices of all specified 1-activation rows in the primary tables.

    Nonhalting states i<Q participate in Stages 1--3. The final state has
    the prescribed overriding halt entry. Counter reset may name any state.
    Unspecified appendants can be empty; they do not occur on this slice.
    """
    assert Q>=2
    z=30*Q+61;rows=[]
    def add(label,indices):rows.extend((label,j) for j in indices)
    add('passive_stage1',[b+j for b in (0,z) for j in range(7)])
    add('passive_stage1_test',[b+j for b in (0,z) for j in range(11,17)])
    add('passive_stage2',[b+j for b in (0,z) for j in range(23,29)])
    for i in range(1,Q):
        add('state_stage1',[b+30*i+j for b in (0,z) for j in (20,25)])
        add('state_stage1_test',[b+30*i+j for b in (0,z) for j in (21,26)])
        add('state_stage2',[30*i+22,30*i+27])
        add('state_stage3',[z+30*i+24,z+30*i+29])
        add('passive_stage3',[30*i+j for j in (*range(31,36),*range(41,46))])
    add('counter_double',[39,40,z+40,41,42])
    add('counter_state_copy',[30*i+60 for i in range(1,Q+1)])
    add('halt',[30*Q+20])
    assert all(0<=j<2*z for _,j in rows)
    assert [(label,j) for label,j in rows if j==30*Q+20]==[('halt',30*Q+20)]
    return rows


def halt_cut_audit(Q,tape,rotation=0):
    """An independently built standard halt configuration and its 1 events.

    The binary tag replaces the unique halt output by H. Only this existing
    suffix can be processed before H; newly appended outputs follow H.
    """
    assert Q>=2 and len(tape)>=2 and set(tape)<=set('ab')
    z=30*Q+61;p=2*z;h=30*Q+20
    count=1<<(len(tape)-1).bit_length()
    state='0'*h+'1'+'0'*(p-h-1)
    cells=['0'*(1+(a=='b'))+'1'+'0'*(p-2-(a=='b')) for a in tape]
    mu='1'+'0'*(z-1)
    word=state+''.join(cells)+mu*count
    assert len(word)%p==0
    rotation%=len(word)
    word=word[rotation:]+word[:rotation];phase=rotation%p
    events=[((phase+j)%p,j) for j,a in enumerate(word) if a=='1']
    hits=[j for m,j in events if m==h]
    assert len(hits)==1
    hit=hits[0];passive={0,1,2,z,z+1,z+2}
    assert all(m==h or m in passive for m,_ in events)
    assert all(m!=h for m,j in events if j>hit)
    # The broader passive class includes partially marked counters.
    assert h not in {b+j for b in (0,z) for j in range(7)}
    return dict(states=Q,tape_cells=len(tape),counter=count,rotation=rotation,
                unique_halt_activation=True,pending_suffix_hits=0)


def verify():
    rng=random.Random(196810);tracks=lengths=frames=cleanup=0;examples=[]
    for case in range(48):
        p=rng.randrange(2,7);halt=rng.randrange(1,p)
        alphas=[''.join(rng.choice('01') for _ in range(rng.randrange(5))) for _ in range(p)]
        packet=build_tracks(alphas,halt);u=materialize(packet);phi=objects(u)
        tracks+=local_audit(packet);beta=packet['beta'];M=beta-1;k=packet['padding_u_copies']
        blocks={a:phi[a]+u*k for a in '01'}
        assert Counter(blocks['0'])==Counter(blocks['1'])
        encoded_len=lambda w:w.count('b')*(beta+2)+w.count('c')
        assert encoded_len(blocks['0'])==encoded_len(blocks['1'])
        for n in range(1,17):
            total=(len(u)-1)+n*len(blocks['0'])+len(u)
            assert total%M==len(u)%M==1 and len(blocks['0'])%M==0
            lengths+=1
        # Actual complete initial words, not merely their length formulas.
        word=''.join(rng.choice('01') for _ in range(rng.randrange(1,7)))
        initial=initial_word(packet,word)
        assert initial[-1]=='b' and len(initial)%M==1
        e=lambda w:''.join('1'+'0'*beta+'1' if c=='b' else '1' for c in w)
        E=lambda w:e(w[:-1])+'1'+'0'*beta
        assert E(initial)==e(u[1:])+''.join(e(blocks[a]) for a in word)+E(u)
        frames+=1
        if case<3:
            examples.append(dict(p=p,halt=halt,beta=beta,s=packet['s'],
                appendants=alphas,u_length=len(u),u_sha256=hashlib.sha256(u.encode()).hexdigest(),
                padding_u_copies=k,block_length=len(blocks['0']),
                binary_block_length=encoded_len(blocks['0']),initial_word=word))
    rows=0
    for Q in range(2,65):rows+=len(active_index_rows(Q))
    cuts=[]
    for _ in range(192):
        Q=rng.randrange(2,12);tape=''.join(rng.choice('ab') for _ in range(rng.randrange(2,25)))
        cuts.append(halt_cut_audit(Q,tape,rng.randrange(100000)))
    # For every finite all-b tail, b->b reduces length by beta-1. On the
    # congruence slice its last nonempty word is exactly b.
    for beta in range(2,37):
        for j in range(1,33):
            n=1+j*(beta-1)
            while n>=beta:n-=beta-1
            assert n==1;cleanup+=1
    return dict(status='PASS_BINARY_TAG_FIXED_HALT_BRIDGE',
        local_literal_track_and_even_cleanup_checks=tracks,
        fixed_morphism_length_checks=lengths,full_binary_endpoint_frames=frames,
        primary_table_activation_rows=rows,standard_halt_cut_checks=len(cuts),
        all_b_cleanup_checks=cleanup,examples=examples,
        counter_contract='initial c=2^ceil(log2 tape_cells), tape_cells>=2; unpaid as ordinary-integer input',
        scope='Fixed production independent of input; halting equivalence on the valid Neary-Woods clockwise-TM CTS slice. No arbitrary-CTS multiple-hit theorem, no materialized universal u, no paid ordinary-input compiler and no new universal arithmetic bound.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status'])
