#!/usr/bin/env python3
"""Finite controls for the proof-carrying command interpreter."""
import hashlib
import json
import proof_carrying as P

C = P.C
EXTRA_PINS = {
    'vendor/Foundation/Foundation/FirstOrder/Arithmetic/HFS/Vec.lean':
        'cd3fa39802e20703d25499cb6ae7993b02e7bc910aaae3b3ce7b37314864af1c',
    'vendor/Foundation/Foundation/FirstOrder/Arithmetic/IOpen/Basic.lean':
        'd984cb8ac65bba359d04323627dc2088a5de781eb20daaa3b4d22c272ce839f8',
    'PA196/Commands/Coding.lean':
        'd7ba0cb2fe144e4cd3113c91a1c5db3eab3781bdc609adede37e6af8b6d82bd6',
    'PA196/Arithmetic/CommandWord.lean':
        '9ebd3fcf70c69476de8badbfbfe859e1cd1f497b71926e66f4450f5d6b8553d7',
    'PA196/Arithmetic/CommandInternal.lean':
        '324dc8ab54ccd22ce54e1f783685459d6d0f47439c93631e128b1fd0ce139f6b',
    'PA196/Arithmetic/CommandStep.lean':
        '3f2496516c578a99c3bf5d97b598198b838b80e43bed7dce5d99ab2eabfa8ab1',
}


def signature(values):
    h = hashlib.sha256()
    for x in values:
        data = x.to_bytes((x.bit_length()+7)//8, 'big')
        h.update(len(data).to_bytes(8,'big'))
        h.update(data)
    return h.hexdigest()


def result(name, commands, initial_store=(0,0,0,0), initial_proofs=(739,0,739)):
    out = P.run_word(commands, initial_store, initial_proofs)
    P.require(out['kind'] == 'live', 'unexpected halt')
    return {'name':name, 'steps':len(commands),
            'store_bit_lengths':[x.bit_length() for x in out['store']],
            'proof_bit_lengths':[x.bit_length() for x in out['proofs']],
            'state_sha256':signature(out['store']+out['proofs']),
            'checker_and_stack_invariant':P.invariant(out['store'],out['proofs'])}


def main():
    for p,h in {**C.PINS, **EXTRA_PINS}.items():
        P.require(hashlib.sha256((C.ROOT/p).read_bytes()).hexdigest()==h,
                  'source hash mismatch: '+p)
    P.require(P.TRUTH==C.leaf(8,0,0,0,0) and C.verify(P.TRUTH)==1, 'bad truth')
    tests = [
      result('zero_underflow', [('shift',)]),
      result('zero_alias_mp_then_underflow',[('mp',0),('shift',)]),
      result('failed_mp_then_guarded_ax',[('mp',3),('ax',0,0,0)]),
      result('guarded_ax_and_nine_shifts',[('ax',0,0,0)]+[('shift',)]*9),
      result('unguarded_ax',[('ax',1,0,0)]),
      result('ghost_underflow',[('shift',)], (0,0,0,0), (739,C.pair(42,0),739)),
    ]
    s = (0,0,0,0)
    P.require(not P.invariant(s,(0,0,739)), 'rejected top certificate passed')
    P.require(not P.invariant(s,(739,0,0)), 'rejected head certificate passed')
    s1 = P.numeric_step(s,('ax',0,0,0))
    P.require(not P.invariant(s1,(739,0,739)), 'missing stack proofs passed')
    # These deliberately invalid stores test only which proof slot halt selects;
    # no accepted proof of 1 is claimed.
    P.require(P.numeric_step((1,0,0,0),('shift',)) is None and
              P.proof_step((1,0,0,0),(101,0,202),('shift',)) == ('halt',101),
              'top-slot halt selection')
    P.require(P.numeric_step((0,0,0,1),('shift',)) is None and
              P.proof_step((0,0,0,1),(101,0,202),('shift',)) == ('halt',202),
              'head-slot halt selection')
    for cmd in [('shift',),('mp',0),('mp',3),('ax',0,0,0),('ax',1,2,3)]:
        P.require(P.decode_atom(P.atom_of(cmd)) == cmd, 'atom round trip')
    # Payload tails are intentionally noncanonical; the exact decoder ignores
    # them. These exercise arbitrary model-coded atoms, not only emitted atoms.
    examples = [(C.pair(0,4),('shift',)),
                (C.pair(1,C.pair(3,4)),('mp',3)),
                (C.pair(3,C.pair(0,C.pair(0,5))),('ax',1,0,0))]
    for atom,cmd in examples:
        P.require(P.decode_atom(atom) == cmd, 'noncanonical atom mismatch')
        P.require(P.run_atoms([atom]) == P.run_word([cmd]), 'atom execution mismatch')
    for a in range(20):
        for b in range(20):
            P.require(P.hfs_uncons(P.hfs_cons(a,b)) == (a,b), 'HFS pair mismatch')
    words = [[],[('shift',)],[('mp',0),('shift',)],
             [('ax',0,0,0)]+[('shift',)]*9]
    for commands in words:
        atoms = [P.atom_of(cmd) for cmd in commands]
        P.require(P.run_atoms(atoms)['kind'] == 'live', 'unexpected word halt')
        P.require(P.extract_hfs_word(P.hfs_word(atoms)) == 0, 'extractor mismatch')
    report={'source_pins':{**C.PINS, **EXTRA_PINS},'tests':tests,'truth_certificate':P.TRUTH,
            'negative_invariant_controls':3,'synthetic_halt_slot_controls':2,
            'canonical_atom_controls':5,'noncanonical_atom_controls':len(examples),
            'foundation_hfs_pair_controls':400,'finite_live_hfs_words':len(words),
            'scope':'Standard-Nat finite controls; no PA proof, literal-TM binding, or accepted contradiction.'}
    print(json.dumps(report,indent=2,sort_keys=True))


if __name__=='__main__':
    main()
