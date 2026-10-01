#!/usr/bin/env python3
"""Construct and verify the shared-resource accelerator from the article."""
from causal_diophantine import Action, compile_accelerator, complete_accelerator

def main():
    actions = [Action.petri('loss_one',(2,),(1,)),
               Action.petri('loss_two',(3,),(1,)),
               Action.petri('shared_read',(1,),(1,))]
    counts = (10**100,10**80,10**90)
    initial = (counts[0]+2*counts[1]+1,)
    system = compile_accelerator(actions)
    certificate = complete_accelerator(actions,initial,counts)
    if certificate is None or not system.check(certificate):
        raise RuntimeError('Certificate generation or verification failed')
    print('Natural witnesses:',len(system.witnesses))
    print('Squared residuals:',len(system.residuals))
    print('Endpoint:',certificate['y_0'])
    print('Polynomial value:',system.value(certificate))
    print('Expanded degree:',system.expanded().degree)

if __name__ == '__main__':
    main()
