# Unvalidated tagged radix-two prototype

This folder is a quick source/compiler cost experiment, **not an accepted Turing machine**. Its table fails a source-frame contract and must not be treated as a consistency machine.

The proposed constructors are `I(a,b)=2p(2a,b)`, `U(x,A)=2p(2A+1,x)`, `M(a,b)=2p(2a,b)+1`, and `E(a,b)=2p(2a+1,b)+1`. The accompanying mathematical note discusses their bijective recoding. All four constructors share doubling of the first paired operand.

The experimental source puts first-operand doubling after the constructor's stack unpairing. It reuses the obsolete four-increment selector as a doubled-Y selector and introduces six fixed controls. Implication and membership use the even constructor; universal and equality use a constructor with one extra scratch-X increment. Membership/equality then add one to the result. The AX word shrinks from 190 to 154 expanded macro tokens.

The naive tree prices 140 fixed controls + 71 readers − 5 individually possible folds = 206 states. This is an **optimistic unvalidated price**, not a realized 206-state machine. Its primitive source-frame replay fails at instruction 11, the zero branch of the first stack-unpair decrement. Diagnosis: changing native control 90 also changes an existing fixed decoder-fold provider used outside the constructor; the old provider path is required there. Keeping a distinct provider or unfolding that fold would add overhead, and no corrected improvement was found.

`../tag2_price.py` reproduces the experiment and reports the failed contract. The source and raw table are retained so the concrete obstruction is inspectable. No extensive optimization or completed physical proof was performed for this prototype. Upstream provenance and licenses are those in the packet root.
