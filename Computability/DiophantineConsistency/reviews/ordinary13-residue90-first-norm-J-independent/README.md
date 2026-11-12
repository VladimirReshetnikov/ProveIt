# Independent source review: J=0 branch

The proposed J forcing uses the correct signed first norm and has the stated premises: all four ports are natural representations and the literal 13/90 graph vanishes. If J=0, then q=1, `C=1-F-alpha<=0` because the shifted F and alpha are positive, and `Bt=C*(X+K0)-F<0` because X and K0 are nonnegative. The literal root becomes `Z=-Bt>0`, while the first norm gives `Z²=0`, a contradiction. The isolated branch needs neither beta>0 nor X>0.

The compact-symbolic client combines this proposed branch with the earlier gap and gamma draft but still explicitly assumes `X>=1`; K is an arbitrary standard natural, with no fixed-byte binding shown here. Source signatures, exact norm/root source, explicit premises and finite sign controls were checked, and the author's receipt reproduces. These checks do not elaborate Lean tactics, imports or axioms, establish provider ancestry or prove a model-to-iPRA endpoint.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue90-first-norm-J-independent/check.py | cmp - reviews/ordinary13-residue90-first-norm-J-independent/result.json
python3 -I -S -B research/ordinary13-residue90-first-norm-J-draft/check.py | cmp - research/ordinary13-residue90-first-norm-J-draft/receipt.json
```
