# Exact AX and arbitrary-tail compiler connections

This supplement binds the ordinary protected-tail argument to retained source declarations. It adds no executed source, binary or Lean result.

## Interrupted AX: fields and final value

`L2Lib219.AS` declares registers in order `np,tw,ws,ac,p1,p2,s1,s2,pl`. At a command root, `L2Root219.toAS` identifies `p1=d` and `p2=h`. `L2Macros219.Clean` requires only `s1=s2=0`; it does not require theoremhood or a zero cache.

The existing 629-transition peer checkpoint at source ordinal161 is therefore

```
st = (np=1, tw=2, ws=67, ac=2, p1=0, p2=1, s1=0, s2=0, pl=0).
```

It satisfies `Clean` while its cached formula is falsum. Register3's value2 is `ac`, not the cache. The existing ordinary macro correspondence places it at the suffix represented by `L2Axioms219.f305`.

Three declarations are relevant:

1. `l305 st hc` is a finite structured run of node305 to `f305 st`, with a **normal** exit. It requires `Clean st`, not theoremhood. Thus the cached falsum does not trigger an intervening NIP in this suffix.
2. `e305` gives the exact value for every `AS`, without cleanliness assumptions.
3. `gateF` clears `ac,p1,p2`. The final fields in `e305` are `0,0,0,0,st.s2,second(unP st.pl)` after the first three fields. Hence both scratch values and the proof list are zero for this checkpoint.

Substitution of the checkpoint into `e305` gives

```
B = bundle222 0 1 2
S = P (rho1 0 1)
      (P (rho2 0 1 2)
        (P (rho3 0 1 2)
          (P (rho4 0 1 2)
            (P (rho5 0 1 2)
              (P (rho6 0 2)
                (P (growG 0 1 2)
                  (P (rho8 0 1 2 0) 67)))))))
f305 st = (1,B,S,0,0,0,0,0,0).
```

The gate is open because `2!=0` and `2!=1`; `B` is a native bundle axiom. The final cache is truth0. Since `67=P (wal 0 F) (P F 0)`, the ten conceptual stack entries are the eight row instances, `Q_0(F)`, and `F`. The suffix adds **eight**, while every later complete AX adds **ten**: two old/generated inputs and these eight row instances. This distinction is why the protected-tail schedule begins at the completed command root, not at ordinal161.

The macro boundary has a useful alternate description: from normal AX input `(1,F,0,2,0,F,0,0,0)`, `par1`, `par2`, `wal`, `readp2` with an empty list, and `par3` produce exactly the same suffix input `(1,2,67,2,0,F,0,0,0)`. This explains the two bad old entries, but is not used to treat them as theorems.

The final tuple is `toAS s` for `Enum222.St s=(pl=0,np=1,tw=B,ws=S,d=0,h=0)`. That is exactly the state shape covered by the protected-tail theorem. No numeric evaluation of the enormous bundle or stack code is needed.

## Root command and source boundary

`L2Root219.root_step` connects every abstract `enumStep` to a normal root run or to a halting root run, for arbitrary `Enum222.St`. `root_some`, `root_none`, and `iter_iff` iterate this correspondence without assuming `Good ws`. Consequently the new abstract seed theorem fits their interface directly.

There are three different proof boundaries:

- The retained Lean declarations above are exact statements about `Dag219`/`Enum222`; this work only read them and did not compile them.
- The accepted primary218 source has ordinary all-natural equivalence to its exact K219 predecessor through the submitted source construction and runtime/calibration lineage. Its primitive word is not literally the maintained `Dag219` word. Applying the `f305` contract at primary218 ordinal161 uses the inherited ordinary macro correspondence; no new exact Lean partial-entry bridge is claimed here.
- The new relay217 binary table currently has a failed complete runtime check. None of the abstract or ordinary source arguments bypasses that failure. A final machine claim requires a valid source/binary bridge for the repaired table and the initial full-tape entry transport.

## Completeness above an arbitrary tail

The key existing `Enum222.Contract p X` is

```
forall T S,
  cexec p (T,S,0,0) = none
  or cexec p (T,S,0,0) = some (X,S,0,0).
```

There is no `Good S` premise. `discard`, each `leaf_contract`, `bundle_contract`, `gen_contract`, and `mp_contract` are proved with the same universally quantified tail. `build` consequently assigns such a block `p` to every derivation of falsum. In particular, proof blocks do not need to discard or prove the contents of the inherited tail. Their early-halting alternative is already enough for completeness.

For an arbitrary incoming working tuple `(t,S,d,h)`, prepend

```
START_U = AX(c=0,x=1,y=1,u=U).
```

The exact `cstep_ax` equation yields

```
T' = gate(d+1,h+1,0)
S' = axStack(d+1,h,h+1,0,U,t,S)
START_U(t,S,d,h) = (T',S',0,0).
```

The block `p` either halts or returns `(F,S',0,0)`. In the latter case the three-command suffix `DROP0,NIP0,NIP0` first pushes this newly derived F, then reads it into the cache, then halts. It never needs to reach the old tail S.

To cover an arbitrary finite candidate cutoff, let `R` be the proof-list pointer for the fixed nonempty tail `p ++ [DROP0,NIP0,NIP0]`. The candidate for the whole program is

```
N_U = P(3, P(1, P(1, P(U,R)))).
```

By pairing bounds, `N_U >= U`. Choosing `U>=np` provides a successful candidate at or above any starting cutoff. Each prior finite proof list drains unless it already halts, so this candidate is eventually executed in a nonhalting run. This is the Source146 arbitrary-cutoff extension, with the universally quantified `Contract` interface checked directly against `Enum222`. The maintained `Enum222.complete` itself states the zero-seed theorem; it does not by itself state the cutoff extension. The ordinary extension is explicitly linked through the retained Source146 `general_seed_lemma.md`.

For the new protected-tail seed, soundness follows from the independent schedule induction and completeness follows from this cofinal compiler family. They do not use contradictory premises: soundness proves the old tail is never read in the actual candidate order, and completeness constructs a later block that works above whichever tail has accumulated by then.
