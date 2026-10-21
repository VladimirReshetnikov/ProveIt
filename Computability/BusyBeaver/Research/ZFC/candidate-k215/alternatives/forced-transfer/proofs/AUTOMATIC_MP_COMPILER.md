# Automatic transfer after cache-return MP

Define M(x) as the calibrated cache-return MP(x) followed immediately by short transfer S. AX and explicit S remain available. With y=d+x, M succeeds and halts if y=1; otherwise its successful result is (y,tail(w),0,head(w)). A failed M gives (0,tail(w),y,head(w)). These are the literal sequential semantics, including zero aliases.

A crucial unconditional identity is M(0):(t,w,0,h) -> (0,tail(w),0,head(w)). It never halts: on success y=0; on failure MP clears cache before S. Thus M0 is a top-discarding stack pop even when its equality comparison succeeds. This avoids assuming any numerical non-equality for arbitrary incoming stores.

Write D=AX(0;0,0), the unchanged ten-head axiom command. Its saved list has incoming top last and its second half, once D has reset parameters, consists of zeros followed by the saved incoming top. Direct count gives:

PUSH = D; M(0)^9; D; M(0)^10 -> (0,[t;w],0,0).
DISCARD = D; M(0)^10; D; M(0)^10 -> (0,w,0,0).

Both identities hold for arbitrary t,w,d,h; all M0 calls have d=0 because AX reset it. None can halt. The second D creates the required trailing zero cache without risking a transfer of an arbitrary saved top.

H=D;S^11 retains the inherited top-preserving one-head removal interface. J(u)=PUSH;M(u), from (0,w,0,0), returns (0,w,u,0). For u>0 its comparison fails because I(0,u)>0 while cache is zero. For u=0 its comparison may succeed, but the unconditional M0 identity gives the same result. This uniform J is intentional, not an overlooked zero-alias case.

Every inherited row selection, bundle selection and generalization block works using these new PUSH and J auxiliaries. The logical inference block is:

DISCARD; PUSH; B_major; PUSH; B_minor; PUSH; S; S; M(Y).

Immediately before M(Y), the exact store is (A,[0;w],0,I(A,Y)). Successful cache-return MP places Y in cache, and the automatic S consumes the reserved zero, giving (Y,w,0,0), or halting if Y=1. No final explicit S is needed. Induction therefore gives a strong compiler from arbitrary numerical (t,w,0,0), not only safe stacks.

Soundness is sequential soundness of old MP then old S. The conservative stack effect is now minus one for both S and M and plus ten for AX. Old scheduler credit bounds do not apply verbatim. Parent's finite grammar check gives debt three when scheduling starts at candidate one, but an all-natural debt proof and blank calibration remain separate obligations.

## Source and measured physical barrier

automatic_mp.sites.json has 201 DAG nodes and 4,709 leaves. The exact layout is ((selector-and-commands,clearT),transfer-tail). Outer CD3 chooses explicit S on zero; inner CD3 chooses MP on zero and AX otherwise. The AX-only CC3 returns to the scheduler; MP ends immediately before S's clearT. The scheduler and arithmetic macro bodies are unchanged.

The source's exact selector edges are recorded in AUTOMATIC_MP_PRICE.json. It is not accompanied by a physical runtime claim. Reassociation of all ten closed factors tested 4,862 shapes, of which 48 preserve this ordinal CFG. Their source counts are 201 or 202, all have zero-runs at least seven, and every owned allocation fails a missing primitive-interface check. A provisional manually supplied right-CD3/right-CC3 interface reaches a dirty-prefix rejection instead. No machine from this family is currently calibrated.
