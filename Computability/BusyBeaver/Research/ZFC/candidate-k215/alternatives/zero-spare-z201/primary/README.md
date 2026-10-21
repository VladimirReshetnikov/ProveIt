# Z201: a newly calibrated215-state command-order machine

Native machine: z201.native.tm (start74, dispatcher84, halt254).
Dense machine: z201.tm (start0, dispatcher83, halt215,215 working states).
Source: sites.json, order NIP/MP/DROP; AX tags unchanged.

The only transition change from the archived order201 table is198/0: write0 rather than1, allocating a zero-valued spare. Changing start to74 then bootstraps a genuine safe root after570263 steps: (N,T,W,A,D,H,X,Y,L)=(5,0,0,0,1,0,0,0,0). The earlier118411-step frame is explicitly unsafe and is not the consistency seed. Its four commands NIP,NIP,DROP,MP(1) discharge the contamination without halting.

PROOF.md gives the ordinary mathematical calibration and explicit inherited assumptions. It uses the empty theorem stack at the later safe root and arbitrary-natural counter calibration, not a protected-tail estimate. This is not a new proof-assistant theorem or a214-state result.

Run `python3 -B verify.py` for portable saved-output audits, native/dense literal blank replay, full tape reconstruction, source reconstruction, dual source graphs, finite435-primitive discharge, graph nonisomorphism, exact ordered runtime cases, affine positivity and full row coverage. Python standard library only; no solver or network is needed.

Run `python3 -B verify.py --full-runtime /tmp/new-z201-runtime` to additionally reconstruct every symbolic runtime derivation over arbitrary natural registers, gaps and finite nonempty natural spare lists. Choose a nonexistent output directory. The inherited core checker is byte-for-byte preserved. Fresh symbolic induction takes several minutes; the ordinary fast audit checks the saved theorem receipts but does not independently reconstruct the induction derivations.

Attribution and inherited proofs are under inherited/baseline, inherited/licenses, and inherited/research/command_family/FAMILY_PROOF.md. The contribution is the newly calibrated order201/backend/start composition, complete safe initialization, fresh universal runtime, independent finite checks and explicit candidate-specific calibration. The numerical calculus and strong proof compiler remain inherited dependencies.
