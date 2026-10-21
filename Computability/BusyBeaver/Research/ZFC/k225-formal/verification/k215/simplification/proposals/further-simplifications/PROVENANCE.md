# Provenance and attribution

This follow-up was prepared on 21 October 2026 to review recent K215 proof commits and identify further proof simplifications. It is distinct from the earlier `K215_Proof_Simplification_2026-10-21.zip` delivery. No prior sealed release file is changed.

## Pinned upstream material

The principal source repository is [VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt), pinned at [beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc](https://github.com/VladimirReshetnikov/ProveIt/commit/beaabc8e3ba961a8892d35a0683c2ed52e4ab4dc). Topic source-pin JSON records identify exact repository paths and Git blobs. Runtime and calibration records also supply SHA-256/length checks. The outer source audit independently checks all bundled pin records. Repeated identical files in different topic directories are kept to make each topic understandable on its own.

The historical placement-only freshness observation is separately recorded at [62f0f95e2b2df5b380ae502eb65bd64f1ee90209](https://github.com/VladimirReshetnikov/ProveIt/commit/62f0f95e2b2df5b380ae502eb65bd64f1ee90209). It verifies the compared tree entries and placement event only; it is not a new compilation or a claim that every repository object was re-audited.

The later production adoption at [de9fdb0873b36d049d075a5c0568f2dfcff28e7a](https://github.com/VladimirReshetnikov/ProveIt/commit/de9fdb0873b36d049d075a5c0568f2dfcff28e7a) is audited separately under `recent_commits/phase5_refresh/`, with source/evidence pins at [0359ebda60aaf52758358e1450a04988136db67e](https://github.com/VladimirReshetnikov/ProveIt/commit/0359ebda60aaf52758358e1450a04988136db67e). Its saved compilation evidence and outer-session telemetry are not represented as a new local build.

The new runtime and review checks are independent authored finite transcriptions. The terminal-drain draft is a small attributed derivative of the pinned upstream PositiveStutter source, retained alongside its input and patch. Other formal drafts are clearly marked uncompiled. Upstream filenames, source headers and recorded compiler results remain unchanged. All received code stays evidence-only.

## Notices

`licenses/` is copied byte-for-byte from the prior sealed release. It contains the ProveIt notice, Wade MIT No Attribution notices, BusyCoq MIT, LibTactics MIT-X11, Undecidability MPL-2.0, the K230 third-party attribution record, and the original notice provenance. That preserved provenance describes its original packet and may mention files not present in this smaller follow-up.

These notices preserve existing terms and attribution; they neither relicense the packet as a whole nor resolve the scope of custom sources without a stated license. The current package makes no new license grant or legal conclusion.
