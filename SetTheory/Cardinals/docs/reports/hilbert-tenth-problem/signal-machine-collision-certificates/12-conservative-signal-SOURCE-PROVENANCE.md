# Primary sources and provenance

The signal-stack construction and reversible control compiler are based on Jérôme Durand-Lose, *Abstract geometrical computation 6: a reversible, conservative and rational-based model for Black hole computation* (2012), Sections 3–4. The later shrinking/acceleration construction is not used.

https://www.univ-orleans.fr/lifo/Members/Jerome.Durand-Lose/Recherche/Publications/2012_IJUC_UC_HC.pdf

The literal source program is Kenichi Morita, *Reversible computing and cellular automata—a survey*, Theoretical Computer Science 395 (2008), 101–131, author draft Theorem 3.3 and Table 5. Its ordinary alphabet is b,Y,N,*,$,1, including the blank. All 62 transition quintuples were transcribed and checked; every published Figure 28 checkpoint agrees with the 184-step replay.

https://hiroshima.repo.nii.ac.jp/record/2008964/files/TCS_395_101.pdf

Important source discrepancy: a paragraph near Table 5 reverses YN and NY relative to Example 3.3 and Figure 28. The general reversal encoding, Figure 28 and all 184 table-driven steps agree on productions (halt,YN,YYN), input NYY, and initial tape NYY*NY*b$NYY. The source's two terminal pairs (q1,b)=halt and (q2,$)=null are distinguished. q1 and q2 also have ordinary transitions. The other 26 empty cells are undefined.

The source's explicitly halting cyclic-tag convention has finite program/data and blank tails on both sides; it does not require a nonblank infinite periodic background. A q0 visit alone is not a cyclic-tag macro boundary, so the differential tests compare the program region, phase marker and active word as well.

The separate binary existence result imports Kenichi Morita, Akihiko Shirasaki and Yoshifumi Gono, *A 1-tape 2-symbol reversible Turing machine*, IEICE Transactions E72(3) (1989), 223–228. The original 1989 publisher abstract and the 2008 survey support the imported conversion result; the 1989 full text was not obtained for this release.

https://globals.ieice.org/en_transactions/transactions/10.1587/e72-e_3_223/_p

Event linearizability is prior work: Durand-Lose, *Abstract geometrical computation and the linear Blum, Shub and Smale model* (2007), Section 4.

https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2007_CiE.pdf

Earlier reversible conservative universality: Durand-Lose, *Reversible conservative rational abstract geometrical computation is Turing-universal*, LNCS 3988 (2006), 163–172.

https://www.univ-orleans.fr/lifo/membres/Jerome.Durand-Lose/Recherche/Publications/2006_CiE.pdf

`data/SOURCE_MANIFEST.json` records exact downloaded-source digests and access date. Source PDFs themselves are not bundled. All implementation code in this release was written for this research, rather than copied from a third-party implementation. The transition table is attributed mathematical data. No new license is asserted for any cited third-party work.
