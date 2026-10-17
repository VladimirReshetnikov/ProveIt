% Finite class/closure kernel. Genuine equality; no finite-domain assumption.
% A research proposal, not a TM state-count certificate.
cnf(k01,axiom,(v(upd(S,J,Z),J) = Z)).
cnf(k02,axiom,(K = J | v(upd(S,J,Z),K) = v(S,K))).
cnf(k03,axiom,(~eps(S,n(A,B)) | ~eps(S,A) | ~eps(S,B))).
cnf(k04,axiom,(eps(S,n(A,B)) | eps(S,A))).
cnf(k05,axiom,(eps(S,n(A,B)) | eps(S,B))).
cnf(k06,axiom,(~eps(S,a(J,K)) | e(v(S,J),v(S,K)))).
cnf(k07,axiom,(eps(S,a(J,K)) | ~e(v(S,J),v(S,K)))).
cnf(k08,axiom,(~eps(S,q(J,A)) | eps(upd(S,J,w(J,A,S)),A))).
cnf(k09,axiom,(~eps(upd(S,J,Z),A) | eps(S,q(J,A)))).
cnf(k10,axiom,(eps(c0,v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),c0)),n(c0,c0))) | eps(upd(upd(B,c0,v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),c0)),c0)),n(c0,c0),v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),upd(upd(c0,c0,Q),n(c0,c0),n(v(c0,n(c0,c0)),v(c0,n(c0,c0)))))),c0)),v(B,c0)))).
cnf(k11,axiom,(eps(c0,v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),c0)),n(c0,c0))) | e(v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),upd(upd(c0,c0,Q),n(c0,c0),n(v(c0,n(c0,c0)),v(c0,n(c0,c0)))))),n(c0,c0)),v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),upd(upd(c0,c0,Q),n(c0,c0),n(v(c0,n(c0,c0)),v(c0,n(c0,c0)))))),c0)))).
cnf(k12,axiom,(eps(c0,v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),c0)),n(c0,c0))) | ~e(v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),upd(upd(c0,c0,Q),n(c0,c0),n(v(c0,n(c0,c0)),v(c0,n(c0,c0)))))),n(c0,c0)),Q))).
cnf(k13,axiom,(~eps(c0,v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),c0)),n(c0,c0))) | e(w(c0,a(c0,n(c0,c0)),upd(c0,n(c0,c0),X)),X) | ~eps(upd(upd(B,c0,X),n(c0,c0),Y),v(B,c0)) | e(Y,v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),c0)),c0)))).
cnf(k14,axiom,(~eps(c0,v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),c0)),n(c0,c0))) | ~e(X,v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),c0)),c0)) | ~eps(upd(upd(B,c0,X),n(c0,c0),Y),v(B,c0)) | e(Y,v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),c0)),c0)))).
cnf(k15,axiom,(~eps(c0,v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),c0)),n(c0,c0))) | ~e(Y,v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),c0)),c0)) | eps(upd(upd(B,c0,v(w(c0,n(n(c0,n(c0,c0)),n(c0,n(c0,c0))),upd(upd(c0,c0,B),n(c0,c0),upd(upd(c0,c0,Y),n(c0,c0),n(v(c0,n(c0,c0)),v(c0,n(c0,c0)))))),c0)),n(c0,c0),Y),v(B,c0)))).
