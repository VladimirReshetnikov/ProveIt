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
cnf(k10,axiom,(eps(upd(upd(B,c0,bad(B,T)),n(c0,c0),out(B,T,Q)),T) | e(pick(X),X) | ~eps(upd(upd(B,c0,X),n(c0,c0),Y),T) | e(Y,h(B,T)))).
cnf(k11,axiom,(e(mem(B,T,Q),out(B,T,Q)) | e(pick(X),X) | ~eps(upd(upd(B,c0,X),n(c0,c0),Y),T) | e(Y,h(B,T)))).
cnf(k12,axiom,(~e(mem(B,T,Q),Q) | e(pick(X),X) | ~eps(upd(upd(B,c0,X),n(c0,c0),Y),T) | e(Y,h(B,T)))).
cnf(k13,axiom,(eps(upd(upd(B,c0,bad(B,T)),n(c0,c0),out(B,T,Q)),T) | ~e(X,h(B,T)) | ~eps(upd(upd(B,c0,X),n(c0,c0),Y),T) | e(Y,h(B,T)))).
cnf(k14,axiom,(e(mem(B,T,Q),out(B,T,Q)) | ~e(X,h(B,T)) | ~eps(upd(upd(B,c0,X),n(c0,c0),Y),T) | e(Y,h(B,T)))).
cnf(k15,axiom,(~e(mem(B,T,Q),Q) | ~e(X,h(B,T)) | ~eps(upd(upd(B,c0,X),n(c0,c0),Y),T) | e(Y,h(B,T)))).
cnf(k16,axiom,(eps(upd(upd(B,c0,bad(B,T)),n(c0,c0),out(B,T,Q)),T) | ~e(Y,h(B,T)) | eps(upd(upd(B,c0,sup(B,T,Y)),n(c0,c0),Y),T))).
cnf(k17,axiom,(e(mem(B,T,Q),out(B,T,Q)) | ~e(Y,h(B,T)) | eps(upd(upd(B,c0,sup(B,T,Y)),n(c0,c0),Y),T))).
cnf(k18,axiom,(~e(mem(B,T,Q),Q) | ~e(Y,h(B,T)) | eps(upd(upd(B,c0,sup(B,T,Y)),n(c0,c0),Y),T))).
