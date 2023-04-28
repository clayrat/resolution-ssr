From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Inductive and6 (P1 P2 P3 P4 P5 P6 : Prop) : Prop :=
  And6 of P1 & P2 & P3 & P4 & P5 & P6.

Notation "[ /\ P1 , P2 , P3 , P4 , P5 & P6 ]" := (and6 P1 P2 P3 P4 P5 P6) : type_scope.

Section ReflectConnectives.
Variable b1 b2 b3 b4 b5 b6 : bool.

Lemma and6P : reflect [/\ b1, b2, b3, b4, b5 & b6] [&& b1, b2, b3, b4, b5 & b6].
Proof.
case: b1=>/=; last by constructor; case.
case: b2=>/=; last by constructor; case.
case: b3=>/=; last by constructor; case.
case: b4=>/=; last by constructor; case.
case: b5=>/=; last by constructor; case.
case: b6=>/=; last by constructor; case.
by constructor.
Qed.

End ReflectConnectives.

Lemma nseq_filter_pred1 {A : eqType} (z : A) s :
  filter (pred1 z) s = nseq (count_mem z s) z.
Proof.
elim: s=>//= x s IH.
by case: eqVneq=>[->|N] /=; rewrite IH.
Qed.

(* decidable subset relation on lists *)
Section Subsetb.
Context {A : eqType}.

Definition subsetb (s1 s2 : seq A) : bool :=
  all [in s2] s1.

Lemma subsetbP (s1 s2 : seq A) : reflect {subset s1 <= s2} (subsetb s1 s2).
Proof.
rewrite /subsetb; apply: (iffP idP).
- by move/allP=>A1 x; apply: A1.
by move=>H; apply/allP=>x Hx; apply: H.
Qed.

Lemma subsetb_id : reflexive subsetb.
Proof. by move=>x; rewrite /subsetb allss. Qed.

Lemma subsetb_trans : transitive subsetb.
Proof.
move=>x y z /subsetbP Hyx /subsetbP Hxz; apply/subsetbP => q Hq.
by apply/Hxz/Hyx.
Qed.

Lemma subsetb_catl s1 s2 s : subsetb (s1 ++ s2) s = subsetb s1 s && subsetb s2 s.
Proof. by rewrite /subsetb all_cat. Qed.

Lemma subsetb_catr_same s s1 : subsetb s (s ++ s1).
Proof. by apply/subsetbP=>z; rewrite mem_cat=>->. Qed.

Lemma subsetb_perml s1 s2 s : perm_eq s1 s2 -> subsetb s1 s = subsetb s2 s.
Proof. by move=>H; rewrite /subsetb; apply: perm_all. Qed.

Lemma subsetb_permr s s1 s2 : perm_eq s1 s2 -> subsetb s s1 = subsetb s s2.
Proof. by move=>H; rewrite /subsetb; apply: eq_all; apply: (perm_mem H). Qed.

End Subsetb.

(* decidable set-equality relation on lists *)
Section Eqset.
Context {A : eqType}.

Definition eqset (s1 s2 : seq A) : bool :=
  subsetb s1 s2 && subsetb s2 s1.

Lemma eqsetP (s1 s2 : seq A) : reflect (s1 =i s2) (eqset s1 s2).
Proof.
rewrite /eqset; apply: (iffP andP).
- case=>/subsetbP A1 /subsetbP A2 x.
  by apply/idP/idP=>[/A1|/A2].
by move=>H; split; apply/allP=>x Hx; [rewrite -H|rewrite H].
Qed.

Lemma eqset_id : reflexive eqset.
Proof. by move=>x; rewrite /eqset subsetb_id. Qed.

Lemma eqset_sym : symmetric eqset.
Proof. by move=>x y; rewrite /eqset andbC. Qed.

Lemma eqset_trans : transitive eqset.
Proof.
move=>x y z /eqsetP Hyx /eqsetP Hxz; apply/eqsetP => q.
by rewrite Hyx.
Qed.

Lemma eqset0 s : eqset [::] s = nilp s.
Proof. by case: s. Qed.

Notation eqsetl s1 s2 := (eqset s1 =1 eqset s2).

Lemma eqsetPl s1 s2 : reflect (eqsetl s1 s2) (eqset s1 s2).
Proof.
apply: (iffP idP).
- move=>H q; apply/idP/idP.
  - by rewrite eqset_sym in H; apply: eqset_trans.
  by apply: eqset_trans.
by move=>/(_ s2)=>->; apply: eqset_id.
Qed.

Lemma eqset_catC s1 s2 : eqsetl (s1 ++ s2) (s2 ++ s1).
Proof. by apply/eqsetPl/eqsetP=>q; rewrite !mem_cat orbC. Qed.

Lemma eqset_cons x s1 s2 : eqset s1 s2 -> eqset (x::s1) (x::s2).
Proof. by move/eqsetP=>H12; apply/eqsetP=>q; rewrite !inE H12. Qed.

Lemma eqset_cons2 x s : eqsetl (x::x::s) (x::s).
Proof. by apply/eqsetPl/eqsetP=>q; rewrite !inE orbA orbb. Qed.

Lemma eqset_catCA s1 s2 s3 : eqsetl (s1 ++ s2 ++ s3) (s2 ++ s1 ++ s3).
Proof. by apply/eqsetPl/eqsetP=>q; rewrite !mem_cat orbCA. Qed.

Lemma eqset_perm s1 s2 : perm_eq s1 s2 -> eqset s1 s2.
Proof. by move=>H; apply/eqsetP/perm_mem. Qed.

End Eqset.

Section Resolution.

(* Literals are nats labelled by pos and neg *)
Variant lit : Type := pos of nat | neg of nat.

Definition eqlit (l1 l2 : lit) :=
  match l1, l2 with
  | pos n1, pos n2 => n1 == n2
  | neg n1, neg n2 => n1 == n2
  | _, _ => false
  end.

Lemma eqlitP : Equality.axiom eqlit.
Proof.
move; case=>n1; case=>n2 /=; try by constructor.
- by apply: (iffP eqP)=>[->|[]].
by apply: (iffP eqP)=>[->|[]].
Qed.

Canonical lit_eqMixin := EqMixin eqlitP.
Canonical lit_eqType := Eval hnf in EqType lit lit_eqMixin.

Definition projLit (l : lit) : nat :=
  match l with
  | pos n => n
  | neg n => n
  end.

Definition notLit (l : lit) : lit :=
  match l with
  | pos n => neg n
  | neg n => pos n
  end.

Lemma notLitK : involutive notLit.
Proof. by case. Qed.

Lemma notLitE x : x != notLit x.
Proof. by case: x. Qed.

Definition clause := seq lit.
Definition form := seq clause.

Definition P : nat := 1.
Definition Q : nat := 2.
Definition R : nat := 3.

Definition phi : form :=
  [:: [:: pos P; pos R];
      [:: neg P];
      [:: pos Q];
      [:: pos P; neg Q; neg R]].

Definition val := seq nat.

Definition valLit (l : lit) (v : val) : bool :=
  match l with
  | pos n => n \in v
  | neg n => n \notin v
  end.

Lemma valLitNot l v : valLit (notLit l) v = ~~ valLit l v.
Proof. by case: l=>n //=; rewrite negbK. Qed.

Definition valClause (c : clause) (v : val) : bool :=
  has (valLit^~ v) c.

Lemma valClause_sub c1 c2 v :
  {subset c1 <= c2} -> valClause c1 v -> valClause c2 v.
Proof.
rewrite /valClause=>Hs.
case/hasP=>x Hx Hv.
apply/hasP; exists x=>//.
by apply: Hs.
Qed.

Definition valForm (f : form) (v : val) : bool :=
  all (valClause^~ v) f.

Definition satisfiable (f : form) : Type := { v : val | valForm f v }.

Lemma satisfiable0 : satisfiable [::].
Proof. by exists [::]. Qed.

Inductive resol : Type := leaf of clause | node of lit & clause & resol & resol.

Definition exTree : resol :=
  node (pos R) [::]
    (node (pos P) [::pos R]
      (leaf [::pos P;pos R])
      (leaf [::neg P])
    )
    (node (pos Q) [::neg R]
      (leaf [::pos Q])
      (node (pos P) [::neg Q;neg R]
        (leaf [::pos P; neg Q; neg R])
        (leaf [::neg P]))
    ).

Definition clauseR (r : resol) : clause :=
  match r with
  | leaf c => c
  | node _ c _ _ => c
  end.

Fixpoint premises (r : resol) : seq clause :=
  match r with
  | leaf c => [::c]
  | node _ _ r1 r2 => premises r1 ++ premises r2
  end.

Lemma ex1 : premises exTree =
            [::[::pos P; pos R];
               [::neg P];
               [::pos Q];
               [::pos P; neg Q; neg R];
               [::neg P]].
Proof. by []. Qed.

Fixpoint correctR (r : resol) : bool :=
  if r is node l c r1 r2 then
    [&& correctR r1, correctR r2,
        l \in clauseR r1, notLit l \in clauseR r2 &
        eqset c (filter (predC1 l) (clauseR r1) ++
                 filter (predC1 (notLit l)) (clauseR r2))]
   else true.

Lemma exTree_correct : correctR exTree.
Proof. by []. Qed.

Definition corresponds (r : resol) (f : form) : bool :=
  subsetb (premises r) f.

Definition refutes (r: resol) (f : form) : bool :=
  corresponds r f && nilp (clauseR r).

Lemma ex2 : refutes exTree phi.
Proof. by []. Qed.

Fixpoint contraClause (r : resol) (v : val) : clause :=
  match r with
  | leaf c => c
  | node l _ r1 r2 => if valLit l v then contraClause r2 v
                                    else contraClause r1 v
  end.

Definition exVal : val := [::Q;R].

Lemma ex3 : contraClause exTree exVal = [::pos P; neg Q; neg R].
Proof. by []. Qed.

Lemma cc1 (r : resol) f v :
  correctR r ->
  corresponds r f ->
  contraClause r v \in f.
Proof.
rewrite /corresponds /=.
elim: r=>/= [c|l c r1 IH1 r2 IH2].
- by move=>_; rewrite andbT.
case/and5P=>H1 H2 _ _ {c}_; rewrite subsetb_catl; case/andP=>A1 A2.
by case: ifP=>_; [apply: IH2 | apply: IH1].
Qed.

Fixpoint lontraClause (r : resol) (v : val) : clause :=
  if r is node l c r1 r2 then
    if valLit l v then notLit l :: lontraClause r2 v
                  else l :: lontraClause r1 v
  else [::].

Lemma ex4 : lontraClause exTree exVal = [::neg R; neg Q; pos P].
Proof. by []. Qed.

Lemma lv1 (r : resol) v : ~~ valClause (lontraClause r v) v.
Proof.
elim: r=>[_|l _ r1 IH1 r2 IH2] //=.
case: ifP=>HV /=; rewrite negb_or.
- by rewrite valLitNot negbK HV.
by rewrite HV.
Qed.

Lemma lc1 (r : resol) v :
  correctR r ->
  subsetb (contraClause r v) (clauseR r ++ lontraClause r v).
Proof.
elim: r=>[c|l c r1 IH1 r2 IH2] /=.
- move=>_; rewrite cats0; exact: allss.
case/and5P=>H1 H2 Hl Hnl Hp.
case: ifP=>Hv.
- move: (IH2 H2)=>/allP /= A.
  apply/allP=>/= x Hx; move: (A x Hx); rewrite !mem_cat inE.
  case/orP=>[Hx'|->]; last by rewrite !orbT.
  rewrite (eqsetP _ _ Hp) mem_cat !mem_filter /= Hx' andbT.
  by rewrite orbA orbC -orbA orNb !orbT.
move: (IH1 H1)=>/allP /= A.
apply/allP=>/= x Hx; move: (A x Hx); rewrite !mem_cat inE.
case/orP=>[Hx'|->]; last by rewrite !orbT.
rewrite (eqsetP _ _ Hp) mem_cat !mem_filter /= Hx' andbT.
by rewrite orbCA !orbA orbN.
Qed.

Lemma lv2 (r : resol) f v :
  correctR r ->
  refutes r f ->
  ~~ valClause (contraClause r v) v.
Proof.
rewrite /refutes=>H /andP [_ /nilP E].
apply: contra (lv1 r v).
move: (lc1 _ v H); rewrite {}E cat0s=>A.
apply: valClause_sub=>x Hx.
by move/allP: A; apply.
Qed.

Theorem resres r f :
  correctR r ->
  refutes r f -> satisfiable f -> False.
Proof.
move=>H R; case=>v Hv.
move: (lv2 _ _ v H R).
case/andP: R=>Hc Hn; move/negP; apply.
move: (cc1 _ _ v H Hc).
set c := contraClause r v; move=>Hp.
by move/allP: Hv=>/(_ _ Hp).
Qed.

Fixpoint percolate0 (r : resol) (a : clause) (l : lit) : resol * bool :=
  match r with
  | leaf c => if c == a then (leaf (l::c), false) else (r, true)
  | node resL c r1 r2 =>
      let '(rp1, b1) := percolate0 r1 a l in
      let '(rp2, b2) := percolate0 r2 a l in
      let cr :=
        match (b1, b2) with
        | (true , true ) => (c, true)
        | (true , false) => if resL == notLit l then (c, true) else (l::c, false)
        | (false, true ) => if resL ==        l then (c, true) else (l::c, false)
        | (false, false) => (l::c, false)
        end in
     (node resL cr.1 rp1 rp2, cr.2)
  end.

Definition percolate (r : resol) (a : clause) (l : lit) : resol := (percolate0 r a l).1.

Definition exPerc := percolate exTree [::neg P] (neg Q).

Lemma percolateClauseR (r : resol) (a : clause) (l : lit) re b :
  percolate0 r a l = (re, b) ->
  clauseR re = if b then clauseR r else l :: clauseR r.
Proof.
case: r=>[c|r c r1 r2] /=; first by case: ifP=>_ /= [<-<-].
case E1: (percolate0 r1 a l)=>[rp1 b1] /=.
case E2: (percolate0 r2 a l)=>[rp2 b2] /=.
by case: ifP=>_; case: ifP=>_ /= [<-<-] //=; case: ifP.
Qed.

Lemma percolateCorrect (r : resol) (a : clause) (l : lit) :
  correctR r -> correctR (percolate r a l).
Proof.
rewrite /percolate; elim: r=>[c|r c r1 IH1 r2 IH2] /=.
- by move=>_; case: ifP.
case/and5P=>H1 H2 Hr Hnr Hp.
case E1: (percolate0 r1 a l)=>[re1 b1] /=.
case E2: (percolate0 r2 a l)=>[re2 b2] /=.
rewrite E1 /= in IH1; rewrite E2 /= in IH2.
rewrite (percolateClauseR _ _ _ _ _ E1) (percolateClauseR _ _ _ _ _ E2).
apply/and5P; split.
- by apply: IH1.
- by apply: IH2.
- by case: {E1}b1=>//; rewrite inE Hr orbT.
- by case: {E2}b2=>//; rewrite inE Hnr orbT.
case: {E1}b1; case: {E2}b2=>//=.
- case: eqVneq=>[Er|Nr] /=.
  - by rewrite Er notLitK in Hp *; rewrite eqxx.
  case: eqVneq=>/= [El|_]; first by rewrite El notLitK eqxx in Nr.
  rewrite -(cat1s _ (filter _ _)) eqset_sym -eqset_catCA eqset_sym /=.
  by apply: eqset_cons.
- by case: eqVneq=>//= _; apply: eqset_cons.
case: eqVneq=>/= [->|Nl].
- rewrite notLitE -(cat1s _ (filter _ _)) eqset_sym -eqset_catCA eqset_sym /=.
  by apply: eqset_cons.
case: eqVneq=>/= _; first by apply: eqset_cons.
rewrite -(cat1s _ (filter _ _)) eqset_sym -cat_cons -eqset_catCA /= eqset_cons2 eqset_sym.
by apply: eqset_cons.
Qed.

(* TODO ad-hoc, refactor *)
Lemma percolatePremises r a l f f1 f2 :
  perm_eq f (f1 ++ f2) ->
  l::a \in f2 ->
  subsetb (premises r) (a::f1) ->
  subsetb (premises (percolate r a l)) f.
Proof.
move=>H1 H2; rewrite /percolate.
elim: r=>[c|r c r1 IH1 r2 IH2] /=.
- rewrite andbT inE; case: eqVneq=>/= [->_|_ Hc]; rewrite andbT (perm_mem H1) mem_cat.
  - by rewrite H2 orbT.
  by rewrite Hc.
case E1: (percolate0 r1 a l)=>[rp1 b1] /=.
case E2: (percolate0 r2 a l)=>[rp2 b2] /=.
move: E1; rewrite (surjective_pairing (percolate0 _ _ _)); case=>E1 _; rewrite {}E1 in IH1.
move: E2; rewrite (surjective_pairing (percolate0 _ _ _)); case=>E2 _; rewrite {}E2 in IH2.
rewrite !subsetb_catl => /andP [S1 S2].
by rewrite IH1 // IH2.
Qed.

Fixpoint graft (r s : resol) : resol :=
  match r with
  | leaf c => if clauseR s == c then s else r
  | node l c r1 r2 => node l c (graft r1 s) (graft r2 s)
  end.

Lemma graftClauseR (r s : resol) :
  clauseR (graft r s) = clauseR r.
Proof. by elim: r=>[c|r c r1 IH1 r2 IH2] //=; case: ifP=>// /eqP. Qed.

Lemma graftCorrect r s :
  correctR r -> correctR s -> correctR (graft r s).
Proof.
elim: r=>[c|r c r1 IH1 r2 IH2] /=.
- by move=>_ Hs; case: ifP.
case/and5P=>H1 H2 Hr Hnr Hp Hs.
apply/and5P; split.
- by apply: IH1.
- by apply: IH2.
- by rewrite (graftClauseR r1 s).
- by rewrite (graftClauseR r2 s).
apply: eqset_trans; first by exact: Hp.
by rewrite !graftClauseR; exact: eqset_id.
Qed.

Lemma graftPremiseSub r s :
  {subset premises (graft r s) <= filter (predC1 (clauseR s)) (premises r) ++ premises s}.
Proof.
move=>x; elim: r=>[c|r c r1 IH1 r2 IH2] /=.
- by case: eqVneq=>//= _; rewrite !inE=>->.
rewrite !mem_cat !mem_filter !mem_cat ?andb_orr /= in IH1 IH2 *.
by case/orP=>[/IH1|/IH2]; case/orP=>-> //; rewrite orbT.
Qed.

(* TODO bigop? *)
Fixpoint measure (f : form) : nat :=
  if f is x::xs then (size x).-1 + measure xs else 0.

Lemma measure_filt f c : measure f = measure (filter (predC1 c) f) + (count_mem c f) * (size c).-1.
Proof.
elim: f=>/= [|x f IH]; first by rewrite mul0n.
case: eqVneq=>/= [{x}->|Nx]; last first.
- by rewrite add0n IH addnA.
by rewrite mulnDl mul1n [RHS]addnCA IH.
Qed.

Definition oneLit (f : form) : bool :=
  all (fun c => size c <= 1) f.

Lemma l0 f : measure f == 0 -> oneLit f.
Proof.
elim: f=>//=c f IH.
by rewrite addn_eq0 -subn1 subn_eq0; case/andP=>-> /IH.
Qed.

(* choose the first clause of size 2+ *)
Lemma chooseClause f : 0 < measure f -> {c : clause | (c \in f) /\ (2 <= size c)}.
Proof.
elim: f=>//=c f IH; rewrite addn_gt0 -subn1 subn_gt0.
case: (ltnP 1 (size c))=>/= [Hs _|_].
- by exists c; split=>//; rewrite inE eqxx.
by case/IH=>c' [H' S']; exists c'; split=>//; rewrite inE H' orbT.
Qed.

Definition fPred (f : form) : Type :=
  satisfiable f + {r : resol | correctR r && refutes r f}.

Lemma decide1 f : oneLit f -> fPred f.
Proof.
elim: f=>[|c f IH]/=.
- by move=>_; left; exact: satisfiable0.
case/andP=>Hc /[dup] Ho /IH; case=>{IH}; case; last first.
- (* f is unsatisfiable *)
  move=>r; case/andP=>Hr Hf.
  right; exists r; rewrite Hr /=.
  move: Hf; rewrite /refutes /corresponds /=; case/andP=>A ->; rewrite andbT.
  by apply: sub_all A=>q; rewrite inE=>->; rewrite orbT.
(* f is satisfiable *)
move=>v Hv; case: c Hc=>/= [_|l].
- by right; exists (leaf [::]).
case=>//= _.
case: (boolP ([::notLit l] \in f))=>Hnl.
- right; exists (node l [::] (leaf [::l]) (leaf [::notLit l]))=>/=.
  by rewrite !inE !eqxx /= /refutes /= andbT /corresponds /= andbT !inE eqxx /= Hnl orbT.
case: (boolP ([::l] \in f))=>Hl.
- left; exists v=>/=; rewrite orbF Hv andbT.
  by move/allP: Hv=>/(_ _ Hl); case/hasP=>x; rewrite inE=>/eqP->.
left; case: l Hnl Hl=>/= n H1 H2.
- exists (if n \in v then v else n::v)=>/=; rewrite orbF.
  case: (boolP (n \in v))=>[->|Nv] //.
  rewrite inE eqxx /=.
  congr (_ = _): Hv; apply: eq_in_all=>c Hc.
  apply/idP/idP; case/hasP=>x Hx Hv; apply/hasP; exists x=>//;
    case: x Hx Hv=>/= m Hm; rewrite inE ?negb_or.
  - by move=>->; rewrite orbT.
  - move=>->; rewrite andbT.
    apply: contraNneq H1 => <-.
    move/allP: Ho=>/(_ _ Hc); case: c Hc Hm=>//= l'; case=>//= H'.
    by rewrite inE=>/eqP->.
  - case/orP=>[/eqP Em|] //; rewrite {m}Em in Hm *.
    move/allP: Ho=>/(_ _ Hc); case: c Hc Hm=>//= l'; case=>//= H' + _.
    by rewrite inE=>/eqP E'; rewrite E' H' in H2.
  by case/andP.
exists (filter (predC1 n) v)=>/=; rewrite orbF mem_filter /= eqxx /=.
congr (_ = _): Hv; apply: eq_in_all=>c Hc.
apply/idP/idP; case/hasP=>x Hx Hv; apply/hasP; exists x=>//;
  case: x Hx Hv=>/= m Hm; rewrite mem_filter /= ?negb_and ?negbK.
- move=>->; rewrite andbT.
  apply: contraNneq H1 => <-.
  move/allP: Ho=>/(_ _ Hc); case: c Hc Hm=>//= l'; case=>//= H'.
  by rewrite inE=>/eqP->.
- by move=>->; rewrite orbT.
- by case/andP.
case/orP=>[/eqP Em|] //; rewrite {m}Em in Hm *.
move/allP: Ho=>/(_ _ Hc); case: c Hc Hm=>//= l'; case=>//= H' + _.
by rewrite inE=>/eqP E'; rewrite E' H' in H2.
Qed.

Theorem decide f : fPred f.
Proof.
move: {2}(measure f) (eqxx (measure f))=>n.
elim/ltn_ind: n f; case=>[_|n IH] f; first by move/l0/decide1.
move/eqP=>Hm; rewrite -Hm in IH.
have/chooseClause: 0 < measure f by rewrite Hm.
case; case=>/= [[]|l1] //; case=>/= [|l2 c] [] // Hf _.
set c' := l1::l2::c.
have Hc' : 0 < count_mem c' f.
- by move: Hf; rewrite -has_pred1 has_count.
set D : form := filter (predC1 c') f.
have Hpf : perm_eq f (D ++ nseq (count_mem c' f) c').
- rewrite perm_sym; move/permPl: (perm_filterC (predC1 c') f)=>Hp.
  apply/perm_trans/Hp; rewrite /D perm_cat2l.
  have -> : [seq x <- f | predC (predC1 c') x] = [seq x <- f | (pred1 c') x].
  - by apply: eq_filter=>z /=; rewrite negbK.
  by rewrite nseq_filter_pred1.
set f1 := [::l1] :: D.
set f2 := (l2::c) :: D.
have M1: measure f1 < measure f.
- rewrite /f1 /= add0n /D (measure_filt f c').
  by rewrite -[ltnLHS]addn0 ltn_add2l muln_gt0 /= andbT.
move: (IH _ M1 f1); rewrite eqxx=>/(_ erefl); case.
- (* f1 is satisfiable *)
  case=>v V1; left; exists v.
  move: V1; rewrite /f1 /= orbF; case/andP=>V1 VD.
  have VC: valClause c' v by rewrite /= V1.
  by rewrite /valForm (perm_all _ Hpf) all_cat -/(valForm D v) VD /= all_nseq VC orbT.
(* f1 is refutable *)
case=>r1 /andP [Hcr1 Hfr1].
have M2: measure f2 < measure f.
- rewrite /f2 /= /D  (measure_filt f c') addnC ltn_add2l /c' /=.
  apply: (leq_ltn_trans (n:=count_mem [:: l1, l2 & c] f * (size c))).
  - by rewrite -[leqLHS]mul1n leq_mul2r Hc' orbT.
  by rewrite mulnS  -[ltnLHS]add0n ltn_add2r.
move: (IH _ M2 f2); rewrite eqxx=>/(_ erefl); case.
- (* f2 is satisfiable *)
  case=>v V2; left; exists v.
  move: V2; rewrite /f2 /=; case/andP=>V2 VD.
  have VC: valClause c' v by rewrite /= V2 orbT.
  by rewrite /valForm (perm_all _ Hpf) all_cat -/(valForm D v) VD /= all_nseq VC orbT.
(* f2 is refutable *)
case=>r2 /andP [Hcr2 Hfr2].
case E: (percolate0 r2 (l2::c) l1)=>[rp b].
move/percolateClauseR: (E).
move: E; rewrite (surjective_pairing (percolate0 _ _ _)); case=>Er Eb.
have Crp: correctR rp by rewrite -Er; apply: percolateCorrect.
case/andP: Hfr2=>Hcc /nilP ->.
have Hcrp : corresponds rp f.
- rewrite -{Crp rp}Er -/(percolate r2 (l2::c) l1) /corresponds.
  apply: (percolatePremises _ _ _ _ D (nseq (count_mem c' f) c'))=>//.
  by rewrite mem_nseq Hc' eqxx.
case: b Eb=>Eb Hcr.
- by right; exists rp; rewrite Crp /= /refutes Hcrp Hcr.
case/boolP: ([::l1] \in premises r1)=>L; last first.
- right; exists r1; rewrite Hcr1 /=.
  case/andP: Hfr1=>Hcc1 Hn.
  apply/andP; split=>//.
  rewrite /corresponds in Hcc1 *.
  apply: (subsetb_trans D).
  - apply/subsetbP=>q Hq.
    move/subsetbP: Hcc1=>/(_ _ Hq); rewrite /f1 inE; case/orP=>// /eqP Eq.
    by rewrite -Eq Hq in L.
  by rewrite (subsetb_permr _ _ _ Hpf); exact: subsetb_catr_same.
right; exists (graft r1 rp); apply/andP; split; first by apply: graftCorrect.
apply/andP; split; last by rewrite graftClauseR; case/andP: Hfr1.
case/andP: Hfr1=>Hcc1 Hn1; rewrite /corresponds in Hcc1 Hcrp *.
apply: subsetb_trans; first by apply/subsetbP/graftPremiseSub.
rewrite subsetb_catl Hcrp andbT.
apply/subsetbP=>z; rewrite mem_filter /=; case/andP=>Hz1 Hz2; rewrite Hcr in Hz1.
move/subsetbP: Hcc1=>/(_ _ Hz2).
rewrite /f1 inE (negbTE Hz1) /= => Hz.
by rewrite (perm_mem Hpf) mem_cat Hz.
Qed.

End Resolution.
