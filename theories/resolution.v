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

(* equal as finite sets *)
Section Eqset.
Context {A : eqType}.

Definition eqset (l1 l2 : seq A) : bool :=
  all [in l2] l1 && all [in l1] l2.

Lemma eqsetP (l1 l2 : seq A) : reflect (l1 =i l2) (eqset l1 l2).
Proof.
rewrite /eqset; apply: (iffP andP).
- case=>/allP A1 /allP A2 x.
  by apply/idP/idP=>[/A1|/A2].
by move=>H; split; apply/allP=>x Hx; [rewrite -H|rewrite H].
Qed.

Lemma eqset_id : reflexive eqset.
Proof. by move=>x; rewrite /eqset allss. Qed.

Lemma eqset_sym : symmetric eqset.
Proof. by move=>x y; rewrite /eqset andbC. Qed.

Lemma eqset_trans : transitive eqset.
Proof.
move=>x y z /eqsetP Hyx /eqsetP Hxz; apply/eqsetP => q.
by rewrite Hyx.
Qed.

Notation eqsetl l1 l2 := (eqset l1 =1 eqset l2).

Lemma eqsetPl l1 l2 : reflect (eqsetl l1 l2) (eqset l1 l2).
Proof.
apply: (iffP idP).
- move=>H q; apply/idP/idP.
  - by rewrite eqset_sym in H; apply: eqset_trans.
  by apply: eqset_trans.
by move=>/(_ l2)=>->; apply: eqset_id.
Qed.

Lemma eqset_catC s1 s2 : eqsetl (s1 ++ s2) (s2 ++ s1).
Proof. by apply/eqsetPl/eqsetP=>q; rewrite !mem_cat orbC. Qed.

Lemma eqset_cons x s1 s2 : eqset s1 s2 -> eqset (x::s1) (x::s2).
Proof. by move/eqsetP=>H12; apply/eqsetP=>q; rewrite !inE H12. Qed.

Lemma eqset_cons2 x s : eqsetl (x::x::s) (x::s).
Proof. by apply/eqsetPl/eqsetP=>q; rewrite !inE orbA orbb. Qed.

Lemma eqset_catCA l1 l2 l3 : eqsetl (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
Proof. by apply/eqsetPl/eqsetP=>q; rewrite !mem_cat orbCA. Qed.

End Eqset.

Section Resolution.

(* lit is a disjoint union nat + nat.
  Its components are natural numbers labelled by pos and neg *)
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

Definition res : Type := { r : resol | correctR r }.

Lemma exTree_correct : correctR exTree.
Proof. by []. Qed.

Definition exRes : res := exist _ exTree exTree_correct.

(* subL clause eqC f1 f2 checks whether f1 is a subset of f2 *)
(* projl_sig, given a resolution, returns the underlying tree.
So proji_sig exRes = exTree. *)
Definition corresponds (r : resol) (f : form) : bool :=
  all
    (* we treat clauses as multisets which might be an overkill *)
    (fun x => has (perm_eq x) f)
    (premises r).

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
  has (perm_eq (contraClause r v)) f.
Proof.
rewrite /corresponds /=.
elim: r=>/= [c|l c r1 IH1 r2 IH2].
- by move=>_; rewrite andbT.
case/and5P=>H1 H2 _ _ {c}_; rewrite all_cat; case/andP=>A1 A2.
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
  all [in clauseR r ++ lontraClause r v] (contraClause r v).
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
case/hasP: (cc1 _ _ v H Hc)=>x Hx.
set c := contraClause r v; move=>Hp.
move/allP: Hv=>/(_ x Hx).
by apply: valClause_sub=>z; move/perm_mem: Hp=>/(_ z)->.
Qed.

Fixpoint percolate0 (r : resol) (a : clause) (l : lit) : resol * bool :=
  match r with
  | leaf c => if perm_eq c a then (leaf (l::c), false) else (r, true)
  | node resL c r1 r2 =>
      let p1 := percolate0 r1 a l in
      let p2 := percolate0 r2 a l in
      let cr :=
        match (p1.2, p2.2) with
        | (true , true ) => (c, true)
        | (true , false) => if resL == notLit l then (c, true) else ((l::c), false)
        | (false, true ) => if resL == l then (c, true) else ((l::c), false)
        | (false, false) => ((l::c), false)
        end in
     (node resL cr.1 p1.1 p2.1, cr.2)
  end.

Definition percolate (r : resol) (a : clause) (l : lit) : resol := (percolate0 r a l).1.

Definition exPerc := percolate exTree [::neg P] (neg Q).

Lemma percolateClauseR (r : resol) (a : clause) (l : lit) re b :
  percolate0 r a l = (re, b) ->
  clauseR re = if b then clauseR r else l :: clauseR r.
Proof.
case: r=>[c|r c r1 r2] /=; first by case: ifP=>_ /= [<-<-].
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

Fixpoint graft (r s : resol) : resol :=
  match r with
  | leaf c => if perm_eq (clauseR s) c then s else r
  | node l c r1 r2 => node l c (graft r1 s) (graft r2 s)
  end.
(*
Lemma graftCorrect r s :
  correctR r -> correctR s -> correctR (graft r s).
Proof.
elim: r=>[c|r c r1 IH1 r2 IH2] /=.
- by move=>_ Hs; case: ifP.
case/and5P=>H1 H2 Hr Hnr Hp Hs.
apply/and5P; split.
- by apply: IH1.
- by apply: IH2.
*)

End Resolution.
