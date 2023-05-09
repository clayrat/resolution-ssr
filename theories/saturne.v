From Equations Require Import Equations.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From resssr Require Import prelude decset model.

Section Saturne.

Definition assign := seq lit.

Definition eval_clause (c : clause) (a : assign) : bool :=
  has [in a] c.

Lemma eval_clause_nil c : ~~ eval_clause c [::].
Proof. by elim: c. Qed.

Lemma eval_clause_in l c a : l \in c -> l \in a -> eval_clause c a.
Proof.
elim: c=>//= m c IH.
by rewrite inE; case/orP=>[/eqP->->|H1 H2] //; rewrite IH // orbT.
Qed.

Lemma eval_clause_weaken l c a : eval_clause c a -> eval_clause c (l :: a).
Proof.
elim: c=>//= m c IH; rewrite inE.
by case/orP=>[->|/IH->]; rewrite orbT.
Qed.

Definition eval_form (f : form) (v : assign) : bool :=
  all (eval_clause^~ v) f.

Notation "[| p | e |]" := (eval_form p e).

Definition sat (p: form) : Prop :=
  exists (a : assign), [| p | a |].

(** Problem unsatisfiability *)
Definition unsat (p: form) : Prop := ~ sat p.

(** The empty problem is satisfiable *)
Lemma smallest_sat_problem : sat [::].
Proof. by exists [::]. Qed.

(** The smallest problem containing the empty clause is unsatisfiable *)
Lemma smallest_unsat_problem: unsat [::[::]].
Proof. by case. Qed.

Lemma sat_aff c p : sat (c::p) -> sat p.
Proof. by case=>/= x /andP [_ H]; exists x. Qed.

Lemma sol_sat p a : [| p | a |] -> sat p.
Proof. by move=>H; exists a. Qed.

Lemma sat_add_sol c p a : [| c::p | a |] -> [| p | a |].
Proof. by move=>/= /andP []. Qed.

(** Remove a literal from a clause *)
Fixpoint remove_lit l (c : clause) :=
  if c is x::rest then
    if x == l then rest
              else x::(remove_lit l rest)
  else [::].

(** Simplify a problem by propagating a literal *)
Fixpoint propagate (l : lit) (p : form) : form :=
  if p is c::rest then
    if l \in c
    then propagate l rest
    else (remove_lit (notLit l) c)::(propagate l rest)
  else [::].

(** Naive size of a problem (number of literals) *)
Fixpoint problem_size (p: form) :=
  if p is c::rest then size c + problem_size rest else 0.

(** Removing a literal from a clause reduces its size *)
Lemma remove_lit_variant (l : lit) (c : clause) : size (remove_lit l c) <= size c.
Proof. by elim: c=>//= l' c IH; case: eqVneq. Qed.

Lemma propagate_variant (l : lit) (p : form) : problem_size (propagate l p) <= problem_size p.
Proof.
elim: p=>//=c p' IH; case: ifP=>/= _.
- by apply: (leq_trans IH); exact: leq_addl.
by apply: leq_add=>//; exact: remove_lit_variant.
Qed.

Lemma eval_clause_remove_neg l c a : l \notin c ->
  eval_clause (remove_lit (notLit l) c) a ->
  eval_clause c (l :: a).
Proof.
elim: c=>//= l' c IH; rewrite !inE negb_or; case/andP=>/negbTE Hl /IH {}IH.
rewrite (eq_sym _ l) {}Hl /=.
case: eqVneq=>[->|_] /= H.
- by apply/orP; right; apply: eval_clause_weaken.
by case/orP: H=>[->|H] //; apply/orP; right; apply: IH.
Qed.

(** Solutions to a SAT problem *)
Definition solutions : Type := seq assign.

(** Resolution algorithm *)
Equations? resolve (p: form) : solutions by wf (problem_size p) lt :=
resolve  [::]         => [::[::]];
resolve ([::]   ::_)  => [::];
resolve ((l::cc)::pp) => let p1 := propagate l pp in
                         let p2 := propagate (notLit l) (cc::pp) in
                         let s1 := map (cons l) (resolve p1) in
                         let s2 := map (cons (notLit l)) (resolve p2) in
                         s1 ++ s2.
Proof.
(* Termination Proof *)
all: apply/ssrnat.ltP; rewrite addSn ltnS /p1 /p2.
- by apply: leq_trans; [exact: propagate_variant | exact: leq_addl].
case: ifP=>/= _.
- by apply: leq_trans; [exact: propagate_variant | exact: leq_addl].
apply: leq_add; last by exact: propagate_variant.
by rewrite notLitK; exact: remove_lit_variant.
Defined.

Lemma propagate_correct a l p :
  [| propagate l p | a |] -> [| p | l :: a |].
Proof.
elim: p=>//= c p IH; case: (boolP (_ \in _))=>/= Hl.
- move=>H; apply/andP; split; last by apply: IH.
  by apply: (eval_clause_in l)=>//; rewrite inE eqxx.
by case/andP=>H1 H2; apply/andP; split; [apply: eval_clause_remove_neg | apply: IH].
Qed.

Lemma resolve_correct (a : assign) (p : form) : a \in resolve p -> eval_form p a.
Proof.
funelim (resolve p)=>//=; rewrite mem_cat; case/orP=>/mapP [x Hx {a}->]; rewrite inE.
- by rewrite eqxx /=; apply/propagate_correct/H.
move: (notLitE l)=>/negbTE -> /=.
move: Hx; case: (boolP (notLit l \in _))=>/= Hnl.
- rewrite /= Hnl in H0; move/H0=>{}H0.
  apply/andP; split; last by apply: propagate_correct.
  by apply/orP; right; apply: (eval_clause_in (notLit l))=>//; rewrite inE eqxx.
rewrite /= (negbTE Hnl) in H0; rewrite notLitK in H0 *; move/H0=>/=; case/andP=>{}H0 H1.
apply/andP; split; last by apply: propagate_correct.
by apply/orP; right; apply: eval_clause_remove_neg=>//; rewrite notLitK.
Qed.

(* doesn't seem to hold *)
(* Lemma resolve_complete (a:assign) (p:form) : eval_form p a -> a \in resolve p. *)

End Saturne.
