From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From resssr Require Import prelude decset model.

Section SaturneResolution.

Definition sat (f : form) : Prop := exists v : val, valForm f v.

Definition unsat (f : form) := ~ sat f.

Definition mem_form (f : form) (c : clause) : bool := has (eqset c) f.

Variant resolvent : form -> clause -> Prop :=
  | resolvent_mem (f : form) (c : clause) : mem_form f c -> resolvent f c
  | resolvent_cut (f : form) (c1 c2 : clause) (l : lit) :
    mem_form f (l::c1) ->
    mem_form f (notLit l::c2) -> resolvent f (c1 ++ c2).

Lemma clause_set_clause_true m f c :
  mem_form f c ->
  valForm f m ->
  valClause c m.
Proof.
elim: f=>//=c' f IH /[swap].
case/andP=>Hc /IH {}IH; case/orP.
- by move/valClause_equiv=>->.
by apply: IH.
Qed.

Theorem resolvent_sound m f c :
  resolvent f c ->
  valForm f m ->
  valClause c m.
Proof.
case=>/= [{}f {}c Hc|{c}f c1 c2 l H1 H2 Hf].
- by apply: clause_set_clause_true.
rewrite valClause_cat.
move: (clause_set_clause_true _ _ _ H1 Hf)=>{H1}/=.
case/orP=>[Hl|->] //.
move: (clause_set_clause_true _ _ _ H2 Hf)=>{H2 Hf}/=.
case/orP=>[|->]; last by rewrite orbT.
by rewrite valLitNot Hl.
Qed.

Corollary resolvent_bot_unsat f : resolvent f [::] -> unsat f.
Proof. by move=>H [v Hv]; move: (resolvent_sound _  _ _ H Hv). Qed.

Inductive resolvent_seq : form -> clause -> Prop :=
  | resolvent_seq_base f c :
    resolvent f c -> resolvent_seq f c
  | resolvent_seq_step f c c' :
    resolvent f c ->
    resolvent_seq (c::f) c' ->
    resolvent_seq f c'.

Lemma resolvent_seq_sound f c m :
  resolvent_seq f c ->
  valForm f m ->
  valClause c m.
Proof.
elim=>{}f {}c; first by exact: resolvent_sound.
move=>c' Hc _ /= IH Hf.
apply: IH; rewrite Hf andbT.
by apply: (resolvent_sound _ f).
Qed.

Variant proof_step : Type :=
  | proof_mem of clause
  | proof_cut of nat & clause & clause.

Definition conclusion (ut : proof_step) : clause :=
  match ut with
  | proof_mem c => c
  | proof_cut _ c1 c2 => c1 ++ c2
  end.

Definition is_proof_step (context : form) (ut : proof_step) : bool :=
  match ut with
  | proof_mem c => mem_form context c
  | proof_cut l c1 c2 =>
      mem_form context (neg l::c1) &&
      mem_form context (pos l::c2)
  end.

Lemma is_proof_step_sound' ctx ut :
  is_proof_step ctx ut ->
  resolvent ctx (conclusion ut).
Proof.
case: ut=>[c|n c1 c2] /=; first by constructor.
by case/andP=>H1 H2; apply: (resolvent_cut _ _ _ (neg n)).
Qed.

Corollary is_proof_step_sound ctx ut m :
  is_proof_step ctx ut ->
  valForm ctx m ->
  valClause (conclusion ut) m.
Proof. by move=>H; apply/resolvent_sound/is_proof_step_sound'. Qed.

Fixpoint is_proof (context : form) (uts : seq proof_step) (c : clause) : bool :=
  if uts is ut::uts' then
    is_proof_step context ut &&
    is_proof ((conclusion ut)::context) uts' c
  else mem_form context c.

Lemma is_proof_sound' uts ctx c :
  is_proof ctx uts c ->
  resolvent_seq ctx c.
Proof.
elim: uts ctx=>/= [ctx H | ut uts IH ctx /andP [H1 H2]]; first by do 2!constructor.
apply: (resolvent_seq_step _ (conclusion ut)).
- by apply: is_proof_step_sound'.
by apply: IH.
Qed.

Corollary is_proof_sound uts ctx c m :
  is_proof ctx uts c ->
  valForm ctx m ->
  valClause c m.
Proof. by move=>H; apply/resolvent_seq_sound/is_proof_sound'/H. Qed.

Theorem resolvent_seq_bot_unsat f : resolvent_seq f [::] -> unsat f.
Proof.
move=>Hres [m Hm].
by move: (resolvent_seq_sound _ _ m Hres Hm).
Qed.

End SaturneResolution.