From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From resssr Require Import prelude decset model.

Section Cnf.

(** Logic language *)
Inductive lprop : Type :=
  | And of lprop & lprop
  | Or  of lprop & lprop
  | Neg of lprop
  | Atom of nat.

Definition Impl (f1 f2 : lprop) : lprop := Or (Neg f1) f2.

Fixpoint eval_lprop (m : val) (f : lprop) : bool :=
  match f with
  | And f1 f2 => eval_lprop m f1 && eval_lprop m f2
  | Or  f1 f2 => eval_lprop m f1 || eval_lprop m f2
  | Neg f     => ~~ eval_lprop m f
  | Atom a    => a \in m
  end.

Inductive precnf : Type :=
  | AndP of precnf & precnf
  | OrP  of precnf & precnf
  | LitP of lit.

(** Conversion algorithm from LProp to PreCnf *)
Fixpoint remove_neg' (sign : bool) (f : lprop) : precnf :=
  match f with
  | And a b =>
    if sign then AndP (remove_neg' sign a) (remove_neg' sign b)
    else OrP (remove_neg' false a) (remove_neg' false b)
  | Or a b =>
    if sign then OrP (remove_neg' sign a) (remove_neg' sign b)
    else AndP (remove_neg' false a) (remove_neg' false b)
  | Neg a =>
    if sign then remove_neg' false a
    else remove_neg' true a
  | Atom n =>
    if sign then LitP (pos n)
    else LitP (neg n)
  end.

Definition remove_neg := remove_neg' true.

Fixpoint eval_precnf (m : val) (f : precnf) : bool :=
  match f with
  | AndP f1 f2 => eval_precnf m f1 && eval_precnf m f2
  | OrP f1 f2 => eval_precnf m f1 || eval_precnf m f2
  | LitP l => valLit l m
  end.

  (* [remove_neg' false] inverse the denotations *)
Lemma remove_neg_false_negb f m :
  eval_precnf m (remove_neg' false f) = ~~ eval_precnf m (remove_neg' true f).
Proof.
elim: f=>[l IHl r IHr|l IHl r IHr|l IH|n] //=.
- by rewrite negb_and IHl IHr.
- by rewrite negb_or IHl IHr.
by rewrite IH negbK.
Qed.

Theorem remove_neg_correct f m : eval_lprop m f = eval_precnf m (remove_neg f).
Proof.
elim: f=>[l IHl r IHr|l IHl r IHr|l IH|n] //=.
- by rewrite IHl IHr.
- by rewrite IHl IHr.
by rewrite IH remove_neg_false_negb.
Qed.

(** Distribute a clause on a set of clauses *)
Definition merge_clause (c : clause) (f : form) :=
  map (cat c) f.

(** Double distribute a set of clauses on another one *)
Fixpoint merge (f f' : form) : form :=
  if f is c::f0
    then merge_clause c f' ++ merge f0 f'
    else [::].

(** PreCnf to Formula conversion *)
Fixpoint cnf' (f : precnf) : form :=
  match f with
  | AndP a b => cnf' a ++ cnf' b
  | OrP a b => merge (cnf' a) (cnf' b)
  | LitP a => [::[::a]]
  end.

(** CNF conversion *)
Definition cnf (f : lprop) : form :=
  cnf' (remove_neg f).

(* [merge_clause] preserve the semantic *)
Theorem merge_clause_correct c f m :
  valForm (merge_clause c f) m = valClause c m || valForm f m.
Proof.
elim: f=>[|c' f IH]/=; first by rewrite orbT.
by rewrite valClause_cat IH orb_andr.
Qed.

(* [merge] preserve the semantic *)
Theorem merge_correct f f' m :
  valForm f m || valForm f' m = valForm (merge f f') m.
Proof.
elim: f=>//= c f IH.
by rewrite valForm_cat -IH merge_clause_correct orb_andl.
Qed.

(* [cnf'] preserve the semantic *)
Theorem cnf'_correct f m : eval_precnf m f = valForm (cnf' f) m.
Proof.
elim: f=>/=[l IHl r IHr|l IHl r IHr|l].
- by rewrite IHl IHr valForm_cat.
- by rewrite IHl IHr merge_correct.
by rewrite andbT orbF.
Qed.

(* [cnf] preserve the semantic *)
Theorem cnf_correct f m : eval_lprop m f = valForm (cnf f) m.
Proof. by rewrite /cnf remove_neg_correct cnf'_correct. Qed.

End Cnf.