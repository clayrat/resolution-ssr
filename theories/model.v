From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From resssr Require Import prelude decset.

Section Model.

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
move; case=>n1; case=>n2 /=; (try by constructor);
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

(* valuations *)
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

Lemma valClause_equiv c1 c2 v : eqset c1 c2 -> valClause c1 v = valClause c2 v.
Proof.
move/eqsetP=>H.
by apply/idP/idP; apply: valClause_sub=>x; rewrite H.
Qed.

Corollary valClause_cat c1 c2 v : valClause (c1 ++ c2) v = valClause c1 v || valClause c2 v.
Proof. by rewrite /valClause has_cat. Qed.

Definition valForm (f : form) (v : val) : bool :=
  all (valClause^~ v) f.

Corollary valForm_cat c1 c2 v : valForm (c1 ++ c2) v = valForm c1 v && valForm c2 v.
Proof. by rewrite /valForm all_cat. Qed.

End Model.
