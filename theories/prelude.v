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
elim: s=>//= h t IH.
by case: (eqVneq h z)=> [->|_] /=; rewrite IH.
Qed.
