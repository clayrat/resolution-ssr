From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.

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

Corollary eqset_false c1 c2 : ~~ eqset c1 c2 -> c1 <> c2.
Proof. apply: contraNnot=>->; exact: eqset_id. Qed.

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
