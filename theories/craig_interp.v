From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import finmap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope fset_scope.

Section FSetInduction.

Lemma fset1U_ind {T : choiceType} {P : {fset T} -> Prop} :
     P fset0
  -> (forall x f, x \notin f -> P f -> P (x |` f))
  -> forall f, P f.
Proof.
move=>H0 Hi f.
apply: finSet_rect f=>f Hf.
case: (fset_0Vmem f)=>[->|[x Hx]]; first by apply: H0.
move/fsetD1K: (Hx)=>/esym ->.
apply: Hi; first by rewrite in_fsetD1 negb_and negbK eqxx.
by apply/Hf/fproperD1.
Qed.

End FSetInduction.

Section Formulas.

Inductive formula A :=
| Atom of A
| Bot
| Neg of formula A
| And of formula A & formula A
| Or of formula A & formula A
| Imp of formula A & formula A.

Definition Top {A} : formula A := Imp (@Bot A) (@Bot A).

Fixpoint atoms {A : choiceType} (f : formula A) : {fset A} :=
  match f with
    | Atom a  => [fset a]
    | Bot     => fset0
    | Neg t   => atoms t
    | And s t => (atoms s) `|` (atoms t)
    | Or  s t => (atoms s) `|` (atoms t)
    | Imp s t => (atoms s) `|` (atoms t)
  end.

End Formulas.

Arguments Bot {A}.

Section Semantics.

Definition valuation A := A -> bool.

Fixpoint sem {A} (v : valuation A) (f : formula A) : bool :=
  match f with
  | Atom k  => v k
  | Bot     => false
  | Neg f   => ~~ sem v f
  | And f g => sem v f && sem v g
  | Or f g  => sem v f || sem v g
  | Imp f g => sem v f ==> sem v g
  end.

End Semantics.

Infix "⊨" := sem (at level 51, left associativity).
Notation "∙⊨ A" := (forall v, v ⊨ A) (at level 60).

Section SemanticsLemmas.

Lemma irrelevant_atom {A : choiceType} (x : A) f v b :
  x \notin atoms f -> [eta v with x |-> b] ⊨ f = v ⊨ f.
Proof.
elim: f=>//=.
- by move=>a; rewrite inE eq_sym=>/negbTE->.
- by move=>f /[apply] ->.
- by move=>l IHl r IHr; rewrite inE negb_or; case/andP=>/IHl -> /IHr ->.
- by move=>l IHl r IHr; rewrite inE negb_or; case/andP=>/IHl -> /IHr ->.
by move=>l IHl r IHr; rewrite inE negb_or; case/andP=>/IHl -> /IHr ->.
Qed.

Lemma relevant_atoms_same_semantics {A : choiceType} (f : formula A) v1 v2 :
  {in atoms f, v1 =1 v2} -> v1 ⊨ f = v2 ⊨ f.
Proof.
elim: f=>//=.
- by move=>a; apply; rewrite inE.
- by move=>f IH H; rewrite (IH H).
- move=>l IHl r IHr H; rewrite IHl ?IHr //.
  - by move=>x Hx; apply: H; rewrite in_fsetU Hx orbT.
  by move=>x Hx; apply: H; rewrite in_fsetU Hx.
- move=>l IHl r IHr H; rewrite IHl ?IHr //.
  - by move=>x Hx; apply: H; rewrite in_fsetU Hx orbT.
  by move=>x Hx; apply: H; rewrite in_fsetU Hx.
move=>l IHl r IHr H; rewrite IHl ?IHr //.
- by move=>x Hx; apply: H; rewrite in_fsetU Hx orbT.
by move=>x Hx; apply: H; rewrite in_fsetU Hx.
Qed.

End SemanticsLemmas.

Section Substitution.

(* replace all atoms `a` in `y` by `x` *)
Fixpoint subst {A : eqType} (a : A) (x y : formula A) : formula A :=
  match y with
  | Atom b  => if a == b then x else Atom b
  | Bot     => Bot
  | Neg h   => Neg (subst a x h)
  | And g h => And (subst a x g) (subst a x h)
  | Or g h  => Or (subst a x g) (subst a x h)
  | Imp g h => Imp (subst a x g) (subst a x h)
  end.

End Substitution.

Notation "f [ g | x ]" := (subst x g f) (at level 69, right associativity).

Section SubstitutionLemmas.

Lemma no_subst {A : choiceType} (k : A) f g :
  k \notin atoms f -> f [g | k] = f.
Proof.
elim: f=>//=.
- by move=>a; rewrite inE => /negbTE ->.
- by move=> f /[apply] ->.
- move=>l IHl r IHr; rewrite in_fsetU negb_or.
  by case/andP=>/IHl->/IHr->.
- move=>l IHl r IHr; rewrite in_fsetU negb_or.
  by case/andP=>/IHl->/IHr->.
move=>l IHl r IHr; rewrite in_fsetU negb_or.
by case/andP=>/IHl->/IHr->.
Qed.

Lemma subst_atoms {A : choiceType} (k : A) f g :
  k \in atoms f -> atoms (f [g | k]) = (atoms f `\ k) `|` atoms g.
Proof.
elim: f=>//=.
- move=>a; rewrite inE => /eqP {k}->.
  by rewrite eqxx fsetDv fset0U.
- move=>l IHl r IHr; rewrite in_fsetU fsetDUl.
  case/boolP: (k \in atoms l)=>Hl; case/boolP: (k \in atoms r)=>Hr //= _.
  - by rewrite (IHl Hl) (IHr Hr) -fsetUUl.
  - by rewrite (IHl Hl) (no_subst _ Hr) (mem_fsetD1 Hr) fsetUAC.
  by rewrite (no_subst _ Hl) (IHr Hr) (mem_fsetD1 Hl) fsetUA.
- move=>l IHl r IHr; rewrite in_fsetU fsetDUl.
  case/boolP: (k \in atoms l)=>Hl; case/boolP: (k \in atoms r)=>Hr //= _.
  - by rewrite (IHl Hl) (IHr Hr) -fsetUUl.
  - by rewrite (IHl Hl) (no_subst _ Hr) (mem_fsetD1 Hr) fsetUAC.
  by rewrite (no_subst _ Hl) (IHr Hr) (mem_fsetD1 Hl) fsetUA.
move=>l IHl r IHr; rewrite in_fsetU fsetDUl.
case/boolP: (k \in atoms l)=>Hl; case/boolP: (k \in atoms r)=>Hr //= _.
- by rewrite (IHl Hl) (IHr Hr) -fsetUUl.
- by rewrite (IHl Hl) (no_subst _ Hr) (mem_fsetD1 Hr) fsetUAC.
by rewrite (no_subst _ Hl) (IHr Hr) (mem_fsetD1 Hl) fsetUA.
Qed.

Lemma substitution_lemma {A : eqType} (a : valuation A) f g n :
  (a ⊨ (f [g | n])) = [eta a with n |-> a ⊨ g] ⊨ f.
Proof.
elim: f=>/= [b||f IHf|s IHs t IHt|s IHs t IHt|s IHs t IHt] //.
- by case: eqVneq.
- by rewrite IHf.
- by rewrite IHs IHt.
- by rewrite IHs IHt.
- by rewrite IHs IHt.
Qed.

Lemma subst_eq1 {A : eqType} (a1 a2 : valuation A) f : a1 =1 a2 -> (a1 ⊨ f) = (a2 ⊨ f).
Proof.
move=>H; elim: f=>/= [||f IHf|f IHf g IHg|f IHf g IHg|f IHf g IHg] //.
- by rewrite IHf.
- by rewrite IHf IHg.
- by rewrite IHf IHg.
- by rewrite IHf IHg.
Qed.

End SubstitutionLemmas.

Section Sema_Craig.

Lemma subst_true_false {A : eqType} v (f : formula A) n :
  v ⊨ f -> v ⊨ (Or (f [ Top | n ]) (f [ Bot | n ])).
Proof.
move=>/=; rewrite !substitution_lemma /=.
move=>Hv; apply/orP.
case Hvn: (v n).
- left; congr (_ = _) : Hv; apply: subst_eq1=>x /=.
  by case: eqVneq=>// ->.
right; congr (_ = _) : Hv; apply: subst_eq1=>x /=.
by case: eqVneq=>// ->.
Qed.

Theorem interpolation {A : choiceType} (g d : formula A) :
  ∙⊨ Imp g d -> exists r, [/\ ∙⊨ Imp g r,
                              ∙⊨ Imp r d,
                              (* the vocabulary condition *)
                              atoms r `<=` atoms g &
                              atoms r `<=` atoms d].
Proof.
move: {2}(atoms g `\` atoms d) (erefl (atoms g `\` atoms d)); move: g=>/[swap].
apply: fset1U_ind=>[|x f Nx IH] g + Hi.
- move/eqP; rewrite fsetD_eq0=>Hgd.
  by exists g; split=>//= v; apply/implyP.
move=>Hgd.
have [Hxg Hxd]: (x \in atoms g /\ x \notin atoms d).
- by apply/andP; rewrite andbC -in_fsetD Hgd in_fset1U eqxx.
set g' := (Or (g [ Top | x ]) (g [ Bot | x ])).
have H' : atoms g' `<=` atoms g.
- rewrite /g' /= !subst_atoms //= fset0U fsetU0 fsetUid.
  by exact: fsubsetDl.
have Hi' : forall v, v ⊨ Imp g' d.
- move=>v /=; apply/implyP.
  rewrite !substitution_lemma /=.
  case/orP=>H.
  - move: (Hi [eta v with x |-> true])=>/= /implyP /(_ H).
    by rewrite irrelevant_atom.
  move: (Hi [eta v with x |-> false])=>/= /implyP /(_ H).
  by rewrite irrelevant_atom.
have Ha' : atoms g' `\` atoms d = f.
- rewrite /= !subst_atoms //= fset0U fsetU0 fsetUid.
  rewrite fsetDDl fsetUC -fsetDDl Hgd.
  by rewrite fsetDUl fsetDv fset0U; apply: mem_fsetD1.
case: (IH _ Ha' Hi')=>rho [Hr1 Hr2 Hr3 Hr4].
exists rho; split=>//; last by apply/fsubset_trans/H'.
move=>v /=; apply/implyP=>Hvg.
move: (Hr1 v)=>/= /implyP; apply.
by apply: subst_true_false.
Qed.

End Sema_Craig.

From Equations Require Import Equations.

Section Sema_Craig_Fn.

(* separating the algorithm *)
(* not extraction-friendly due to the use of finmap *)
Equations? interpolate {A : choiceType}
                       (g d : formula A) : formula A
                       by wf #|` (atoms g `\` atoms d)| lt :=
interpolate g d with (fset_0Vmem (atoms g `\` atoms d)) := {
  | inl _ => g
  | inr (@exist x Hx) => interpolate (Or (g [ Top | x ]) (g [ Bot | x ])) d
}.
Proof.
apply: ssrnat.ltP.
move: (Hx); rewrite in_fsetD => /andP [_ Hg].
rewrite !subst_atoms //= !fsetU0 fsetUid fsetDDl
  fsetUC -fsetDDl cardfsD ltn_subrL !cardfs_gt0.
apply/andP; split; apply/fset0Pn; exists x=>//.
by rewrite in_fsetI in_fset1 Hx eqxx.
Qed.

Theorem nonexistential_interpolation {A : choiceType} (g d : formula A) :
  ∙⊨ Imp g d -> [/\ ∙⊨ Imp g (interpolate g d),
                    ∙⊨ Imp (interpolate g d) d &
                    atoms (interpolate g d) `<=` (atoms g `&` atoms d)].
Proof.
apply_funelim (interpolate g d)=>{}A {}g {}d.
- move=>E _ H; split=>//.
  - by move=>v; apply/implyP.
  by rewrite fsubsetIidl -fsetD_eq0 E.
move=>x /[dup]; rewrite {1}in_fsetD => /andP [Hd Hg] Hx.
set g' := (Or (g [ Top | x ]) (g [ Bot | x ])).
move=>IH _ H.
have: ∙⊨ Imp g' d.
- move=>v /=; apply/implyP.
  rewrite !substitution_lemma /=.
  case/orP=>H1.
  - move: (H [eta v with x |-> true])=>/= /implyP /(_ H1).
    by rewrite irrelevant_atom.
  move: (H [eta v with x |-> false])=>/= /implyP /(_ H1).
  by rewrite irrelevant_atom.
move=>/[dup] H'.
case/IH=>H1 H2 H3; split=>//.
- move=>v; apply/implyP=>Hv.
  move/implyP: (H1 v); apply.
  by apply: subst_true_false.
apply: (fsubset_trans H3)=>/=; apply: fsetSI.
by rewrite !subst_atoms //= !fsetU0 fsetUid fsubD1set.
Qed.

End Sema_Craig_Fn.
