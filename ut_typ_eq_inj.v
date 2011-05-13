(** * Definition of a weaker form a Pi injectivity for PTSe

Since Strong Pi injectivity is wrong in the general case, we define
here a weaker form of Pi injectivity, which is informative enought
to directly prove Subject Reduction. However, we still don't know if
this injectivity is provable without using PTS_{atr} and the general
equivalence. *)

Require Import base.
Require Import ut_term ut_red ut_env ut_typ ut_typ_eq ut_sr.
Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt.
Require Import Plus Minus.
Require Import typ_annot glue final_result.


Module ut_typ_eq_inj_mod (X:term_sig) (Y:pts_sig X).
  Include Theory X Y.
  Import X Y.

Reserved Notation "Γ ⊢e M = N " (at level 80, M, N at level 30, no associativity).

(* Definition of the weak equality *)
Inductive wtyp_eq : Env -> Term -> Term -> Prop :=
 | wtyp_eq_intro : forall Γ A B s, Γ ⊢e A = B : !s -> Γ ⊢e A = B
 | wtyp_eq_intro2 : forall Γ A B s, Γ ⊢e A = B : !s -> Γ ⊢e  B = A
 | wtyp_eq_trans : forall Γ A B C, Γ ⊢e A = B -> Γ ⊢e B = C -> Γ ⊢e A = C
where "Γ ⊢e M = N" := (wtyp_eq Γ M N): UT_scope.

Hint Constructors wtyp_eq.

Open Scope UT_scope.

Lemma wtyp_eq_sym: forall Γ A B, Γ ⊢e B = A -> Γ ⊢e A = B.
induction 1; eauto.
Qed.

Hint Resolve wtyp_eq_sym.

Lemma weak_to_PTSe : forall Γ A B, Γ ⊢e A = B -> exists a, exists b, Γ ⊢e A : !a /\ Γ ⊢e B : !b.
induction 1; intros.
exists s; exists s; split. apply left_reflexivity in H; trivial. apply right_reflexivity in H; trivial.
exists s; exists s; split. apply right_reflexivity in H; trivial. apply left_reflexivity in H; trivial.
destruct IHwtyp_eq1 as (a & _ & ? & _ ). destruct IHwtyp_eq2 as ( ? & c & _ & ? ).
exists a; exists c; intuition.
Qed.

Lemma weak_to_PTS : forall Γ A B, Γ ⊢e A = B -> A ≡ B.
induction 1; intros.
apply FromPTSe_to_PTS in H; intuition.
apply FromPTSe_to_PTS in H; intuition.
eauto.
Qed.

Lemma wconv_in_env : forall Γ A B, Γ ⊢e A = B -> forall M T, A::Γ ⊢e M : T -> B::Γ ⊢e M : T.
induction 1; intros.
change (B::Γ) with (nil++B::Γ). eapply conv_in_env. apply H0. simpl; reflexivity. apply H.
apply right_reflexivity in H; trivial.

change (A::Γ) with (nil++A::Γ). eapply conv_in_env. apply H0. simpl; reflexivity. apply cSym; apply H.
apply left_reflexivity in H; trivial.

eauto.
Qed.

Lemma Cnv_wtyp_eq : forall Γ M T, Γ ⊢e M : T -> forall T', Γ ⊢e T = T' -> Γ ⊢e M : T'.
intros. revert M H. induction H0; intros.
eauto. eauto. eauto.
Qed. 

Lemma Cnv_eq_wtyp_eq : forall Γ M N T, Γ ⊢e M = N : T -> forall T', Γ ⊢e T = T' -> Γ ⊢e M = N : T'.
intros. revert M N H. induction H0; intros.
eauto. eauto. eauto.
Qed. 


(* Generation lemmas for PTSe: we can't state them with the usual equality, but weak equality is just fine *)
Lemma gen_pi : forall Γ A B T, Γ ⊢e Π(A),B : T -> exists s1, exists s2, exists s3, 
    (T = !s3 \/ Γ⊢e T = !s3) /\ Rel s1 s2 s3 /\ Γ ⊢e A : !s1  /\ A::Γ ⊢e B : !s2 .
intros. remember (Π(A),B) as P. revert A B HeqP. induction H; intros; subst; try discriminate.
clear IHtyp1 IHtyp2. injection HeqP; intros; subst; clear HeqP.
exists s; exists t; exists u; intuition.
destruct (IHtyp A0 B0) as (a & b & c & ? & ? & ? &  ?); trivial. exists a; exists b; exists c; split.
destruct H1; right. subst. eauto. eauto.
intuition.
Qed.

Lemma gen_la : forall Γ A M T, Γ ⊢e λ[A],M : T -> exists s1, exists s2, exists s3, exists B, 
    Γ ⊢e T =  Π(A), B /\ Rel s1 s2 s3 /\ Γ ⊢e A : !s1 /\ A::Γ ⊢e M : B /\ A::Γ ⊢e B : !s2.
intros. remember (λ[A],M) as L. revert A M HeqL. induction H; intros ; subst; try discriminate.
clear IHtyp1 IHtyp2 IHtyp3. injection HeqL; intros; subst; clear HeqL.
exists s1; exists s2; exists s3; exists B; intuition.
econstructor. eapply cRefl. econstructor. apply H. trivial. trivial.
destruct (IHtyp A0 M) as (a & b & c & D &? &? & ? & ? & ?); trivial. clear IHtyp.
exists a; exists b; exists c; exists D; split. eauto. intuition.
Qed.

Lemma gen_app : forall Γ M N T, Γ ⊢e M · N : T -> exists A, exists B, Γ ⊢e T = B[← N] /\ Γ ⊢e M : Π(A),B /\ Γ ⊢e N : A.
intros. remember (M·N) as A. revert M N HeqA. induction H; intros; subst; try discriminate.
clear IHtyp1 IHtyp2. injection HeqA; intros; subst; clear HeqA.
exists A; exists B; intuition.
apply TypeCorrect_Refl in H. destruct H as (s & [ | ]). discriminate.
apply gen_pi in H as (s1 & s2 & s3 & ?  & ? & ? & ?).
apply wtyp_eq_intro with s2. apply cRefl. change !s2 with !s2[← N].
eapply substitution. apply H3. apply H0. constructor.
destruct (IHtyp M N) as (K & L & ? & ?& ?); trivial. exists K; exists L; split.
eauto. intuition.
Qed.



(* Weak Pi Injectivity for PTSe *)
Lemma wPiInj : forall Γ A B C D, Γ ⊢e Π(A),B = Π(C),D -> Γ ⊢e A = C /\ A::Γ ⊢e B = D.
intros. destruct (weak_to_PTSe _ _ _ H) as (u & u' & ? & ?).
apply weak_to_PTS in H. apply PiInj in H as (? & ?).
apply Betac_confl in H as (U & ? & ?). apply Betac_confl in H2 as (V & ? & ?).
apply gen_pi in H0 as (s & t & ? &  h); decompose [and] h; clear h.
apply gen_pi in H1 as (s' & t' & ? &  h); decompose [and] h; clear h.
assert (Γ ⊢e A = C).
  apply wtyp_eq_trans with U. apply wtyp_eq_intro with s.
  apply PTSe_SR_trans; trivial. apply wtyp_eq_intro2 with s'. apply PTSe_SR_trans; trivial.
split; trivial.
apply wtyp_eq_trans with V. apply wtyp_eq_intro with t. apply PTSe_SR_trans; trivial.
apply wtyp_eq_intro2 with t'. apply PTSe_SR_trans; trivial. 
eapply wconv_in_env. apply wtyp_eq_sym; apply H10. trivial.
Qed.



Lemma wtyp_eq_subst : forall Γ M N , Γ  ⊢e M = N   -> forall Δ P A, Δ  ⊢e P : A -> 
 forall Γ' n , sub_in_env Δ P A n Γ Γ' ->  Γ' ⊢e M [ n ←P ] = N [ n ←P ].
induction 1; intros.
apply wtyp_eq_intro with s. change !s with !s[n← P]. eapply substitution. apply H. apply H0. trivial.
apply wtyp_eq_intro2 with s. change !s with !s[n← P]. eapply substitution. apply H. apply H0. trivial.
eauto.
Qed.

(* A direct proof of Subject Reduction from Weak Pi Injectivity *)
Lemma SRe : forall Γ M T, Γ ⊢e M : T -> forall N, M → N -> Γ ⊢e M = N : T.
intros. revert Γ T H. induction H0; intros.
apply gen_app in H as (C & B & ? & ? & ?).
apply gen_la in H0 as (s1 & s2  & s3 & D & ? & ? & ? & ? & ?).
apply wPiInj in H0 as (? & ?).
apply Cnv_eq_wtyp_eq with D[← N]. eapply cBeta. apply H2. trivial. trivial.
trivial. apply Cnv_wtyp_eq with C; intuition. apply wtyp_eq_trans with B[← N].
apply wtyp_eq_sym. eapply wtyp_eq_subst. apply H6. apply H1. constructor.
intuition.
(**)
apply gen_app in H as (A & B & ? & ? & ?).
apply Cnv_eq_wtyp_eq with B[← N]. econstructor. apply IHBeta. apply H1. apply cRefl. trivial. intuition.
(**)
apply gen_app in H as (A & B & ? & ? & ?).
apply Cnv_eq_wtyp_eq with B[← N]. econstructor. apply cRefl; apply H1. apply IHBeta. trivial. intuition.
(**)
apply gen_la in H as (s1 & s2 & s3 & D & h); decompose [and] h; clear h.
apply Cnv_eq_wtyp_eq with (Π(A),D). econstructor. apply H2. apply cRefl; trivial. apply IHBeta; trivial. trivial. intuition.
(**)
apply gen_la in H as (s1 & s2 & s3 & D & h); decompose [and] h; clear h.
apply Cnv_eq_wtyp_eq with (Π(A),D). econstructor. apply H2. apply IHBeta; trivial. apply cRefl; trivial.  trivial. intuition.
(**)
apply gen_pi in H as (s1 & s2 & s3 & h); decompose [and] h; clear h.
destruct H. subst. econstructor. apply H2. apply cRefl; trivial. apply IHBeta; trivial. 
apply Cnv_eq_wtyp_eq with !s3. econstructor. apply H2. apply cRefl; trivial. apply IHBeta; trivial. intuition.
(**)
apply gen_pi in H as (s1 & s2 & s3 & h); decompose [and] h; clear h.
destruct H. subst. econstructor. apply H2. apply IHBeta; trivial.  apply cRefl; trivial.  
apply Cnv_eq_wtyp_eq with !s3. econstructor. apply H2. apply IHBeta; trivial.  apply cRefl; trivial. intuition. 
Qed.

End ut_typ_eq_inj_mod.


