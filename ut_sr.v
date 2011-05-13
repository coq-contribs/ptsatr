(** * The Subject Reduction Property. *)
Require Import base.
Require Import ut_term.
Require Import ut_red.
Require Import ut_env.
Require Import ut_typ.
Require Import List.

Module Type ut_sr_mod  (X:term_sig) (Y:pts_sig X) (TM:ut_term_mod X) (EM:ut_env_mod X TM) (RM: ut_red_mod X TM).
 Include (ut_typ_mod X Y TM EM RM).
  Import TM EM RM.
Open Scope UT_scope.

(** In order to prove SR, we need to be able to talk
about reduction inside a context. *)

Reserved Notation " a →e b " (at level 20).
Reserved Notation " a →→e b "(at level 20).
Reserved Notation " a ≡e b " (at level 20).


(* How to deal with Beta reduction in the context *)
Inductive Beta_env : Env -> Env -> Prop :=
 | Beta_env_hd   : forall A B Γ , A →  B  -> (A::Γ) →e (B::Γ)
 | Beta_env_cons : forall A Γ Γ', Γ →e Γ' -> (A::Γ) →e (A::Γ')
where " E →e F " := (Beta_env E F) : UT_scope.

Inductive Betas_env : Env -> Env -> Prop :=
 | Betas_env_refl  : forall Γ       , Γ →→e Γ
 | Betas_env_Beta  : forall Γ Γ'    , Γ →e Γ'  -> Γ →→e Γ' 
 | Betas_env_trans : forall Γ Γ' Γ'', Γ →→e Γ' -> Γ' →→e Γ'' -> Γ →→e Γ''
where " E →→e F" := (Betas_env E F) : UT_scope.

Inductive Betac_env : Env -> Env -> Prop :=
 | Betac_env_Betas : forall Γ Γ'    , Γ →→e Γ' -> Γ ≡e Γ'
 | Betac_env_sym   : forall Γ Γ'    , Γ ≡e  Γ' -> Γ' ≡e Γ
 | Betac_env_trans : forall Γ Γ' Γ'', Γ ≡e  Γ' -> Γ' ≡e Γ'' -> Γ ≡e Γ''
where "E ≡e F" := (Betac_env E F) : UT_scope.


Hint Constructors Beta_env Betas_env Betac_env.

(** Some basic properties of Beta inside context.*)
Lemma Betas_env_nil : forall Γ, nil →→e Γ -> Γ = nil.
intros. remember (@nil Term) as N. revert HeqN.
induction H; intros; subst; try discriminate. 
trivial. inversion H. rewrite IHBetas_env1 in *; trivial.
intuition.
Qed.

Lemma Betas_env_nil2 : forall Γ, Γ →→e nil -> Γ = nil.
intros. remember (@nil Term) as N. revert HeqN.
induction H; intros; subst; try discriminate. 
trivial. inversion H. rewrite IHBetas_env2 in *; trivial.
intuition.
Qed.

Lemma Betas_env_inv :forall A B Γ Γ', (A::Γ)  →→e ( B::Γ') -> A →→ B /\ Γ →→e Γ'.
intros. remember (A::Γ) as Γ1; remember (B::Γ') as Γ2.
revert A B Γ Γ' HeqΓ1 HeqΓ2. induction H; intros; subst; try discriminate.
injection HeqΓ2; intros; subst; clear HeqΓ2. intuition.
inversion H; subst; clear H.  intuition. intuition.
destruct Γ'. apply Betas_env_nil in H0. discriminate.
destruct (IHBetas_env1 A t Γ0 Γ') as ( ? & ?); trivial. clear IHBetas_env1.
destruct (IHBetas_env2 t B Γ' Γ'0) as ( ? & ?); trivial. clear IHBetas_env2.
eauto.
Qed.

Lemma Betas_env_hd : forall A B Γ , A→→B -> (A::Γ) →→e (B::Γ).
intros.
induction H.
constructor.
constructor; apply Beta_env_hd; trivial.
apply Betas_env_trans with (N::Γ); intuition.
Qed.

Lemma Betas_env_cons : forall A Γ Γ', Γ →→e Γ' -> (A::Γ) →→e (A::Γ').
intros.
induction H.
constructor.
constructor; apply Beta_env_cons; trivial.
apply Betas_env_trans with (A::Γ'); trivial.
Qed.

Lemma Betas_env_comp : forall A B Γ Γ', A→→B -> Γ →→e Γ' -> (A::Γ) →→e (B::Γ').
intros.
apply Betas_env_trans with (A::Γ').
apply Betas_env_cons; trivial.
apply Betas_env_hd; trivial.
Qed.

(** There is two ways to prove SR: either we prove that reduction inside the
context and inside the term "at the same time" is valid, or we first do this
for the context only at first, but we need to weaken a little the hypothesis.
  Here we choose the second solution.*)
(** First step toward full SR: if we do reductions inside the context
  of a valid judgment, and if the resulting context is well-formed, 
  then the judgement is still valid with the resulting context. *)
Lemma Beta_env_sound :   forall Γ M T, Γ ⊢ M : T -> forall Γ', Γ' ⊣ -> Γ →e Γ' -> Γ' ⊢ M : T .
induction 1; intros.
(**)
constructor; trivial.
(**)
revert A v H0 H H1. 
induction H2; intros. destruct H0 as (AA&  ? & ?). inversion H3; subst; clear H3.
inversion H1; subst; clear H1. inversion H2; subst; clear H2.
apply Cnv with ( B  ↑ 1 ) s. intuition.
constructor. econstructor;apply H1. exists B; intuition.
change !s with !s ↑ 1. apply thinning with s0 ;trivial.
constructor. trivial. exists AA; intuition.
destruct H0 as (AA&  ? & ?).  inversion H3; subst; clear H3.
constructor. trivial. exists A; intuition.
change (S(S n)) with (1+S n). change #(S n) with (#n  ↑ 1).
rewrite <- lift_lift.
inversion H1; subst; clear H1.
apply thinning with s; trivial. apply IHBeta_env. eauto. inversion H; subst; clear H. eauto. 
eauto. 
(**)
econstructor. apply H. apply IHtyp1; eauto. apply IHtyp2; eauto.
(**)
econstructor. apply H. apply IHtyp1; eauto. apply IHtyp2; eauto. apply IHtyp3; eauto.
(**)
econstructor.  apply IHtyp1; eauto. apply IHtyp2; eauto.
(**)
econstructor. apply H. eapply IHtyp1; eauto. apply IHtyp2; eauto.
Qed.

(** Same with expansion in the context.*)
Lemma Beta_env_sound_up :   forall Γ M T, Γ ⊢ M : T -> forall Γ', Γ' ⊣ -> Γ' →e Γ -> Γ' ⊢ M : T  .
induction 1; intros.
(**)
constructor; trivial.
(**)
revert A v H0 H H1. induction H2; intros. destruct H0 as (AA&  ? & ?). inversion H3; subst; clear H3.
inversion H1; subst; clear H1. inversion H2; subst; clear H2.
apply Cnv with ( A  ↑ 1 ) s. intuition.
constructor. econstructor; apply H1.  exists A; intuition.
change !s with !s ↑ 1. apply thinning with s0 ;trivial.
constructor. trivial. exists AA; intuition.
destruct H0 as (AA&  ? & ?).  inversion H3; subst; clear H3.
constructor. trivial. exists A; intuition.
change (S(S n)) with (1+S n). change #(S n) with (#n  ↑ 1).
rewrite <- lift_lift.
inversion H1; subst; clear H1.
apply thinning with s; trivial. apply IHBeta_env. exists AA; intuition. inversion H; subst; clear H. eauto. 
eauto.
(**)
econstructor. apply H. apply IHtyp1; eauto. apply IHtyp2; eauto.
(**)
econstructor. apply H. apply IHtyp1; eauto. apply IHtyp2; eauto. apply IHtyp3; eauto.
(**)
econstructor.  apply IHtyp1; eauto. apply IHtyp2; eauto.
(**)
econstructor. apply H. eapply IHtyp1; eauto. apply IHtyp2; eauto.
Qed.

(** Second Step: reduction in the term.*)
Lemma Beta_sound : forall Γ M T, Γ ⊢ M : T -> forall N, M → N ->  Γ ⊢ N : T.
induction 1; intros.
(*1*)
inversion H1.
(*2*)
inversion H1.
(*3*)
inversion H2; subst; clear H2. econstructor; eauto. econstructor. apply H. intuition.
eapply Beta_env_sound. apply H1. eauto. intuition.
(*4*)
inversion H3; subst; clear H3. eauto.
apply Cnv with ( Π (A'), B) s3. eauto.
econstructor. apply H. eauto.
eapply Beta_env_sound. apply H1. econstructor. eauto. intuition.
eapply Beta_env_sound. apply H2. econstructor. eauto. intuition.
econstructor; eauto.
(*5*)
inversion H1; subst; clear H1.
assert (exists u, Γ ⊢ Π(A),B : !u). apply TypeCorrect in H.
destruct H. destruct H; discriminate. trivial.
destruct H1. apply gen_pi in H1 as (s & t & u & h); decompose [and] h; clear h.
apply gen_la in H  as (u1 & u2 & u3 & D & ? & ? & ? & ? & ?).
apply PiInj in H as (? & ?).
eapply Cnv with (s := t). eapply Betac_subst2. apply Betac_sym. apply H9.
eapply substitution. apply H7. eapply Cnv. apply H. apply H0. apply H6. constructor.
eauto. change !t with (!t  [ ← N] ). eapply substitution. apply H5. apply H0. constructor.
eauto.

econstructor.  eauto. trivial.
assert (exists u, Γ ⊢ Π(A),B : !u). apply TypeCorrect in H.
destruct H. destruct H; discriminate. trivial.
destruct H1. apply gen_pi in H1 as (s & t & u & h); decompose [and] h; clear h.
apply Cnv with (B [← N']) t. apply Betac_subst. auto.
econstructor. apply H. eauto.
change !t with (!t  [ ← N] ). eapply substitution. apply H6. apply H0. constructor.
eauto.
(**)
eauto.
Qed.

(** With both lemmas, we can now prove the full SR.*)
Lemma SubjectRed : forall Γ M T, Γ ⊢ M : T-> 
  forall N , M →→ N -> Γ ⊢ N : T.
intros. induction H0.
trivial. eapply Beta_sound.
apply H. trivial. intuition.
Qed.

(** Reduction in the type is valid.*)
Lemma Betas_typ_sound : forall Γ M T, Γ ⊢ M : T -> 
 forall T', T →→ T' -> Γ ⊢ M : T'.
intros.
assert ((exists s, T = !s )\/ exists s,  Γ ⊢ T : !s ) by ( apply TypeCorrect in H; intuition).
destruct H1 as [[s Hs]|[s Hs]].
rewrite Hs in *. apply Betas_S in H0. rewrite H0; trivial.
apply Cnv with T s; intuition.
apply SubjectRed with T; intuition.
Qed.

(** Wellformation of a context after reduction.*)
Lemma Beta_env_sound2 : forall Γ Γ', Γ ⊣ -> Γ →e Γ' -> Γ' ⊣.
intros. induction H0; intuition.
inversion H; subst; clear H. 
econstructor. eapply Beta_sound. apply H2. trivial.
inversion H; subst; clear H.
econstructor. eapply Beta_env_sound. apply H2.  apply IHBeta_env.
eauto. trivial.
Qed.

Lemma Betas_env_sound2 : forall Γ Γ', Γ ⊣ -> Γ →→e Γ' -> Γ' ⊣.
intros.
induction H0; intuition.
eapply Beta_env_sound2. apply H. trivial.
Qed.

Lemma Betas_env_sound :   forall Γ M T, Γ ⊢ M : T-> forall Γ', Γ →→e Γ' -> Γ' ⊢ M : T.
intros.
induction H0; intuition.
eapply Beta_env_sound. apply H. apply Beta_env_sound2 with Γ. apply wf_typ in H. trivial.
trivial. trivial.
Qed.

Lemma Betas_env_sound_up :   forall Γ M T, Γ ⊢ M : T -> forall Γ', Γ' ⊣ -> Γ' →→e Γ -> Γ' ⊢ M : T.
intros. revert M T H H0 .
induction H1; intros.
trivial.
eapply Beta_env_sound_up. apply H0. trivial. trivial.
apply IHBetas_env1. apply IHBetas_env2. trivial. apply Betas_env_sound2 with Γ; trivial.
trivial.
Qed.


(** In its complete form: SubjectReduction. *)
Lemma Subject_Reduction :  forall Γ M T, Γ ⊢ M : T ->
  forall Γ' N T', M →→ N -> Γ →→e Γ' ->  T →→ T' -> Γ' ⊢ N : T'.
intros.
apply Betas_typ_sound with T; intuition.
apply Betas_env_sound with Γ; intuition.
apply SubjectRed with M; intuition.
Qed.

End ut_sr_mod.



