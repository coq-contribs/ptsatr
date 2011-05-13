(** * Definition of PTS_{atr} and proof of Confluence
In order to prove the equivalence between PTS and PTSe, Adams built a system
called Typed Parallel One Step Reduction that mimics the usual parallel reduction
to prove that a typed equality judgement is confluent. He emphasises the use of
an additionnal annotation (the co-domain [(x)B]) in order to be able to track
typing information, and prove that PTS_{atr} enjoys the diamon property.*)
(** His result is restricted to "functional" PTS. To extend it to all PTS, we
added a second annotation (the domain [A]) and prove that every PTS is
equivalent to its PTSe counterpart.*)
Require Import base term.
Require Import red.
Require Import env.
Require Import base.
Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt Plus Minus.


Module PTS_ATR_mod (X:term_sig) (Y:pts_sig X) (TM:term_mod X) (EM: env_mod X TM) (RM: red_mod X TM).
 Import X Y TM EM RM.

(** PTS_{atr} typind definition: we define at the same time the
 one step and the multistep in order to keep track of some well-typed path
 between two possible domains in the typ_beta case.*)
Reserved Notation "Γ ⊢ s ▹ t : A" (at level 80, s, t, T at level 30, no associativity) .
Reserved Notation "Γ ⊣ " (at level 80, no associativity).
Reserved Notation "Γ ⊢ s ▹▹ t : T " (at level 80, s, t, T at level 30, no associativity) .

Inductive wf : Env -> Prop :=
  | wf_nil : nil ⊣
  | wf_cons : forall Γ A A' s, Γ ⊢ A ▹ A' : !s -> A::Γ ⊣
where "Γ ⊣" := (wf Γ) : Typ_scope
with typ : Env -> Term -> Term -> Term -> Prop :=
 | typ_var : forall Γ x A, Γ ⊣ ->  A ↓ x  ⊂ Γ -> Γ ⊢ #x ▹ #x  : A
 | typ_sort : forall Γ s1 s2, Ax s1 s2 -> Γ ⊣  -> Γ ⊢ !s1 ▹ !s1 : !s2
 | typ_pi : forall Γ s1 s2 s3 A A' B B', Rel s1 s2 s3 ->
    Γ ⊢ A ▹ A' : !s1 -> A::Γ ⊢ B ▹ B' : !s2 -> Γ ⊢ Π(A),B ▹ Π(A'),B' : !s3
 | typ_la : forall Γ A A' B B' M M' s1 s2 s3, Rel s1 s2 s3 -> 
    Γ ⊢ A ▹ A' : !s1 -> A::Γ ⊢ B ▹ B' : !s2 -> A::Γ ⊢ M ▹ M' : B ->
    Γ ⊢ λ[A],M ▹ λ[A'],M' : Π(A),B
 | typ_app : forall Γ M M' N N' A A' B B' s1 s2 s3, Rel s1 s2 s3 -> 
   Γ ⊢ A ▹ A' : !s1 -> A::Γ ⊢ B ▹ B' : !s2 -> Γ ⊢ M ▹ M' : Π(A),B -> Γ ⊢ N ▹ N' : A ->
    Γ ⊢ (M ·(A,B) N) ▹ (M'·(A',B') N') : B[ ←N] 
 | typ_beta : forall Γ M M' N N' A A' A'' A''' A0 B B' s1 s2 s3, Rel s1 s2 s3 -> 
   Γ ⊢ A ▹ A' : !s1 -> Γ ⊢ A'' ▹ A''' : !s1  -> Γ ⊢ A0 ▹▹ A : !s1 -> Γ ⊢ A0 ▹▹ A'' : !s1 ->
   A::Γ ⊢ B ▹ B' : !s2 -> A::Γ ⊢ M ▹ M' : B -> Γ ⊢ N ▹ N' : A ->
    Γ ⊢ ((λ[A],M) ·(A'',B) N) ▹ M'[ ← N'] : B[ ←N]
 | typ_red : forall Γ M N A B s, Γ ⊢ M ▹ N : A -> Γ ⊢ A ▹ B : !s -> Γ ⊢ M ▹ N : B
 | typ_exp : forall Γ M N A B s, Γ ⊢ M ▹ N : B -> Γ ⊢ A ▹ B : !s -> Γ ⊢ M ▹ N : A
where "Γ ⊢ M ▹ N : T" := (typ Γ  M N T) : Typ_scope 
with typ_reds : Env -> Term -> Term  -> Term -> Prop :=
 | typ_reds_intro : forall Γ s t T, Γ ⊢ s ▹ t : T -> Γ ⊢ s ▹▹ t : T
 | typ_reds_trans : forall Γ s t u T , Γ ⊢ s ▹▹ t : T -> Γ ⊢ t ▹▹ u : T -> Γ ⊢ s ▹▹ u : T
where "Γ ⊢ s ▹▹ t : T " := (typ_reds Γ s t T) : Typ_scope.

Open Scope Typ_scope.

(* begin hide *)
Hint Constructors wf typ typ_reds.

Scheme typ_ind' := Induction for typ Sort Prop
      with typ_reds_ind' := Induction for typ_reds Sort Prop
      with wf_ind' := Induction for wf Sort Prop.

Combined Scheme typ_induc from typ_ind', typ_reds_ind', wf_ind'.
(* end hide *)

(** Weakening property for PTS_{atr} .*)
Theorem weakening: (forall Δ t t' T, Δ ⊢ t ▹ t' : T -> forall Γ d d' s n Δ', 
    ins_in_env Γ d n Δ Δ' ->   Γ ⊢ d ▹ d' :!s -> Δ' ⊢ t ↑ 1 # n ▹ t' ↑ 1 # n : T ↑ 1 # n ) /\
(forall Δ t t' T, Δ ⊢ t ▹▹ t' : T -> forall Γ d d' s n Δ', 
    ins_in_env Γ d n Δ Δ' ->   Γ ⊢ d ▹ d' :!s -> Δ' ⊢ t ↑ 1 # n ▹▹ t' ↑ 1 # n : T ↑ 1 # n ) /\
(forall Γ, Γ ⊣ -> forall Δ Γ' n A A' s, ins_in_env Δ A n Γ Γ' -> Δ ⊢ A ▹ A' : !s -> Γ' ⊣).
apply typ_induc; intros; simpl.
destruct le_gt_dec. constructor. eapply H; eauto.
destruct i as (u & ?& ?).
rewrite H2. exists u; split.
change (S (S x)) with (1+ S x). rewrite liftP3; trivial. intuition. simpl; intuition. eapply ins_item_ge. apply H0.
trivial. trivial.
constructor. eapply H; eauto. eapply ins_item_lift_lt. apply H0. trivial. trivial.
(**)
econstructor; trivial. eapply H; eauto.
(**)
apply typ_pi with s1 s2; trivial.
change !s1 with (!s1 ↑ 1 # n); eapply H; eauto.
change !s2 with (!s2 ↑ 1 # (S n)); eapply H0; eauto.
(**)
apply typ_la with (B'↑1# (S n)) s1 s2 s3; trivial.
change !s1 with (!s1 ↑ 1 # n); eapply H; eauto.
change !s2 with (!s2 ↑ 1 # (S n)); eapply H0; eauto.
eapply H1; eauto.
(** app with annot **)
change n with (0+n); rewrite substP1. simpl.
eapply typ_app. apply r. eapply H; eauto. eapply H0; eauto.
eapply H1; eauto. eapply H2; eauto.
(** beta with annot **)
change n with (0+n); rewrite 2! substP1. simpl.
eapply typ_beta. apply r. eapply H; eauto. eapply H0; eauto.
eapply H1; eauto. eapply H2; eauto. eapply H3; eauto. eapply H4; eauto. 
eapply H5; eauto.
(**)
apply typ_red with (A ↑ 1 # n) s. eapply H; eauto.
change !s with (!s ↑ 1 # n); eapply H0; eauto.
(**)
apply typ_exp with (B ↑ 1 # n) s. eapply H; eauto.
change !s with (!s ↑ 1 # n); eapply H0; eauto.
(* reds *)
constructor; eapply H; eauto. eauto.
(* wf *)
inversion H; subst; clear H. eauto.
(**)
inversion H0; subst; clear H0.
eauto.
apply wf_cons with (A' ↑ 1  # n0) s.
change !s with (!s ↑ 1 # n0); eauto.
Qed.

Theorem thinning :
   forall Γ M N T A A' s,
      Γ ⊢ M ▹ N : T ->
   Γ ⊢ A ▹ A' : !s ->
   A::Γ ⊢ M ↑ 1 ▹ N ↑ 1 : T ↑ 1.
intros.
eapply weakening. apply H. constructor. apply H0.
Qed.


Theorem thinning_reds :
   forall Γ M N T A A' s,
      Γ ⊢ M ▹▹ N : T ->
   Γ ⊢ A ▹ A' : !s ->
   A::Γ ⊢ M ↑ 1 ▹▹ N ↑ 1 : T ↑ 1.
intros.
eapply weakening. apply H. constructor. apply H0.
Qed.

Lemma wf_from_typ : forall  Γ M N T,  Γ ⊢ M ▹ N : T -> Γ ⊣.
induction 1; eauto.
Qed.

Lemma wf_from_typ_reds : forall  Γ M N T,  Γ ⊢ M ▹▹ N : T -> Γ ⊣.
induction 1. apply wf_from_typ in H; trivial.
trivial.
Qed.

Hint Resolve wf_from_typ wf_from_typ_reds.

Theorem thinning_n : forall n Δ Δ',
   trunc n Δ Δ' ->
   forall M N T , Δ' ⊢ M ▹ N : T  -> Δ ⊣ ->
               Δ ⊢ M ↑ n ▹ N ↑ n : T ↑ n.
induction n; intros.
inversion H; subst; clear H. rewrite 3! lift0; trivial.

inversion H; subst; clear H.
change (S n) with (1+n).
replace (M ↑ (1+n)) with ((M ↑ n )↑ 1) by (apply lift_lift).
replace (N ↑ (1+n)) with ((N ↑ n )↑ 1) by (apply lift_lift).
replace (T ↑ (1+n)) with ((T ↑ n )↑ 1) by (apply lift_lift).
inversion H1; subst; clear H1.
eapply thinning. eapply IHn. apply H3. trivial.
apply wf_from_typ in H2; trivial.
apply H2.
Qed.

Theorem thinning_reds_n : forall n Δ Δ',
   trunc n Δ Δ' ->
   forall M N T , Δ' ⊢ M ▹▹ N : T  -> Δ ⊣ ->
               Δ ⊢ M ↑ n ▹▹ N ↑ n : T ↑ n.
induction n; intros.
inversion H; subst; clear H. rewrite 3! lift0; trivial.

inversion H; subst; clear H.
change (S n) with (1+n).
replace (M ↑ (1+n)) with ((M ↑ n )↑ 1) by (apply lift_lift).
replace (N ↑ (1+n)) with ((N ↑ n )↑ 1) by (apply lift_lift).
replace (T ↑ (1+n)) with ((T ↑ n )↑ 1) by (apply lift_lift).
inversion H1; subst; clear H1.
eapply thinning_reds. eapply IHn. apply H3. trivial.
apply wf_from_typ in H2; trivial.
apply H2.
Qed.

(** In order to prove substitution for PTS_{atr}, we first need to prove some
context conversion lemmas, because of the new annotation we added.
We will first prove some weak form of conversion, where the ending context is
supposed to be welltyped. As soon as we will have the substitution property, we
will be able to prove that it's in fact always the case.*)
(** Reduction in context definition .*)
Inductive env_red1 : Env -> Env -> Prop :=
 | red1_intro : forall Γ  A B s , Γ ⊢ A ▹  B : !s  ->  env_red1 (A::Γ) (B::Γ)
 | red1_next : forall A Γ Γ', env_red1 Γ Γ' -> env_red1 (A::Γ) (A::Γ')
.

Hint Constructors env_red1.

Inductive env_red : Env -> Env -> Prop :=
 | r_step : forall Γ Γ', env_red1 Γ  Γ' -> env_red Γ  Γ'
 | r_refl : forall Γ  , env_red Γ  Γ 
 | r_trans : forall Γ  Γ' Γ'', env_red Γ  Γ' -> env_red Γ' Γ'' -> env_red Γ  Γ''.

Hint Constructors env_red.

 Lemma red_item : forall n A  Γ  Γ' ,  A ↓ n ⊂ Γ -> env_red1 Γ Γ' ->  Γ' ⊣ ->  A ↓ n ⊂ Γ' \/ 
   (forall Γ'', trunc (S n) Γ Γ'' -> trunc (S n) Γ' Γ'') /\ (exists B, exists s, Γ' ⊢ A ▹ B : !s /\  B ↓ n ⊂ Γ').
induction n; intros. destruct H as (a & ?& ?). inversion H2; subst; clear H2.
 inversion H0; subst; clear H0. inversion H1; subst; clear H1. right. split; intros.
 inversion H; subst; clear H. constructor; intuition. exists (B ↑ 1); exists s; split.
 change !s with (!s ↑ 1). eapply thinning. trivial. apply H0. exists B; intuition.
 left. exists a; intuition.

 inversion H0; subst; clear H0. destruct H as (a & ?& ?). inversion H0; subst; clear H0.
 left. exists a; split. trivial. constructor; trivial. destruct H as (a & ? & ?). 
 inversion H0; subst; clear H0. destruct (IHn (a ↑ (S n)) Γ0 Γ'0); trivial.
 exists a; intuition. inversion H1; subst; clear H1. apply wf_from_typ in H0; trivial. 
 destruct H as ( ? & ?& ?). apply inv_lift in H; subst. left. exists x; intuition.
 destruct H. destruct H0 as ( a' & s' & ? & ?). right. split; intros. 
 inversion H5; subst; clear H5. constructor. intuition.
 exists ( a' ↑ 1); exists s'; split. change !s' with (!s' ↑ 1). change (S (S n)) with (1+ S n).
 rewrite <- lift_lift. inversion H1; subst; clear H1.  eapply thinning. trivial. apply H6.
 destruct H3 as (b & ?& ?). exists b; split. subst. rewrite lift_lift. trivial. constructor; trivial.
Qed.



Lemma red1_in_env : (forall Γ M N T, Γ ⊢ M ▹ N : T -> forall Γ',  Γ' ⊣ -> env_red1 Γ Γ'-> Γ' ⊢ M ▹ N :  T ) /\
 (forall Γ M N T, Γ ⊢ M ▹▹ N : T -> forall Γ',  Γ' ⊣ -> env_red1 Γ Γ'-> Γ' ⊢ M ▹▹ N :  T ) /\
 (forall Γ, Γ ⊣ -> True).
apply typ_induc; intros; simpl; trivial.
(**) 
destruct (red_item x A Γ Γ' i H1 H0). intuition. destruct H2. destruct H3 as (A' & s & ? & ?).
apply typ_exp with A' s; trivial.  intuition. 
(**)
intuition.
(**)
apply typ_pi with s1 s2; intuition. eapply H0. econstructor. apply H; trivial. intuition.
(**)
apply typ_la with B' s1 s2 s3; intuition.
eapply H0. econstructor. apply H; trivial. intuition.
eapply H1. econstructor. apply H; trivial. intuition.
(**)
eapply typ_app. apply r. intuition.
eapply H0. econstructor. apply H; trivial. intuition.
intuition. intuition.
(**)
eapply typ_beta. apply r. apply H; intuition. apply H0; intuition. apply H1; intuition. intuition.
eapply H3. econstructor. apply H; trivial. intuition.
eapply H4. econstructor. apply H; trivial. intuition.
intuition.
(**)
apply typ_red with A s;intuition.
(**)
apply typ_exp with B s;intuition.
(**)
eauto.
eauto.
Qed.

(** Reflexive, Transitive, Symetric closure of PTS_{atr}. Since we are not
functional, we can't inforce the fact that every step is typed by the same type.
  But we only need the equality at the type level, so we will check that every
  step is welltyped, by a sort, but we will forget about this sort.*)
Reserved Notation "Γ ⊢ s ≡' t " (at level 80, s, t, T at level 30, no associativity) .

Inductive typ_peq : Env -> Term -> Term  -> Prop :=
 | typ_peq_intro : forall Γ A B s, Γ ⊢ A ▹ B : !s -> Γ ⊢ A ≡' B 
 | typ_peq_intro2 : forall Γ A B s, Γ ⊢ B ▹ A : !s -> Γ ⊢ A ≡' B
 | typ_peq_trans : forall Γ A B C , Γ ⊢ A ≡' B  -> Γ ⊢ B ≡' C  -> Γ ⊢ A ≡' C
where "Γ ⊢ s ≡' t " := (typ_peq Γ s t) : Typ_scope.

Hint Constructors typ_peq.

Lemma typ_peq_sym : forall Γ A B  , Γ  ⊢ A ≡' B  -> Γ  ⊢ B ≡' A .
induction 1; eauto.
Qed.

Hint Resolve typ_peq_sym.



Lemma reds_to_conv : forall Γ M N s, Γ ⊢ M ▹▹ N : !s -> Γ ⊢ M ≡' N.
intros. remember !s as S. revert s HeqS. induction H; intros; subst.
eauto. eauto.
Qed.

Hint Resolve reds_to_conv.

(** Conversion in Context definition .*)
Inductive env_conv1 : Env -> Env -> Prop :=
 | conv1_intro : forall Γ  A B , Γ ⊢ A ≡' B  ->  env_conv1 (A::Γ) (B::Γ)
 | conv1_next : forall A Γ Γ', env_conv1 Γ Γ' -> env_conv1 (A::Γ) (A::Γ')
.

Hint Constructors env_conv1.

Inductive env_conv : Env -> Env -> Prop :=
 | c_step : forall Γ Γ', env_conv1 Γ  Γ' -> env_conv Γ  Γ'
 | c_refl : forall Γ  , env_conv Γ  Γ 
 | c_trans : forall Γ  Γ' Γ'', env_conv Γ  Γ' -> env_conv Γ' Γ'' -> env_conv Γ  Γ''.

Hint Constructors env_conv.


Lemma c1_sym : forall Γ Γ', env_conv1 Γ Γ' -> env_conv1 Γ' Γ.
induction 1; intros; intuition.
Qed.

Lemma c_sym : forall Γ Γ', env_conv Γ Γ' -> env_conv Γ' Γ.
induction 1; intros.
apply c1_sym in H; intuition. trivial. eauto.
Qed.

Hint Resolve c_sym.


Lemma env_red1_to_conv1 : forall Γ Γ', env_red1 Γ Γ' -> env_conv1 Γ Γ'.
induction 1; intuition.
eauto.
Qed.

Lemma env_red_to_conv : forall Γ Γ', env_red Γ Γ' -> env_conv Γ Γ'.
induction 1; intuition.
apply env_red1_to_conv1 in H; intuition.
eauto.
Qed.

Hint Resolve env_red_to_conv.


Lemma peq_thinning : forall  Γ A B, Γ ⊢ A ≡' B  -> forall C C' s, Γ ⊢ C ▹ C' : !s 
 -> C::Γ ⊢ A ↑ 1 ≡' B ↑ 1.
induction 1; intros. apply typ_peq_intro with s. change !s with (!s ↑ 1).
apply thinning with C' s0; trivial. apply typ_peq_intro2 with s. change !s with (!s ↑ 1).
apply thinning with C' s0; trivial. eauto.
Qed.

Lemma peq_thinning_n : forall n Δ Δ',
   trunc n Δ Δ' ->
   forall A B , Δ' ⊢ A ≡' B  -> Δ ⊣ ->  Δ ⊢ A ↑ n ≡'  B ↑ n .
induction n; intros.
inversion H; subst; clear H. rewrite 2! lift0; trivial.

inversion H; subst; clear H.
change (S n) with (1+n).
replace (A ↑ (1+n)) with ((A ↑ n )↑ 1) by (apply lift_lift).
replace (B ↑ (1+n)) with ((B ↑ n )↑ 1) by (apply lift_lift).
inversion H1; subst; clear H1.
eapply peq_thinning. eapply IHn. apply H3. trivial.
apply wf_from_typ in H2; trivial.
apply H2.
Qed.


(** Type manipulation functions *)
Lemma typ_pcompat : forall Γ M N A, Γ ⊢ M ▹ N : A -> forall B , Γ ⊢ A ≡' B  -> Γ ⊢ M ▹ N : B.
intros.
revert M N  H.
induction H0; intros.
eauto. eauto. eauto.
Qed.


Lemma typ_red_trans : forall Γ M N A B s, Γ ⊢ M ▹ N : A -> Γ ⊢ A ▹▹ B : !s -> Γ ⊢ M ▹ N : B.
intros. remember !s as S. revert M N H s HeqS. induction H0; intros; subst; eauto.
Qed.

Lemma typ_exp_trans : forall Γ M N A B s, Γ ⊢ M ▹ N : B -> Γ ⊢ A ▹▹ B : !s -> Γ ⊢ M ▹ N : A.
intros. remember !s as S. revert M N H s HeqS. induction H0; intros; subst; eauto.
Qed.


  Lemma conv_item :
   forall n A Γ Γ',  A ↓ n ⊂ Γ -> env_conv1 Γ Γ' -> Γ' ⊣ -> A ↓ n ⊂  Γ' \/
     (forall Γ'', trunc (S n) Γ Γ'' -> trunc (S n) Γ' Γ'') /\ (exists B,  Γ' ⊢ A ≡' B /\   B ↓ n ⊂  Γ').
induction n; intros. destruct H as (u & ?& ?).
inversion H2; subst; clear H2. inversion H0;subst; clear H0.
right. split; intros. inversion H; subst; clear H. constructor. trivial.
exists (lift_rec 1 0 B); split. inversion H1; subst; clear H1. apply peq_thinning with A' s; trivial.
exists B; intuition. left. exists u; intuition.
destruct H as (u & ?& ?). inversion H2; subst; clear H2. inversion H0; subst; clear H0.
left. exists u; intuition. destruct (IHn (lift_rec (S  n) 0 u) l Γ'0 ). exists u; intuition.
trivial. inversion H1; subst; clear H1. apply wf_from_typ in H0; trivial.
left. destruct H as (uu & ?& ?). apply inv_lift in H. subst. exists uu; intuition.
destruct H. right. split; intros. constructor. apply H. inversion H2; subst; clear H2.
trivial. destruct H0 as ( uu &? & ?). destruct H2 as (v & ?& ?). subst.
exists (lift_rec (S (S n)) 0 v); split. change (S (S n)) with (1+ S n).
replace (u ↑ (1+S n)) with ((u ↑ (S n) )↑ 1) by (apply lift_lift).
replace (v ↑ (1+S n)) with ((v ↑ (S n) )↑ 1) by (apply lift_lift).
inversion H1; subst; clear H1. eapply peq_thinning. trivial. apply H6.
exists v; intuition.
Qed.

Lemma   conv1_in_env : (forall Γ M N T, Γ ⊢ M ▹ N : T -> forall Γ', env_conv1 Γ Γ' -> Γ'  ⊣ ->  Γ' ⊢ M ▹ N : T) /\
  (forall Γ M N T, Γ ⊢ M ▹▹ N : T -> forall Γ', env_conv1 Γ Γ' -> Γ'  ⊣ ->  Γ' ⊢ M ▹▹ N : T) /\
  (forall Γ, Γ ⊣ -> True).
apply typ_induc;intros; simpl; trivial.
destruct (conv_item x A Γ  Γ' i H0 H1). intuition.
destruct H2. destruct H3 as (B & ?). apply typ_pcompat with B; intuition.
(**)
intuition.
(**)
apply typ_pi with s1 s2; eauto.
(**)
apply typ_la with B' s1 s2 s3; eauto.
(**)
eapply typ_app; eauto.
(**)
eapply typ_beta;eauto.
(**)
eauto.
(**)
eauto.
(**)
eauto.
eauto.
Qed.

Lemma sub_trunc : forall Γ0 a A n Γ Δ, sub_in_env Γ0 a A n Γ Δ -> trunc n Δ Γ0.
induction 1.
apply trunc_O.
apply trunc_S. trivial.
Qed.

Lemma sub_in_env_item : forall Δ P A n Γ Γ', sub_in_env Δ P A n Γ Γ' -> A ↓ n ∈ Γ.
induction 1; eauto.
Qed.

(* begin hide *)
Lemma typ_reds_to_red_ : forall Γ M N T, Γ ⊢ M ▹▹ N : T -> exists M', Γ ⊢ M ▹ M' : T.
induction 1. exists t; trivial.
trivial.
Qed.


Lemma reds_Pi_ : forall Γ A A' s, Γ ⊢ A  ▹▹ A' : !s -> forall B t u, A::Γ ⊢ B  ▹ B :!t ->
  Rel s t u ->  Γ ⊢ Π (A), B ▹▹ Π (A'), B : !u.
intros until 1. remember !s as S. revert s HeqS. induction H; intros; subst.
constructor. eapply typ_pi; eauto.
apply typ_reds_trans with (Pi t B). eapply IHtyp_reds1. reflexivity. apply H1. trivial.
eapply IHtyp_reds2. reflexivity. eapply conv1_in_env. apply H1. econstructor. eauto.
apply typ_reds_to_red_ in H0. destruct H0 as (? & ? ). econstructor. apply H0. trivial.
Qed.

(* end hide *)
(** Left-Hand reflexivity: this ensure that a valid derivation starts from a well
typed term.*)
Theorem red_refl_lt : forall Γ M N T, Γ ⊢ M ▹ N : T -> Γ ⊢ M ▹ M :T.
induction 1; intros.
constructor; trivial.
constructor; trivial.
apply typ_pi with s1 s2; trivial.
apply typ_la with B' s1 s2 s3; trivial.
eapply typ_app;trivial. apply H. trivial. trivial.
(**)
eapply typ_app;trivial. apply H. trivial. eapply conv1_in_env.
apply IHtyp3. econstructor. apply typ_peq_trans with A0. eauto. eauto.
eauto. eapply typ_pcompat. eapply typ_la. apply H.
trivial. apply IHtyp3. trivial. apply typ_peq_trans with (Π(A0),B).
apply typ_peq_sym. apply reds_to_conv with s3. eapply reds_Pi_; eauto.
eapply conv1_in_env. apply IHtyp3. eauto. apply typ_reds_to_red_ in H2 as (? & ?). econstructor; apply H2.
apply reds_to_conv with s3. eapply reds_Pi_; eauto.
eapply conv1_in_env. apply IHtyp3. eauto. apply typ_reds_to_red_ in H2 as (? & ?). econstructor; apply H2.
apply typ_pcompat with A. trivial. eauto.
(**)
apply typ_red with A s; trivial.
apply typ_exp with B s; trivial.
Qed.

Lemma reds_refl_lt : forall Γ M N T, Γ ⊢ M ▹▹ N : T -> Γ ⊢ M ▹ M :T.
induction 1. apply red_refl_lt in H; trivial.
trivial.
Qed.

(** Substitution Lemma *)
Theorem subst_gen : (forall Γ M N T, Γ ⊢ M ▹ N : T ->
  forall Δ Γ' u U n, sub_in_env Δ u U n Γ Γ' ->
  forall u', Δ ⊢ u ▹ u' : U -> 
  Γ' ⊢ M [ n ← u] ▹ N [ n ← u'] : T [ n ← u])/\
(forall Γ M N T, Γ ⊢ M ▹▹ N : T ->
  forall Δ Γ' u U n, sub_in_env Δ u U n Γ Γ' ->
  forall u', Δ ⊢ u ▹ u' : U -> 
  Γ' ⊢ M [ n ← u] ▹▹ N [ n ← u'] : T [ n ← u])/\
 (forall Γ, Γ ⊣ -> forall Δ P P' A n Γ', Δ ⊢ P ▹ P' : A ->
    sub_in_env  Δ P A n Γ Γ' ->     Γ' ⊣ ).
apply typ_induc; intros.
(* 1 / 8 *)
simpl. destruct lt_eq_lt_dec as [ []| ].
constructor. eapply H. apply H1. apply H0.
eapply nth_sub_item_inf. apply H0. intuition. trivial.
destruct i as (a & ?& ?).
subst. rewrite substP3; intuition.
apply thinning_n with Δ. eapply sub_trunc. apply H0.
replace a with U. trivial. eapply fun_item. eapply sub_in_env_item. apply H0.  trivial.
eapply H. apply H1. apply H0.
destruct i as (a & ? &?).
constructor. eapply H. apply H1. apply H0.
subst. rewrite substP3; intuition.
exists a. split. replace (S (x -1)) with x. trivial.
rewrite minus_Sn_m. rewrite <- pred_of_minus. simpl; trivial. destruct x. apply lt_n_O in l; elim l.
intuition. eapply nth_sub_sup. apply H0. destruct x. apply lt_n_O in l; elim l. rewrite <- pred_of_minus. 
simpl; intuition. replace (S (x -1)) with x. trivial. rewrite minus_Sn_m. rewrite <- pred_of_minus. 
simpl; trivial. destruct x. apply lt_n_O in l; elim l. intuition.
(* 1 / 7 *)
simpl; constructor; trivial.
eapply H. apply H1. apply H0.
(* 1 / 6 *)
simpl.
apply typ_pi with s1 s2; trivial.
eapply H. apply H1. trivial. eapply H0. constructor; apply H1. trivial.
(* 1 / 5 *)
simpl.
apply typ_la with (B'[(S n) ← u']) s1 s2 s3; trivial.
eapply H. apply H2. trivial. eapply H0. constructor; apply H2. trivial.
eapply H1. constructor; apply H2. trivial.
(* 1 / 4 *)
simpl.
rewrite subst_travers.
replace (n+1) with (S n) by (rewrite plus_comm; trivial).
eapply typ_app. apply r. eapply H; eauto. eapply H0; eauto. eapply H1; eauto. eapply H2; eauto.
(* 1 / 3 *)
simpl. rewrite 2! subst_travers. replace (n+1) with (S n) by (rewrite plus_comm; trivial).
eapply typ_beta. apply r.
eapply H; eauto. eapply H0; eauto. eapply H1; eauto. apply red_refl_lt in H7; trivial.
eapply H2; eauto. apply red_refl_lt in H7; trivial. eapply H3; eauto.
eapply H4; eauto. eapply H5; eauto.
(* 1 / 2 *)
apply typ_red with (A[n ←u]) s. eapply H. apply H1. trivial. 
change !s with (!s[n ← u]). eapply H0. apply H1. apply red_refl_lt in H2; trivial.
(* 1 / 1 *)
apply typ_exp with (B[n ←u]) s. eapply H. apply H1. trivial. 
change !s with (!s[n ← u]). eapply H0. apply H1. apply red_refl_lt in H2. trivial.
(* reds *)
eauto.
(**)
eapply typ_reds_trans. eapply H. apply H1. apply red_refl_lt in H2. apply H2.
eapply H0; eauto.
(* wf *)
inversion H0.
(**)
inversion H1; subst; clear H1.
apply wf_from_typ in t; trivial.

eapply wf_cons. eapply H. apply H6. apply H0.
Qed.


(** Right-Hand Reflexivity: this time, is the ending part of a judgment that's always
valid.*)
Theorem red_refl_rt : forall Γ M N T, Γ ⊢ M ▹ N : T -> Γ ⊢ N ▹ N :T.
induction 1; intros.
(**)
constructor; trivial.
(**)
constructor; trivial.
(**)
apply typ_pi with s1 s2; trivial. eapply red1_in_env. apply IHtyp2. 
econstructor. apply IHtyp1. eauto.
(**)
apply typ_exp with ( Π (A'), B') s3. apply typ_la with B' s1 s2 s3; trivial.
eapply red1_in_env. apply IHtyp2. econstructor. apply IHtyp1. eauto.
apply typ_red with B s2. eapply red1_in_env. apply IHtyp3. econstructor. apply IHtyp1. eauto.
eapply red1_in_env. apply H1. econstructor. apply IHtyp1. eauto.
apply typ_pi with s1 s2; trivial.
(**)
apply typ_exp with  B' [ ← N'] s2. eapply typ_app. apply H. trivial. eapply conv1_in_env. apply IHtyp2.
eauto. econstructor. apply IHtyp1. apply typ_red with  (Π (A), B) s3. trivial. apply typ_pi with s1 s2; trivial.
apply typ_red with A s1. trivial. trivial. change !s2 with (!s2[ ←N]).
eapply subst_gen. apply H1. constructor. trivial.
(**)
apply typ_exp with B [ ← N'] s2. eapply subst_gen. apply IHtyp4. constructor. trivial.
change !s2 with (!s2[ ←N]). eapply subst_gen. apply red_refl_lt in H4; apply H4.
constructor. trivial.
(**)
apply typ_red with A s; trivial.
(**)
apply typ_exp with B s; trivial.
Qed.

Lemma reds_refl_rt : forall Γ M N T, Γ ⊢ M ▹▹ N : T -> Γ ⊢ N ▹ N :T.
induction 1. apply red_refl_rt in H; trivial.
trivial.
Qed.

(** With Left and Right reflexivity, we can finally prove that context
conversion preserves validity of context.*)
Lemma env_red1_wf : forall Γ Γ' , env_red1 Γ Γ' -> Γ ⊣  -> Γ' ⊣.
induction 1; intros. apply red_refl_rt in H. econstructor. apply H.
inversion H0; subst; clear H0. econstructor. eapply red1_in_env.
apply H2. apply wf_from_typ in H2; intuition. trivial.
Qed.

Lemma env_red_wf : forall Γ Γ' , env_red Γ Γ' -> Γ ⊣  -> Γ' ⊣.
induction 1; intros.
apply env_red1_wf with Γ; trivial. trivial. eauto.
Qed.

Lemma red_in_env : forall Γ M N T, Γ ⊢ M ▹ N : T -> forall Γ', env_red Γ Γ'-> Γ' ⊢ M ▹ N :  T.
intros. revert M N T H . induction H0; intros. 
eapply red1_in_env with Γ; trivial. apply wf_from_typ in H0. apply env_red1_wf with Γ; trivial.
trivial.
eauto.
Qed.

Lemma red_in_env_reds : forall Γ M N T, Γ ⊢ M ▹▹ N : T -> forall Γ', env_red Γ Γ'-> Γ' ⊢ M ▹▹ N :  T.
intros. revert M N T H . induction H0; intros. 
eapply red1_in_env with Γ; trivial. apply wf_from_typ_reds in H0. apply env_red1_wf with Γ; trivial.
trivial.
eauto.
Qed.


Lemma wf_from_peq : forall Γ M N , Γ ⊢ M ≡' N  -> Γ⊣.
induction 1; intuition.
apply  wf_from_typ in H; trivial.
apply  wf_from_typ in H; trivial.
Qed.

Hint Resolve wf_from_peq.

(** Every step of an equality is welltyped, by a sort, but we need to guess
it.*)
Lemma typ_peq_to_red : forall Γ A B  , Γ  ⊢ A ≡' B  ->  exists s, exists t, 
  Γ ⊢ A ▹ A : !s /\ Γ ⊢ B ▹ B : !t.
induction 1. 
exists s; exists s; split; [apply red_refl_lt with B; trivial | apply red_refl_rt with A ; trivial].
exists s; exists s; split; [apply red_refl_rt with B; trivial | apply red_refl_lt with A ; trivial].
destruct IHtyp_peq1 as (a & b & ? & ?). destruct IHtyp_peq2 as (a' & b' & ? & ?).
exists a; exists b'; intuition.
Qed.

Lemma env_conv1_wf : forall Γ Γ' , env_conv1 Γ Γ' -> Γ ⊣  -> Γ' ⊣.
induction 1; intros. apply typ_peq_to_red in H as (_ & b & _ & ?).
econstructor. apply H. inversion H0; subst; clear H0. econstructor.
eapply conv1_in_env. apply H2. trivial. apply wf_from_typ in H2; intuition.
Qed.

Lemma env_conv_wf : forall Γ Γ' , env_conv Γ Γ' -> Γ ⊣  -> Γ' ⊣.
induction 1; intros.
apply env_conv1_wf with Γ; trivial. trivial. eauto.
Qed.

(** Final Conversion in Context. *)
Theorem conv_in_env : forall Γ M N T, Γ ⊢ M ▹ N : T -> forall Γ', env_conv Γ Γ'-> Γ' ⊢ M ▹ N :  T.
intros. revert M N T H . induction H0; intros. 
apply conv1_in_env with Γ; trivial. apply wf_from_typ in H0. apply env_conv1_wf with Γ; trivial.
trivial.
eauto.
Qed.

Theorem conv_in_env_reds : forall Γ M N T, Γ ⊢ M ▹▹ N : T -> forall Γ', env_conv Γ Γ'-> Γ' ⊢ M ▹▹ N :  T.
intros. revert M N T H . induction H0; intros. 
apply conv1_in_env with Γ; trivial. apply wf_from_typ_reds in H0. apply env_conv1_wf with Γ; trivial.
trivial.
eauto.
Qed.

Lemma env_red_cons : forall a b s Γ Γ', Γ ⊢ a ▹▹ b : !s -> env_red Γ Γ' ->
  env_red (a::Γ) (b::Γ').
assert (  forall a b s Γ , Γ ⊢ a ▹▹ b : !s -> env_red (a::Γ) (b::Γ)).
intros. remember !s as S. revert s HeqS. induction H; intros; subst.
eauto. eauto.
intros. revert a b s H0.
induction H1; intros. eapply r_trans. eapply H.  apply H1.
constructor. constructor. trivial.
eapply H. apply H0.
eapply r_trans. apply IHenv_red1 with s. apply H0.
apply IHenv_red2 with s.  apply reds_refl_rt in H0.
constructor. eapply red_in_env. apply H0. trivial.
Qed.

Lemma env_conv_cons  : forall a b Γ Γ', Γ ⊢ a ≡' b -> env_conv  Γ Γ' ->
  env_conv (a::Γ) (b::Γ'). intros. revert a b H.
induction H0; intros. eapply c_trans. constructor. constructor. apply H0.
constructor. constructor. trivial.
constructor. constructor. trivial.
eapply c_trans. apply IHenv_conv1. apply H.
apply IHenv_conv2. apply typ_peq_to_red in H as (_ & t & _ & ?).
econstructor. eapply conv_in_env. apply H. trivial.
Qed.



Theorem conv_in_env_peq : forall Γ A B, Γ ⊢ A ≡' B -> forall Γ', env_conv  Γ Γ' ->
 Γ' ⊢ A ≡' B.
induction 1; intros. econstructor. eapply conv_in_env. apply H. trivial.
apply typ_peq_intro2 with s. eapply conv_in_env. apply H. trivial.
eauto.
Qed.


(** Inversion lemma: as for PTS, if a term is well typed, we can infer a lot of
  information on its type, subterms, or reduce form.*)

Lemma pgen_sort : forall Γ s N T, Γ ⊢ !s ▹ N : T -> 
  N = !s /\ ( exists t, Ax s t /\ (T = !t \/ Γ ⊢ T ≡' !t )).
intros.
remember (!s) as S. revert s HeqS. induction H; intros; subst; try discriminate.
injection HeqS; intros; subst; clear HeqS.
intuition.
exists s2; intuition.

destruct (IHtyp1 s0) as (? & t & ? & ?); trivial.
split; trivial. exists t; split; trivial. destruct H3. subst. right; eauto. right; eauto.

destruct (IHtyp1 s0) as (? & t & ? & ?); trivial.
split; trivial. exists t; split; trivial. destruct H3. subst. right; eauto. right; eauto.
Qed.


Lemma wf_item : forall Γ A n, A ↓ n ∈ Γ ->
   forall  Γ', Γ ⊣ ->  trunc (S n) Γ Γ' -> exists A', exists s, Γ' ⊢ A ▹ A' : !s.
induction 1; intros.
inversion H0; subst; clear H0.
inversion H5; subst; clear H5.
inversion H; subst.
exists A'; exists s; trivial.
inversion H1; subst; clear H1.
inversion H0; subst.
apply IHitem; trivial. apply wf_from_typ in H2; trivial.
Qed.

Lemma wf_item_lift : forall Γ t n ,Γ ⊣  -> t ↓ n ⊂ Γ ->
  exists t', exists s,  Γ ⊢ t  ▹ t' : !s.
intros.
destruct H0 as (u & ? & ?).
subst.
assert (exists Γ' , trunc (S n) Γ Γ') by (apply item_trunc with u; trivial).
destruct H0 as (Γ' & ?).
destruct (wf_item Γ u n H1 Γ' H H0) as (u' & ? & ?).
exists (u'  ↑ (S n)); exists x.
change !x with (!x ↑(S n)).
eapply thinning_n. apply H0. trivial. trivial.
Qed.

Lemma pgen_var : forall Γ x N T, Γ ⊢ #x ▹ N : T -> 
  N = #x /\ ( exists Z,  Z ↓ x  ⊂ Γ  /\   Γ ⊢ T ≡' Z ).
intros.
remember #x as X . revert x HeqX. induction H; intros; subst; try discriminate.
injection HeqX; intros; subst; clear HeqX.
intuition. exists A; intuition. apply wf_item_lift in H0. 
destruct H0 as (A' & s & ?). eauto. trivial.

destruct (IHtyp1 x) as (? & ?); trivial. 
destruct H2 as (A' & ? &?). intuition.
exists A'; intuition. eauto.

destruct (IHtyp1 x) as (? & ?); trivial. 
destruct H2 as (A' & ? &?). intuition.
exists A'; intuition. eauto. 
Qed.

Lemma pgen_pi : forall Γ A B N T ,  Γ ⊢ Π (A), B ▹ N : T -> exists A', exists B', 
  exists s1, exists s2, exists s3, Rel s1 s2 s3 /\ Γ ⊢ A ▹ A' : !s1 /\ A::Γ ⊢ B ▹ B' : !s2 /\
  N = Π (A'), B' /\ (T = !s3 \/ Γ ⊢ T ≡' !s3 ).
intros.
remember (Π(A),B) as P. revert A B HeqP. induction H; intros; subst; try discriminate.
injection HeqP ; intros; subst; clear HeqP.
clear IHtyp1 IHtyp2.
exists A'; exists B'; exists s1; exists s2; exists s3; intuition.

destruct (IHtyp1 A0 B0) as (A' & B'& s1 & s2 & s3 & h); trivial.
decompose [and] h; clear h IHtyp1.
exists A'; exists B'; exists s1; exists s2; exists s3; repeat split; trivial.
destruct H6. subst; right; eauto. right; eauto. 

destruct (IHtyp1 A0 B0) as (A' & B'& s1 & s2 & s3 & h); trivial.
decompose [and] h; clear h IHtyp1.
exists A'; exists B'; exists s1; exists s2; exists s3; repeat split; trivial.
destruct H6. subst; right; eauto. right; eauto.
Qed.


Lemma pgen_la : forall  Γ A M N T,  Γ  ⊢ λ[A],M ▹ N : T -> exists A',exists M', exists B, exists B', 
 exists s1, exists s2, exists s3, Rel s1 s2 s3 /\ Γ  ⊢ A ▹ A' : !s1 /\ A::Γ  ⊢ M ▹ M' : B /\
  A::Γ  ⊢ B ▹ B' :!s2 /\ N = λ[A'],M' /\ (Γ  ⊢ Π (A), B ≡' T ).
intros.
remember (λ[A],M) as L. revert A M HeqL. induction H; intros; subst; try discriminate.
injection HeqL; intros; subst;  clear HeqL.
exists A'; exists M'; exists B; exists B'; exists s1; exists s2; exists s3; intuition.
econstructor. econstructor. apply H. apply red_refl_lt with A'; trivial. apply red_refl_lt with B'; trivial.

destruct (IHtyp1 A0 M0) as (A' & M' & K & K' &s1 & s2 & s3 & h); trivial.
decompose [and] h; clear IHtyp1 h.
exists A'; exists M'; exists K; exists K'; exists s1; exists s2; exists s3; intuition.
eauto. 


destruct (IHtyp1 A0 M0) as (A' & M' & K & K' &s1 & s2 & s3 & h); trivial.
decompose [and] h; clear IHtyp1 h.
exists A'; exists M'; exists K; exists K'; exists s1; exists s2; exists s3; intuition.
eauto.
Qed.

Lemma pgen_app : forall Γ W P V X Y Z , Γ ⊢ (W ·(P,V) X) ▹ Y : Z -> exists U, exists U', exists V',
 exists X', exists s1, exists s2, exists s3, Rel s1 s2 s3 /\ Γ ⊢ U ▹ U' : !s1 /\ 
 U::Γ ⊢ V ▹ V' : !s2  /\ Γ ⊢ X ▹ X' : U /\ Γ  ⊢ V[← X] ≡' Z   /\
(  (exists W', Γ ⊢ W ▹ W' : Π(U),V /\ P = U /\ Y = W' ·(U',V') X' ) \/
   (exists K0, exists K, exists K', exists T, exists T', P = K /\ W = λ[U],T /\ U::Γ ⊢ T ▹ T' : V /\ Y = T'[←X'] /\
  Γ ⊢ K0 ▹▹ K : !s1 /\ Γ ⊢ K0 ▹▹ U : !s1 /\ Γ ⊢ K ▹ K' : !s1 )).
intros.
remember (App W P V X ) as APP. revert W V P X HeqAPP. induction H; intros; subst; try discriminate.
injection HeqAPP; intros; subst; clear HeqAPP. clear IHtyp4 IHtyp3 IHtyp2 IHtyp1.
exists P; exists A'; exists B'; exists N'; exists s1; exists s2; exists s3; intuition.
apply typ_peq_intro with s2. apply red_refl_lt with B'[← N'].
change !s2 with (!s2[←X]). eapply subst_gen. apply H1. constructor. trivial. eauto.

injection HeqAPP; intros; subst; clear HeqAPP. clear IHtyp4 IHtyp3 IHtyp2 IHtyp1 IHtyp5.
exists A; exists A'; exists B'; exists N'; exists s1; exists s2; exists s3; intuition.
apply typ_peq_intro with s2. apply red_refl_lt with B'[← N']. change !s2 with (!s2[←X]). eapply subst_gen. apply H4. constructor. trivial.
right. exists A0; exists P; exists A'''; exists M; exists M'; intuition.


destruct (IHtyp1 W V P X) as (U & U' &   V' & X' & s1 &s2 &s3  & h); trivial.  decompose [and] h; clear h.
exists U; exists U';  exists V'; exists X'; exists s1; exists s2; exists s3; intuition. eauto. eauto.

destruct (IHtyp1 W V P X) as (U & U' & V' & X' & s1 &s2 &s3  & h); trivial. decompose [and] h; clear h.
exists U; exists U';  exists V'; exists X'; exists s1; exists s2; exists s3; intuition. eauto. eauto.
Qed.


Lemma fun_item_lift : forall A A' v Γ , A ↓ v ⊂ Γ -> A' ↓ v ⊂ Γ -> A = A'.
intros.
destruct H as (x & ?& ?). destruct H0 as (x' & ?& ?).
subst. replace x' with x. trivial. eapply fun_item. apply H1. apply H2.
Qed.

(** Correctness of typing.*)
Lemma typ_wf : forall Γ M N A , Γ ⊢ M ▹ N : A  -> (exists s, A = !s) \/ (exists s, Γ ⊢ A ▹ A : !s).
induction 1; intros.
destruct (wf_item_lift   Γ A x H H0) as (A' & s & ?).
right. exists s; apply red_refl_lt with A'; trivial.
(**)
left; exists s2; trivial.
(**)
left; exists s3; trivial.
(**)
right. exists s3. apply typ_pi with s1 s2. trivial.
apply red_refl_lt with A'; trivial. apply red_refl_lt with B'; trivial.
(**)
right. exists s2. change !s2 with (!s2  [ ← N]).
eapply subst_gen. apply red_refl_lt with B'; apply H1. constructor. apply red_refl_lt with N'; trivial.
(**)
right. exists s2. change !s2 with (!s2  [ ← N]).
eapply subst_gen. apply red_refl_lt with B'; apply H4. constructor. apply red_refl_lt with N'; trivial.
(**)
right. exists s. apply red_refl_rt with A; trivial.
(**)
right. exists s. apply red_refl_lt with B; trivial.
Qed.


(** Type Exchange: this property is critic. We need it to simulate a reduction
we know valid in another of it's type. We will use it to reannotate some type
reductions in the correct sorts, in order to be allowed by [Rel] to build
Pi-types.*)
Theorem relocate : forall Γ M N A , Γ ⊢ M ▹ N : A  -> forall P B,  Γ ⊢ M ▹ P : B ->  Γ ⊢ M ▹ N : B /\ Γ ⊢ M ▹ P : A.
induction 1; intros.
(**)
apply pgen_var in H1. destruct H1 as (-> & A' & ? &  ?).
replace A' with A in *. split.
apply typ_pcompat with A ; intuition.
constructor; trivial.
eapply fun_item_lift. apply H0. trivial.
(**)
apply pgen_sort in H1. destruct H1 as (-> & t & ? & ?). destruct H2. subst. intuition.
intuition.
apply typ_pcompat with !t ;intuition.
(**)
apply pgen_pi in H2. destruct H2 as (A'' & B'' & t1 & t2 & t3 & h).
decompose [and] h; clear h. subst.
destruct (IHtyp1 A'' !t1 H4) as ( ? & ?). clear IHtyp1.
destruct (IHtyp2 B'' !t2 H3) as ( ? & ?). clear IHtyp2.
destruct H7. subst. eauto.
split. 
apply typ_pcompat with !t3 ;intuition. apply typ_pi with t1 t2; trivial.
apply typ_pi with s1 s2; trivial.
(**)
apply pgen_la in H3. destruct H3 as (A'' & M'' & K & K' & t1 & t2 & t3 & h).
decompose [and] h; clear h. subst.
destruct (IHtyp1 A'' !t1 H5) as (? & ?); clear IHtyp1.
clear IHtyp2.
destruct (IHtyp3 M'' K H4) as (? & ?); clear IHtyp3.
split. apply typ_pcompat with (Π (A), K) ; intuition.
apply typ_la with K' t1 t2 t3; trivial. apply typ_la with B' s1 s2 s3; trivial.
(**)
apply pgen_app in H4 as (U & U' & B'' &  N'' & t1 & t2 & t3 & h). decompose [and] h; clear h.
destruct (IHtyp4 N'' U H7) as ( ? & ?); clear IHtyp4. destruct H10.
destruct H10 as (M'' & ? & ? & ->). subst. destruct (IHtyp3 M'' (Π (U), B) H10) as (? & ?); clear IHtyp3. split.
apply typ_pcompat with B [ ← N] ;intuition. eapply typ_app. apply H. trivial. trivial. trivial. trivial.
eapply typ_app. apply H4. trivial. trivial. trivial. trivial.

destruct H10 as (K0 & K & K' & T & T' & ? & -> & ? & -> & ? & ? & ?). subst. split.
apply typ_pcompat with B [ ← N];intuition.  eapply typ_app. apply H. trivial. trivial. trivial. trivial.
eapply typ_beta. apply H4. apply H6. apply H15. apply H14. trivial. apply H5. trivial. trivial.
(**)
apply pgen_app in H7  as (U & U' &  D' & N'' & t1 & t2 & t3 & h). decompose [and] h; clear h.
destruct (IHtyp5 N'' U H10) as ( ? & ?); clear IHtyp5. destruct H13. destruct H13 as (L & ? & ? & ->). subst.
apply pgen_la in H13 as (A'' & M'' & K & K' & u1 & u2 & u3 & h). decompose [and] h; clear h. subst.
destruct (IHtyp1 A'' !u1 H16) as (? & ?); clear IHtyp1. clear IHtyp2.
destruct (IHtyp4 M'' K H15) as (? & ?); clear IHtyp4. split. apply typ_pcompat with B [ ← N] ;intuition.
eapply typ_beta. apply H. apply H0. apply reds_refl_rt in H3; apply H3. apply H2. trivial. apply H4. trivial. trivial.
eapply typ_app. apply H7. trivial. trivial. apply typ_pcompat with  ( Π (A), K ) ; intuition.
apply typ_la with K' u1 u2 u3; trivial. trivial.

destruct H13 as (U0 & K & K' & T & T' & ? & ? & ? & ->  & ? & ?& ?). injection H15; intros; subst; clear H15.
clear IHtyp1. destruct (IHtyp2 K' !t1 H19) as (? & ?); clear IHtyp2. split.
apply typ_pcompat with (B [ ← N]); intuition.
eapply typ_beta. apply H. apply H0. apply H1. apply H2. trivial. apply H4. trivial. trivial.
eapply typ_beta. apply H. apply H0. apply H1. apply H2. trivial. apply H4. trivial. trivial.
(**)
destruct (IHtyp1 P B0 H1) as (? & ?); clear IHtyp1.
split. eauto. eauto.
(**)
destruct (IHtyp1 P B0 H1) as (? & ?); clear IHtyp1.
split. eauto. eauto.
Qed.

(** Facts abouts Reds*)
Lemma typ_reds_trans_ : forall Γ M N T, Γ ⊢ M ▹▹ N : T  -> forall P T', Γ ⊢ N ▹ P : T' -> Γ ⊢ M ▹▹ P : T.
induction 1; intros.
apply typ_reds_trans with t. intuition. destruct (relocate Γ t P T' H0 t T). apply red_refl_rt in H; trivial.
intuition. eauto.
Qed.

Lemma typ_reds_trans2 : forall Γ M N T, Γ ⊢ M ▹▹ N : T  -> forall P T', Γ ⊢ N ▹▹ P : T' -> Γ ⊢ M ▹▹ P : T.
intros. revert M T H. induction H0; intros.
apply typ_reds_trans_ with s T; trivial.
eauto.
Qed.


Hint Resolve typ_reds_trans2.


Lemma typ_reds_relocate : forall Γ M N T, Γ ⊢ M ▹▹ N : T  -> forall P T', Γ ⊢ M ▹ P : T' -> Γ ⊢ M ▹▹ N : T'.
induction 1; intros. constructor. eapply relocate. apply H0. apply H.
eauto.
Qed.

Lemma reds_typ_pcompat : forall Γ M N A , Γ ⊢ M ▹▹ N : A -> forall B , Γ ⊢ A ≡' B  -> Γ ⊢ M ▹▹ N : B.
induction 1; intros. constructor. apply typ_pcompat with T; trivial.
eauto.
Qed.


(** Another version of inversion lemmas: for multi-step reduction.*)
Lemma Pi_Reds : forall Γ A B N T, Γ ⊢ Π(A),B ▹▹ N : T -> exists A', exists B', exists s1, exists s2, exists s3, 
  Rel s1 s2 s3 /\ N = Π(A'),B' /\ Γ ⊢ A ▹▹ A' : !s1 /\ A::Γ ⊢ B ▹▹ B' : !s2 /\ (T = !s3 \/ Γ ⊢ T ≡' !s3).
intros until 1. remember (Pi A B) as P. revert A B HeqP. induction H; intros; subst.
apply pgen_pi in H. destruct H as (A' & B' & s & tt & u & h). decompose [and] h; clear h.
exists A'; exists B'; exists s; exists tt; exists u; intuition.
destruct (IHtyp_reds1 A B) as (A1 & B1 & s1 & t1 & u1 & ? &  -> & ? & ? & ?). trivial. clear IHtyp_reds1.
destruct (IHtyp_reds2 A1 B1) as (A2 & B2 & s2 & t2 & u2 & ? & -> & ? & ? & ?). trivial.
exists A2; exists B2; exists s1; exists t1; exists u1; repeat split. trivial.
eapply typ_reds_trans2. apply H2. apply H6.  eapply typ_reds_trans2. apply H3.
eapply conv_in_env_reds. apply H7. apply c_sym. apply env_red_to_conv. apply env_red_cons with s1; trivial.
trivial.
Qed.

Lemma La_Reds : forall Γ A b N T, Γ ⊢ λ[A],b ▹▹ N : T -> exists A', exists b', exists D, exists D',  exists s1, exists s2, exists s3, 
  Rel s1 s2 s3 /\ N = λ[A'],b' /\ Γ ⊢ A ▹▹ A' : !s1 /\ A::Γ ⊢ b ▹▹ b' : D /\ A::Γ ⊢ D ▹▹ D' : !s2 /\ Γ ⊢ T ≡' Π(A),D.
intros until 1. remember (La A b) as P. revert A b HeqP. induction H; intros; subst.
apply pgen_la in H. destruct H as (A' & b' & D & D' &  s & tt & u & h). decompose [and] h; clear h.
exists A'; exists b'; exists D; exists D'; exists s; exists tt; exists u; intuition.
destruct (IHtyp_reds1 A b) as (A1 & b1 & D1 & D'1 & s1 & t1 & u1 & ? &  -> & ? & ? &  ?  &?). trivial. clear IHtyp_reds1.
destruct (IHtyp_reds2 A1 b1) as (A2 & b2 & D2 & D'2 & s2 & t2 & u2 & ? & -> & ? & ? & ? & ?). trivial.
exists A2; exists b2; exists D1; exists D'1; exists s1; exists t1; exists u1; repeat split. trivial.
eapply typ_reds_trans2. apply H2. apply H7.  eapply typ_reds_trans2. apply H3.
eapply conv_in_env_reds. apply H8. apply c_sym. apply env_red_to_conv. apply env_red_cons with s1; trivial. trivial.
trivial.
Qed.

Lemma Sort_Reds : forall Γ s P T, Γ ⊢ !s ▹▹ P : T -> P = !s /\ exists t, Ax s t /\ (T = !t \/ ( Γ ⊢ T ≡' !t)).
intros. remember !s as S. revert s HeqS. induction H; intros; subst.
apply pgen_sort in H. intuition.
destruct (IHtyp_reds1 s0) as (? & s1 & ? & ?); trivial.
destruct (IHtyp_reds2 s0) as (? & s2 & ?& ?); trivial.
split. transitivity t. trivial. trivial.
exists  s2; split; trivial.
Qed.

(* begin hide *)
Lemma typ_ind2 : 
forall P : Env -> Term -> Term -> Term -> Prop,
       (forall (Γ : Env) (x : nat) (A : Term),
        Γ ⊣ -> A ↓ x ⊂ Γ -> P Γ #x #x A) ->
       (forall (Γ : Env) (s1 s2 : Sorts), Ax s1 s2 -> Γ ⊣ -> P Γ !s1 !s1 !s2) ->
       (forall (Γ : Env) (s1 s2 s3 : Sorts) (A A' B B' : Term),
        Rel s1 s2 s3 ->
        Γ ⊢ A ▹ A' : !s1 ->
        P Γ A A' !s1 ->
        A :: Γ ⊢ B ▹ B' : !s2 ->
        P (A :: Γ) B B' !s2 -> P Γ (Π (A), B) (Π (A'), B') !s3) ->
       (forall (Γ : Env) (A A' B B' M M' : Term) (s1 s2 s3 : Sorts),
        Rel s1 s2 s3 ->
        Γ ⊢ A ▹ A' : !s1 ->
        P Γ A A' !s1 ->
        A :: Γ ⊢ B ▹ B' : !s2 ->
        P (A :: Γ) B B' !s2 ->
        A :: Γ ⊢ M ▹ M' : B ->
        P (A :: Γ) M M' B -> P Γ (λ [A], M) (λ [A'], M') (Π (A), B)) ->
       (forall (Γ : Env) (M M' N N' A A' B B' : Term) (s1 s2 s3 : Sorts),
        Rel s1 s2 s3 ->
        Γ ⊢ A ▹ A' : !s1 ->
        P Γ A A' !s1 ->
        A :: Γ ⊢ B ▹ B' : !s2 ->
        P (A :: Γ) B B' !s2 ->
        Γ ⊢ M ▹ M' : Π (A), B -> P Γ M M' (Π (A), B) ->
        (forall AA MM, M = La AA MM -> exists MM',exists AA', exists BB, M' = La AA' MM' /\
            AA :: Γ ⊢ MM ▹ MM' : BB /\ P (AA :: Γ) MM MM' BB )
        ->
        Γ ⊢ N ▹ N' : A -> P Γ N N' A -> P Γ (M ·(A, B)N) (M' ·(A', B')N') B [ ← N]) ->
       (forall (Γ : Env) (M M' N N' A A' A'' A''' A0 B B' : Term)
          (s1 s2 s3 : Sorts),
        Rel s1 s2 s3 ->
        Γ ⊢ A ▹ A' : !s1 ->
        P Γ A A' !s1 ->
        Γ ⊢ A'' ▹ A''' : !s1 ->
        P Γ A'' A''' !s1 ->
        Γ ⊢ A0 ▹▹ A : !s1 ->
        Γ ⊢ A0 ▹▹ A'' : !s1 ->
        A :: Γ ⊢ B ▹ B' : !s2 ->
        P (A :: Γ) B B' !s2 ->
        A :: Γ ⊢ M ▹ M' : B ->
        P (A :: Γ) M M' B ->
        Γ ⊢ N ▹ N' : A ->
        P Γ N N' A -> P Γ ((λ [A], M) ·( A'', B)N) M' [ ← N'] B [ ← N]) ->
       (forall (Γ : Env) (M N A B : Term) (s : Sorts),
        Γ ⊢ M ▹ N : A ->
        P Γ M N A -> Γ ⊢ A ▹ B : !s -> P Γ A B !s -> P Γ M N B) ->
       (forall (Γ : Env) (M N A B : Term) (s : Sorts),
        Γ ⊢ M ▹ N : B ->
        P Γ M N B -> Γ ⊢ A ▹ B : !s -> P Γ A B !s -> P Γ M N A) ->
       forall (e : Env) (t t0 t1 : Term), e ⊢ t ▹ t0 : t1 -> P e t t0 t1.
intros P Cvar Csort CPi CLa CApp CBeta CRed CExp.
fix 5.
destruct 1.
apply Cvar; trivial.
apply Csort; trivial.
eapply CPi. apply H. trivial. apply typ_ind2. trivial. trivial. apply typ_ind2. trivial.
eapply CLa. apply H. trivial. apply typ_ind2. trivial. apply H1. apply typ_ind2. trivial. trivial. apply typ_ind2. trivial.
(**)
eapply CApp. apply H. apply H0. apply typ_ind2; trivial. apply H1. apply typ_ind2; trivial. trivial. apply typ_ind2; trivial.
elim H2; intros; try discriminate. exists M'0; exists A'0; exists B0; split. trivial. split.
replace AA with A0. replace MM with M0.  trivial. injection H11; intros; subst; trivial. 
injection H11; intros; subst; trivial. replace MM with M0. replace AA with A0. apply typ_ind2.
trivial. injection H11; intros; subst; trivial. injection H11; intros; subst; trivial.  apply H5; trivial. apply H5;trivial.
trivial. apply typ_ind2; trivial.
(**)
eapply CBeta. apply H. apply H0. apply typ_ind2; trivial. apply H1. apply typ_ind2; trivial. 
apply H2. trivial. apply H4. apply typ_ind2; trivial. trivial. apply typ_ind2; trivial. trivial. apply typ_ind2; trivial.
(**)
eapply CRed. apply H. apply typ_ind2; trivial. apply H0. apply typ_ind2; trivial.
eapply CExp. apply H. apply typ_ind2; trivial. apply H0. apply typ_ind2; trivial.
Qed.
(* end hide *)

(** Diamond Property: PTS_{atr} is like [Betap], it enjoys the diamond property.
  This is where half the magic happens (and mainly where the new annotation is
  needed.*)
Theorem OSDiamond  : forall Γ M N A , Γ ⊢ M ▹ N : A  -> forall P B,  Γ ⊢ M ▹ P : B -> 
  exists Q, Γ ⊢ N ▹ Q : A /\ Γ ⊢ N ▹ Q : B /\ Γ ⊢ P ▹ Q: A /\ Γ ⊢ P ▹ Q : B.
induction 1 using typ_ind2; intros.
apply pgen_var in H1. destruct H1 as ( -> & A' & ? & ?).
replace A' with A in *. exists #x; intuition.
apply typ_pcompat with A; intuition. apply typ_pcompat with A; intuition.
eapply fun_item_lift . apply H0. trivial.
(**)
apply pgen_sort in H1. destruct H1 as (-> & t & ? & ?).
destruct H2; subst; exists !s1; intuition. apply typ_pcompat with !t; intuition. apply typ_pcompat with !t; intuition.
(**)
apply pgen_pi in H2. destruct H2 as (A'' & B'' & t1 & t2 & t3 & h). decompose [and] h; clear h.
subst. destruct (IHtyp1 A'' !t1 H4) as ( QA & ? & ? & ?& ?).
destruct (IHtyp2 B'' !t2 H3) as (QB & ? & ? & ? & ?). exists (Pi QA QB); repeat split.
econstructor. apply H. trivial. eapply conv_in_env. apply H10. eauto.
destruct H7. subst. econstructor. apply H2. trivial. eapply conv_in_env. apply H11. eauto.
apply typ_pcompat with !t3; intuition. econstructor. apply H2. trivial. 
eapply conv_in_env. apply H11. eauto.
econstructor. apply H. trivial. eapply conv_in_env. apply H12. eauto.
destruct H7. subst. econstructor. apply H2. trivial. eapply conv_in_env. apply H13. eauto.
apply typ_pcompat with !t3; intuition. econstructor. apply H2. trivial. eapply conv_in_env. apply H13. eauto.
(**)
apply pgen_la in H3. destruct H3 as (A'' & M'' & D & D' & t1 & t2 & t3 & h).
decompose [and] h; clear h. subst. destruct (IHtyp1 A'' !t1 H5) as (QA & ? & ?& ?& ?).
destruct (IHtyp3 M'' D H4) as (QM & ? & ? & ?& ?). exists (La QA QM); intuition.
eapply typ_exp with (Pi A' B) s3. econstructor. apply H. trivial.
eapply conv_in_env. apply H1. eauto. eapply conv_in_env. apply H12. eauto.
econstructor. apply H. trivial. apply red_refl_lt in H1. trivial.
apply typ_pcompat with (Pi A D); trivial. apply typ_exp with (Pi A' D) t3. 
econstructor. apply H3. trivial. eapply conv_in_env. apply H6. eauto. 
eauto. eapply conv_in_env. apply H13. eauto. econstructor. apply H3. eapply relocate. apply H5. apply H0. apply red_refl_lt in H6; trivial.
eapply typ_exp with (Pi A'' B) s3. econstructor. apply H. trivial.
eapply conv_in_env. apply H1. eauto. eapply conv_in_env.  apply H14.  eauto. 
econstructor. apply H. eapply relocate. apply H0. apply H5. apply red_refl_lt in H1. trivial.
apply typ_pcompat with (Pi A D); trivial. apply typ_exp with (Pi A'' D) t3. 
econstructor. apply H3. trivial. eapply conv_in_env.  apply H6. eauto.
eapply conv_in_env. apply H15. eauto. econstructor. apply H3. trivial. apply red_refl_lt in H6; trivial.
(**)
apply pgen_app in H5 as (C & C' &  D'  & N'' & t1 & t2 & t3 & h). decompose [and] h; clear h.
destruct (IHtyp4 N'' C H8) as (QN & ?& ? &? & ?). clear IHtyp4.  destruct H11.
destruct H11 as (M'' & ? & ? & -> ). subst.
destruct (IHtyp2 D' !t2) as (QB & ? & ?& ?& ?). trivial. clear IHtyp2.
destruct (IHtyp3 M'' (Pi C B) H11) as (QM & ?& ? & ? & ?). clear IHtyp3.
destruct (IHtyp1 C' !t1 H7) as (QC & ? & ?& ? & ?). 
exists (App QM QC QB QN); intuition. 
apply typ_exp with (B' [← N']) s2. econstructor. apply H. trivial.
eapply conv_in_env. apply H15. eauto. apply typ_red with (Pi C B) s3. trivial. econstructor.
apply H. trivial. trivial. apply typ_pcompat with C; trivial. eauto.
change !s2 with (!s2 [ ← N ]). eapply subst_gen. apply H1. constructor. trivial.
apply typ_pcompat with (B [← N]); trivial. 
apply typ_exp with (B' [← N']) s2. econstructor. apply H. trivial.  eapply conv_in_env. apply H15. eauto.
apply typ_red with (Pi C B) s3. trivial. econstructor. apply H. trivial. trivial. apply typ_pcompat with C; trivial. eauto.
change !s2 with (!s2 [ ← N ]). eapply subst_gen. apply H1. constructor. trivial.
apply typ_exp with (D' [← N'']) t2. econstructor. apply H5. trivial. eapply conv_in_env. apply H18. eauto.
apply typ_red with (Pi C B) t3. trivial. econstructor. apply H5. trivial. trivial. apply typ_pcompat with C; eauto.
change !t2 with (!t2 [ ← N ]). eapply subst_gen. apply H6. constructor. trivial.
apply typ_pcompat with (B [← N]); trivial.
apply typ_exp with (D' [← N'']) t2. econstructor. apply H5. trivial. eapply conv_in_env.  apply H18.  eauto. 
apply typ_red with (Pi C B) t3. trivial. econstructor. apply H5. trivial. trivial. apply typ_pcompat with C; eauto.
change !t2 with (!t2 [ ← N ]). eapply subst_gen. apply H6. constructor. trivial.

destruct H11 as (C0 & K & K' & T & T' & ? & -> & ? &  ->  & ? & ? & ?). subst. 
apply pgen_la in H2 as (C'' & T'' & F & F' & u1 & u2 & u3 & h). decompose [and] h; clear h. subst.
destruct (H3 C T) as (MM & AA' & BB & h); trivial. decompose [and] h; clear h.
injection H21; intros; subst; clear H21. clear H3. destruct (H25 T' B H15) as (QMM &? & ? & ? & ?). clear H25.
assert( Γ ⊢ AA' ▹ AA' : !t1). destruct (relocate Γ  C C' !t1 H7 AA' !u1 H19). apply red_refl_rt in H27; trivial. 
assert( Γ ⊢ A' ▹ A' : !t1). destruct (relocate Γ  K K' !t1 H18 A' !s1 H0). apply red_refl_rt in H28; trivial. 
assert (AA' :: Γ ⊢ B' ▹ B' : !t2). destruct (relocate (C :: Γ)  B D' !t2 H6 B' !s2) as (? & ? ). eapply conv_in_env.
eauto. apply c_trans with (C0::Γ). eauto. eauto. eapply conv_in_env with (C::Γ). apply red_refl_rt in H29; trivial. eauto.
exists ( QMM [ ←  QN]); repeat split.
apply typ_exp with (B' [← N']) s2. econstructor. apply H5. apply H25. apply H27.
eapply typ_reds_trans2. apply H17. eauto. eauto. apply H28. 
apply typ_pcompat with B. eapply conv_in_env.  apply H21. eauto. eapply conv_in_env_peq.
econstructor. apply H1. apply c_trans with (C0::Γ). eauto. apply c_trans with (C::Γ). eauto. eauto. apply typ_pcompat with C. trivial.
eauto. change !s2 with (!s2 [ ← N ]). eapply subst_gen. apply H1. constructor. trivial.
apply typ_pcompat with (B [← N]); trivial. apply typ_pcompat with (B'[← N']).
econstructor. apply H5. apply H25. apply H27. eapply typ_reds_trans2. apply H17. eauto. eauto. apply H28.
apply typ_pcompat with B. eapply conv_in_env. apply H21. eauto. eapply conv_in_env_peq. econstructor.
apply H1.  apply c_trans with (C0::Γ). eauto. apply c_trans with (C::Γ). eauto. eauto. apply typ_pcompat with C. trivial.
eauto. apply typ_peq_intro2 with s2.  change !s2 with (!s2 [ ← N ]). eapply subst_gen. apply H1. constructor. trivial.
apply typ_pcompat with (B [← N'']).  eapply subst_gen. apply H26. constructor. trivial.
apply typ_peq_intro2 with s2. change !s2 with (!s2 [ ← N ]). eapply subst_gen. apply red_refl_lt in H1; apply H1. constructor. apply typ_pcompat with C; eauto.
apply typ_pcompat with (B [← N]); trivial. apply typ_pcompat with (B [← N'']).  eapply subst_gen. apply H26. constructor. trivial.
apply typ_peq_intro2 with s2. change !s2 with (!s2 [ ← N ]). eapply subst_gen. apply red_refl_lt in H1; apply H1. constructor. apply typ_pcompat with C; eauto.
(**)
apply pgen_app in H7 as (C & C' &  D' & N'' & t1 & t2 & t3 & h). decompose [and] h; clear h.
destruct (IHtyp5 N'' C H10) as (QN & ?& ? &? & ?). clear IHtyp5.
destruct H13. destruct H13 as (LM & ? & ? &  ->). subst.
apply pgen_la in H13 as (A'' & M'' & F & F' & u1 & u2 & u3 & h). decompose [and] h; clear h. subst.
destruct (IHtyp4 M'' F H17) as (QM & ? & ? & ? & ?). clear IHtyp4.
assert (Γ ⊢ A ≡' C). apply reds_to_conv in H3. apply reds_to_conv in H2. eauto.
assert( Γ ⊢ A'' ▹ A'' : !s1). destruct (relocate Γ  A A' !s1 H0 A'' !u1 H18). apply red_refl_rt in H27; trivial.
assert( Γ ⊢ C' ▹ C' : !s1). destruct (relocate Γ  C A''' !s1 H1 C' !t1 H9). apply red_refl_rt in H28; trivial.
assert( A''::Γ ⊢ D' ▹ D' : !s2). destruct (relocate (C::Γ) B D'!t2 H8 B' !s2 ).
eapply conv_in_env. apply H4. eauto. eapply conv_in_env. apply red_refl_rt in H28; apply H28. apply c_trans with (A:: Γ ). eauto. eauto.
exists (QM [ ← QN]); intuition.
apply typ_exp with (B [← N']) s2. eapply subst_gen. apply H20. constructor. trivial.
change !s2 with (!s2 [ ← N ]). eapply subst_gen. apply red_refl_lt in H4; apply H4. constructor. trivial.
apply typ_pcompat with (B[ ← N]); trivial.  apply typ_exp with (B [← N']) s2. eapply subst_gen. apply H20.
constructor. trivial. change !s2 with (!s2 [ ← N ]). eapply subst_gen. apply red_refl_lt in H4; apply H4. constructor. trivial.
apply typ_exp with (D' [← N'']) t2.   econstructor. apply H. apply H26. apply H27. eapply typ_reds_trans2. apply H2. eauto.
eauto. apply H28. apply typ_pcompat with B. eapply conv_in_env. apply H23. eauto. eapply conv_in_env_peq.
eauto. apply c_trans with (A::Γ). eauto. eauto. apply typ_pcompat with A; trivial. eauto. 
change !t2 with (!t2 [ ← N ]). eapply subst_gen. apply H8. constructor. trivial.
apply typ_pcompat with (B [← N]); trivial. apply typ_exp with (D' [← N'']) t2. econstructor. apply H.  apply H26. apply H27.
eapply typ_reds_trans2. apply H2. eauto. eauto. apply H28. apply typ_pcompat with B. eapply conv_in_env. apply H23. apply c_trans with (A::Γ); eauto.
eapply conv_in_env_peq. eauto. apply c_trans with (A::Γ); eauto. apply typ_pcompat with A; trivial. eauto. 
change !t2 with (!t2 [ ← N ]). eapply subst_gen. apply H8. constructor. trivial.
                                  (* beta / beta, fight ! *)
destruct H13 as (C0 & K & K' & T & T' & ? & ? & ? & -> & ? & ? & ?). injection H17; intros; subst; clear H17.
destruct (IHtyp4 T' B H18) as (QM & ? & ? & ? & ?). clear IHtyp4.
exists (QM  [ ← QN]); intuition. 
apply typ_exp with (B [← N']) s2. eapply subst_gen. apply H13. constructor. trivial.
change !s2 with (!s2 [←  N]). eapply subst_gen. apply red_refl_lt in H4; apply H4. constructor. trivial.
apply typ_pcompat with (B[←  N]); trivial. apply typ_exp with (B[← N']) s2.
eapply subst_gen. apply H13. constructor. trivial.
change !s2 with (!s2 [←  N]). eapply subst_gen. apply red_refl_lt in H4; apply H4. constructor. trivial.
apply typ_exp with (B [← N'']) t2. eapply subst_gen. apply H22. constructor. trivial.
change !t2 with (!t2 [←  N]). eapply subst_gen. apply red_refl_lt in H8; apply H8. constructor. trivial.
apply typ_pcompat with (B[←  N]); trivial. apply typ_exp with (B[← N'']) t2.
eapply subst_gen. apply H22. constructor. trivial.
change !t2 with (!t2 [←  N]). eapply subst_gen. apply red_refl_lt in H8; apply H8. constructor. trivial.
(** YOUHHHHOU **)
destruct (IHtyp1 P B0 H1) as (Z & ? & ? & ? & ?).
exists Z; split; eauto.
(**)
destruct (IHtyp1 P B0 H1) as (Z & ? & ? & ? & ?).
exists Z; split; eauto.
Qed.


Lemma SubDiam : forall Γ M N A, Γ ⊢ M ▹ N : A   -> forall P B,  Γ ⊢ M ▹▹ P : B -> exists Q, Γ ⊢ N ▹▹ Q : A /\  Γ ⊢ P ▹ Q : B.
intros. revert N A H. induction H0; intros.
destruct (OSDiamond Γ s t T H N A H0) as (w & ? & ? & ? & ?).
exists w; split; eauto.
destruct (IHtyp_reds1 N A H) as (w1 &? & ?).
destruct (IHtyp_reds2 w1 T H1) as (w2 & ? & ?).
exists w2; split; eauto.
Qed.


Lemma ChurchRosser: forall Γ M N A , Γ ⊢ M ▹▹ N : A  -> forall P B,  Γ ⊢ M ▹▹ P : B -> exists Q, Γ ⊢ N ▹▹ Q : A /\  Γ ⊢ P ▹▹ Q: B.
induction 1; intros.
destruct (SubDiam Γ s t T H P B H0) as (w & ? & ?).
exists w; split; eauto.
destruct (IHtyp_reds1 P B H1) as (Q & ? & ?).
destruct (IHtyp_reds2 Q T H2) as (R & ? & ?).
exists R; split; eauto.
Qed.


Theorem Confluence : forall Γ A B,  Γ ⊢ A ≡' B -> exists Q,exists s, exists t,   Γ  ⊢ A ▹▹ Q : !s /\ Γ  ⊢ B ▹▹ Q : !t.
induction 1; intros.
exists B; exists s; exists s; intuition. apply red_refl_rt in H; intuition.
exists A; exists s; exists s; intuition. apply red_refl_rt in H; intuition.
destruct IHtyp_peq1 as (Q & q & q' & ? & ?). destruct IHtyp_peq2 as (Q1 & q1 & q'1 & ?& ?).
destruct (ChurchRosser Γ B Q1 !q1 H3 Q !q' H2) as (z &? & ?).
exists z; exists q; exists q'1; split; eauto.
Qed.

(** The holy graal: Weak Pi Injectivity is the key property to prove Typed
SubjectReduction and the equivalence between PTS and PTSe.*)
Theorem PiInj : forall Γ A B C D , Γ ⊢ Π(A),B ≡' Π(C),D ->   Γ ⊢ A ≡' C /\ A::Γ ⊢ B ≡' D.
intros. apply Confluence in H. destruct H  as (P & s & t & ? & ?) .
apply Pi_Reds in H as (A1 & B1 & s1 & t1 & u1 & ? & -> & ? & ? & ?).
apply Pi_Reds in H0 as (A2 & B2 & s2 & t2 & u2 & ? & ? & ? & ? & ?).
injection H4; intros; subst; clear H4.
split. apply typ_peq_trans with A2. apply reds_to_conv in H1; trivial. apply reds_to_conv in H5; intuition.
apply typ_peq_trans with B2. apply reds_to_conv in H2; trivial.  apply reds_to_conv in H6. eapply conv_in_env_peq.
apply typ_peq_sym. apply H6. apply reds_to_conv in H5. apply reds_to_conv in H1. eauto.
Qed.


(** Some congruence consequences of [PiInj] .*)
Lemma ConvSort : forall Γ s t, Γ ⊢ !s ≡' !t  -> s = t.
intros. apply Confluence in H as (R& ?& ? & ? & ?). apply Sort_Reds in H as ( ? & _).
apply Sort_Reds in H0 as (? & _). rewrite H in H0; injection H0; intros; trivial.
Qed.


Lemma reds_Pi : forall Γ A A' s, Γ ⊢ A  ▹▹ A' : !s -> forall B B' t u, A::Γ ⊢ B  ▹▹ B' :!t ->
  Rel s t u ->  Γ ⊢ Π (A), B ▹▹ Π (A'), B' : !u.
assert (forall Γ A A' S, Γ ⊢ A  ▹▹ A' : S -> forall s B B' t u, S = !s -> A::Γ ⊢ B  ▹ B' :!t ->
  Rel s t u ->  Γ ⊢ Π (A), B ▹▹ Π (A'), B' : !u).
induction 1; intros; subst. constructor. eapply typ_pi; eauto.
apply typ_reds_trans with (Pi t B). eapply IHtyp_reds1. reflexivity. apply red_refl_lt in H2.
apply H2. trivial. eapply IHtyp_reds2. reflexivity. eapply conv_in_env. apply H2.
apply reds_to_conv in H. eauto. trivial.
assert (forall Γ' B B' T, Γ' ⊢ B  ▹▹ B' : T -> forall Γ A A' s t u, T = !t -> Γ' = A::Γ ->
  Γ ⊢ A  ▹ A' :!s ->   Rel s t u ->  Γ ⊢ Π (A), B ▹▹ Π (A'), B' : !u). clear H.
induction 1; intros; subst. constructor. eapply typ_pi; eauto.
apply typ_reds_trans with (Pi A t). eapply IHtyp_reds1. reflexivity. trivial. apply red_refl_lt in H3; apply H3.
trivial. eapply IHtyp_reds2. reflexivity. trivial. apply H3. trivial.
intros. apply typ_reds_trans with (Pi A B'). eapply H0. apply H2. reflexivity. trivial.
apply reds_refl_lt in H1; apply H1. trivial.
eapply H. apply H1. reflexivity. apply reds_refl_rt in H2; apply H2.  trivial.
Qed.


Lemma reds_La : forall Γ A A' s, Γ ⊢ A  ▹▹ A' : !s -> forall M M' B B' t u, A::Γ ⊢ M ▹▹ M' :B ->
  A::Γ ⊢ B ▹ B' : !t ->  Rel s t u ->  Γ ⊢  λ[A], M ▹▹ λ[A'], M' :Π (A), B .
assert (forall Γ A A' S, Γ ⊢ A  ▹▹ A' : S ->  forall M M' B B' s t u,S = !s ->  A::Γ ⊢ M ▹ M' :B ->
  A::Γ ⊢ B ▹ B' : !t ->  Rel s t u ->  Γ ⊢  λ[A], M ▹▹ λ[A'], M' :Π (A), B) .
induction 1; intros; subst. constructor. econstructor. apply H3. trivial. apply H2. trivial.
apply typ_reds_trans with (La t M). eapply IHtyp_reds1. reflexivity. apply red_refl_lt in H2; trivial.
apply H3. apply H4. eapply reds_typ_pcompat.  eapply IHtyp_reds2.  reflexivity.  
eapply conv_in_env. apply H2. apply reds_to_conv in H; eauto.
eapply conv_in_env. apply H3. apply reds_to_conv in H; eauto. apply H4.
apply typ_peq_sym. apply reds_to_conv with u0. eapply reds_Pi. apply H. apply red_refl_lt in H3; constructor; apply H3. trivial.
assert (forall Γ' M M' B, Γ' ⊢ M  ▹▹ M' : B -> forall Γ A A' B' s t u, Γ' = A::Γ ->
  Γ ⊢ A  ▹ A' :!s ->  A::Γ ⊢ B ▹ B' : !t ->  Rel s t u ->  Γ ⊢  λ[A], M ▹▹ λ[A'], M' :Π (A), B) . clear H.
induction 1; intros; subst.
constructor. econstructor. apply H3. trivial. apply H2. trivial.
apply typ_reds_trans with (La A t). eapply IHtyp_reds1. trivial. apply red_refl_lt in H2; apply H2.
apply H3. apply H4. eapply IHtyp_reds2. trivial. apply H2. apply H3. apply H4.
intros. apply typ_reds_trans with (La A M'). eapply H0. apply H2. trivial. apply reds_refl_lt in H1; apply H1. 
apply H3. apply H4. eapply H. apply H1. reflexivity. apply reds_refl_rt in H2; apply H2.
apply H3. apply H4.
Qed.

Lemma reds_subst : forall A Γ M M' B , A::Γ ⊢ M  ▹▹ M' : B -> forall N N' , Γ ⊢ N ▹ N' : A ->
   Γ ⊢  M[ ← N ] ▹▹ M' [ ← N' ] : B[ ← N ].
intros until 1.  remember (A::Γ) as ΓΓ. revert A Γ HeqΓΓ. induction H; intros; subst.
constructor. eapply subst_gen. apply H. constructor. trivial.
eapply typ_reds_trans2. eapply IHtyp_reds1. reflexivity. apply H1.
eapply IHtyp_reds2. reflexivity. apply red_refl_rt in H1; trivial.
Qed.



Lemma reds_subst_gen : forall A Γ M M' B , A::Γ ⊢ M  ▹▹ M' : B -> forall N N' , Γ ⊢ N ▹▹ N' : A ->
   Γ ⊢  M[ ← N ] ▹▹ M' [ ← N' ] : B[ ← N ].
intros. revert M M' B H. induction H0; intros.
eapply reds_subst. apply H0. trivial.
eapply typ_reds_trans2. eapply IHtyp_reds1. apply H.
eapply IHtyp_reds2. constructor. apply reds_refl_rt in H; apply H. 
Qed.


Lemma eq_subst_gen :  forall A Γ M M' , A::Γ ⊢ M  ≡' M'  -> forall N N' N'' , Γ ⊢ N ▹▹ N' : A  ->
Γ ⊢ N'' ▹▹ N' : A  ->   Γ ⊢  M[ ← N ] ≡' M' [ ← N'' ] .
intros. apply Confluence in H as (P & q & q' & ? & ?).
apply typ_peq_trans with (P[ ← N']). apply reds_to_conv with q. change !q with (!q [ ← N]).
eapply reds_subst_gen. apply H. apply H0. apply typ_peq_sym.
apply reds_to_conv with q'. change !q' with (!q' [ ← N'']).
eapply reds_subst_gen. apply H2. apply H1.
Qed.

Lemma reds_App_ : forall Γ M M' A B , Γ ⊢ M ▹▹ M' : Π(A),B -> forall N N' , Γ ⊢ N ▹▹ N' : A ->
  Γ ⊢ M ·(A,B) N  ▹▹ M'·(A,B) N' : B[ ← N].
intros until 1. remember (Pi A  B) as P. revert A B HeqP. induction H; intros; subst.
revert B s t H. induction H0; intros.
destruct (typ_wf Γ s0 t0 (Pi T B) H0). destruct H1 as (? & ?); discriminate.
destruct H1 as (u & ?). apply pgen_pi in H1 as (T' & B'' & t1 & t2 & t3 & h).
decompose [and] h; clear h. injection H4; intros; subst; clear H4.
constructor.  econstructor. apply H1. apply H3. trivial. trivial. trivial.
apply typ_reds_trans with (App s0 T B t). eapply IHtyp_reds1. apply red_refl_lt in H; trivial.
apply reds_typ_pcompat with (B [← t]). eapply IHtyp_reds2. trivial.
apply typ_wf in H. destruct H. destruct H as (? & ?); discriminate. destruct H as (s3 & ?).
apply pgen_pi in H as (T' & B'' & t1 & t2 & t3 & h). decompose [and] h; clear h.
injection H2; intros; subst; clear H2. apply typ_peq_sym.
apply reds_to_conv with t2. change !t2 with (!t2 [← s]).
eapply reds_subst_gen. constructor. apply H0. trivial.
eapply typ_reds_trans2. eapply IHtyp_reds1. reflexivity. apply H1.
eapply IHtyp_reds2. reflexivity. constructor; apply reds_refl_rt in H1; trivial.
Qed.


Lemma reds_App__ : forall Γ M M' A B , Γ ⊢ M ▹ M' : Π(A),B -> forall B' s N N' , Γ ⊢ N ▹ N' : A ->
 A::Γ ⊢ B ▹▹ B' : !s ->   Γ ⊢ M ·(A,B) N  ▹▹ M·(A,B') N : B[ ← N].
intros. revert M M' N N' H H0 . remember (A::Γ) as ΓΓ. remember !s as S.
revert A Γ HeqΓΓ s HeqS. induction H1; intros; subst.
constructor. destruct (typ_wf Γ0 M M' (Pi A s) H0). destruct H2 as ( ?& ?); discriminate.
destruct H2 as (x & ?). apply pgen_pi in H2 as (A' & s' & s1 & s2 & s3 & h). decompose [and] h;clear h.
injection H5; intros; subst; clear H5.
econstructor. apply H2. apply H4. eapply relocate. apply H3. apply H. apply red_refl_lt with M'; trivial.
apply red_refl_lt with N'; trivial.
eapply typ_reds_trans2. eapply IHtyp_reds1. reflexivity. reflexivity. apply H. apply H0.
eapply IHtyp_reds2. reflexivity. reflexivity. apply typ_pcompat with (Pi A s). apply H.
apply typ_wf in H  as [ | ]. destruct H ; discriminate. destruct H as (x & ?).
apply pgen_pi in H as (A'' & s'' & a & b& c & h); decompose [and] h; clear h.
apply reds_to_conv with c. eapply reds_Pi. constructor. apply red_refl_lt in H2; apply H2.
eapply typ_reds_relocate. apply H1_. apply H1. trivial.
apply H0.
Qed.

Lemma reds_App___ : forall Γ M M' A B , Γ ⊢ M ▹ M' : Π(A),B -> forall A' s N N' , Γ ⊢ N ▹ N' : A ->
 Γ ⊢ A ▹▹ A' : !s ->   Γ ⊢ M ·(A,B) N  ▹▹ M·(A',B) N : B[ ← N].
intros. revert M M' N N' H H0 . remember !s as S. revert s HeqS. induction H1; intros; subst.
constructor. destruct (typ_wf Γ M M' (Pi s B) H0). destruct H2 as ( ?& ?); discriminate.
destruct H2 as (x & ?). apply pgen_pi in H2 as (s' & B' & s1 & s2 & s3 & h). decompose [and] h;clear h.
injection H5; intros; subst; clear H5.
econstructor. apply H2. eapply relocate. apply H4. apply H. trivial. apply red_refl_lt with M'; trivial.
apply red_refl_lt with N'; trivial.
eapply typ_reds_trans2. eapply IHtyp_reds1. reflexivity. apply red_refl_lt in H; apply H. apply red_refl_lt in H0; apply H0.
eapply IHtyp_reds2. reflexivity. apply typ_pcompat with (Pi s B). apply H.
apply typ_wf in H  as [ | ]. destruct H ; discriminate. destruct H as (x & ?).
apply pgen_pi in H as (s'' & B'' & a & b& c & h); decompose [and] h; clear h.
apply reds_to_conv with c. eapply reds_Pi. eapply typ_reds_relocate. apply H1_. apply H2. 
constructor; apply red_refl_lt in H1; apply H1. trivial. apply typ_pcompat with s.
apply H0. apply reds_to_conv in H1_. trivial.
Qed.


Lemma reds_App : forall Γ M M' A B , Γ ⊢ M ▹▹ M' : Π(A),B -> forall A' B' s t N N' , Γ ⊢ N ▹▹ N' : A ->
 Γ ⊢ A ▹▹ A' : !s ->  A::Γ ⊢ B ▹▹ B' : !t -> Γ ⊢ M ·(A,B) N  ▹▹ M'·(A',B') N' : B[ ← N].
intros. eapply typ_reds_trans. eapply reds_App_. apply H. apply H0.
apply reds_typ_pcompat with (B [ ← N']).  eapply typ_reds_trans. eapply reds_App___.
apply reds_refl_rt in H; apply H. apply reds_refl_rt in H0; apply H0. apply H1.
eapply reds_App__. apply typ_pcompat with (Π(A),B). apply reds_refl_rt in H; apply H.
apply reds_refl_lt in H; apply typ_wf in H  as [ | ]. destruct H ; discriminate. destruct H as (x & ?).
apply pgen_pi in H as (A'' & B'' & a & b& c & h); decompose [and] h; clear h.
apply reds_to_conv with c. eapply reds_Pi. eapply typ_reds_relocate. apply H1. apply H4.
constructor. eapply relocate. apply H3. apply reds_refl_lt in H2; apply H2. trivial. apply reds_refl_rt in H0.
apply typ_pcompat with A. apply H0. eauto. eapply conv_in_env_reds. apply H2. eauto.
apply typ_peq_sym. apply reds_to_conv with t. change !t with (!t[← N]).
eapply reds_subst_gen. apply reds_refl_lt in H2; constructor; apply H2. trivial.
Qed.

(** Subject Reduction: PTS_{atr} can lift an untyped reduction from [Betap] to
PTS_{atr}. However, we prove here that a one-step [Betap] reduction can be lifted to
a multi-step PTS_{atr} judgment. This is because of our new annotation, we need
some room to check the validity of the typing. *)
Theorem SR : (forall M N, Betap M N -> forall Γ P A,  Γ ⊢ M ▹ P : A -> Γ ⊢ M ▹▹ N : A ).
induction 1; simpl in *; intros.
constructor; apply red_refl_lt in H; trivial.
(**)
constructor; apply red_refl_lt in H; trivial.
(**)
apply pgen_la in H1 as (A'' & M'' & D & D' & t1 & t2 & t3 & h).
decompose [and] h; clear h. apply reds_typ_pcompat with (Pi A D); trivial.
eapply reds_La.  eapply IHBetap1; eauto. eapply IHBetap2; eauto. apply H4. apply H1.
(**)
apply pgen_pi in H1. destruct H1 as (A'' & B'' & t1 & t2 & t3 & h). 
decompose [and] h; clear h. destruct H6.  subst. eapply reds_Pi. eapply IHBetap1; eauto.
eapply IHBetap2; eauto. trivial. apply reds_typ_pcompat with !t3; intuition.
eapply reds_Pi. eapply IHBetap1; eauto. eapply IHBetap2; eauto. trivial.
(**)
apply pgen_app in H3 as (C & C'  & D' & N'' & t1 & t2 & t3 & h). decompose [and] h; clear h.
apply reds_typ_pcompat with (B [ ← N]); trivial. destruct H9. destruct H8 as (M'' & ? & ? & _ ). clear P. subst.
eapply reds_App. eapply IHBetap1; eauto. eapply IHBetap2; eauto. eapply IHBetap3; eauto. eapply IHBetap4; eauto.

destruct H8 as (U0 & K & K' & T & T' & ? & -> &  ? & _ & ? & ? & ?). subst.
eapply reds_App. eapply IHBetap1. apply typ_pcompat with (Π(U0),B). apply typ_pcompat with (Π(C),B).
econstructor. apply H3. apply H5. apply H4. apply H9. apply typ_peq_sym. apply reds_to_conv with t3.
eapply reds_Pi. apply H11. constructor. apply red_refl_lt with D'. eapply conv_in_env. apply H4. eauto. trivial.
apply reds_to_conv with t3. eapply reds_Pi. apply H10. constructor. apply red_refl_lt with D'. eapply conv_in_env.
apply H4. eauto. trivial. eapply IHBetap2. apply typ_pcompat with C. apply H6.
apply reds_to_conv in H11. apply reds_to_conv in H10. eauto. eapply IHBetap3; eauto. eapply IHBetap4; eauto. 
eapply conv_in_env. apply H4.  apply reds_to_conv in H11. apply reds_to_conv in H10. eauto.
(**)
apply pgen_app in H1 as (C & C' &  D' &  N'' & t1 & t2 & t3 & h).
decompose [and] h; clear h. apply reds_typ_pcompat with (L [ ← N]); trivial.
destruct H7. destruct H6 as (LA & ? & ? &  _). clear P. subst. 
apply pgen_la in H6 as (A'' & m'' & F & F' & u1 & u2 & u3 & h). decompose [and] h; clear h.
clear H10 LA. apply PiInj in H12 as (? & ?).  destruct (Confluence Γ A C H10) as ( Z & a & c & ? & ?).
destruct (Confluence (A::Γ) F L H11) as (Y & f & d & ? & ?).
apply typ_reds_trans with ((λ[A],M)·(Z,L)N). eapply reds_App___.
apply typ_pcompat with  (Π(Z),Y). apply typ_pcompat with (Π(A),Y). econstructor. apply H6. apply H8.
eapply reds_refl_rt. eapply typ_reds_relocate. apply H14. apply H9. apply typ_pcompat with F. apply H7. eauto.
apply reds_to_conv with u3. apply reds_Pi with u1 u2. eapply typ_reds_relocate. apply H12. apply H8.
constructor. apply reds_refl_rt with F. eapply typ_reds_relocate. apply H14. apply H9. trivial. apply typ_peq_sym.
apply reds_to_conv with t3. apply reds_Pi with t1 t2. eapply typ_reds_relocate. apply H13. apply H3.
eapply typ_reds_relocate. eapply conv_in_env_reds. apply H15. eauto. apply H2. trivial. apply H4. apply H13. 
apply typ_reds_trans with ((λ[A],M)·(Z,Y)N). eapply reds_App__.
apply typ_pcompat with  (Π(Z),Y). apply typ_pcompat with (Π(A),Y). econstructor. apply H6. apply H8.
eapply reds_refl_rt. eapply typ_reds_relocate. apply H14. apply H9. apply typ_pcompat with F. apply H7. eauto.
apply reds_to_conv with u3. apply reds_Pi with u1 u2. eapply typ_reds_relocate. apply H12. apply H8.
constructor. apply reds_refl_rt with F. eapply typ_reds_relocate. apply H14. apply H9. trivial. apply typ_peq_sym.
apply reds_to_conv with t3. apply reds_Pi with t1 t2. constructor. eapply reds_refl_rt. eapply typ_reds_relocate. apply H13.
apply H3. eapply typ_reds_relocate. eapply conv_in_env_reds. apply H15. eauto. eapply conv_in_env.
apply H2. eauto. trivial. apply typ_pcompat with C. apply H4. eauto. eapply conv_in_env_reds. apply H15. eauto.
eapply typ_reds_trans2 with (N:=M[← N]). constructor. apply typ_pcompat with (Y[← N]). econstructor. apply H6. apply H8.
eapply reds_refl_rt.  eapply typ_reds_relocate. apply H12. apply H8. constructor. apply red_refl_lt in H8; apply H8.
eapply typ_reds_relocate. apply H12. apply H8. eapply reds_refl_rt. eapply typ_reds_relocate. apply H14. apply H9.
apply typ_pcompat with F. apply red_refl_lt with m''; trivial. eauto. apply red_refl_lt with N''. apply typ_pcompat with C. trivial.
eauto. apply typ_peq_sym. apply reds_to_conv with d. change !d with (!d[← N]). eapply reds_subst. apply H15. apply typ_pcompat with C.
apply red_refl_lt with N''; trivial. eauto. eapply reds_subst_gen. eapply IHBetap1. apply H7. eapply IHBetap2. apply typ_pcompat with C.
apply H4. eauto. 

destruct H6 as (U0 & G & G' & T & T' & h); decompose [and] h; clear h. clear P H9. injection H8; intros; subst; clear H8.
eapply typ_reds_trans2 with (N :=  T[← N]).
constructor. econstructor. apply H1. apply H3. apply H13. apply H11. trivial. apply H2.
apply red_refl_lt with T'; trivial. apply red_refl_lt with N''; trivial. eapply reds_subst_gen.
eapply IHBetap1. apply H7. eapply IHBetap2. apply H4.
Qed.

Lemma SR_trans :   (forall M N, Betaps M N -> forall Γ P A,  Γ ⊢ M ▹ P : A -> Γ ⊢ M ▹▹ N : A ).
induction 1; intros.
eapply SR. trivial. apply H0.
apply typ_reds_trans with N. eapply IHBetaps1. apply H1.
eapply IHBetaps2. eapply reds_refl_rt. eapply IHBetaps1. apply H1.
Qed.


Lemma SR_trans' : forall M N, Betas M N -> forall Γ P A,  Γ ⊢ M ▹ P : A -> Γ ⊢ M ▹▹ N : A.
intros.
eapply SR_trans. apply Betaps_Betas_closure. trivial. apply H0.
Qed.

Lemma peq_subst : forall A Γ B B' , A::Γ ⊢ B ≡' B' -> forall N N' , Γ ⊢ N ▹ N' : A -> 
   Γ ⊢ B [ ← N ] ≡' B'[ ← N]. intros until 1.
remember (A::Γ) as ΓΓ. revert A Γ HeqΓΓ. induction H; intros; subst.
apply typ_peq_intro with s. change !s with (!s[← N]). eapply subst_gen.
apply H. constructor. apply red_refl_lt with N';  trivial.
apply typ_peq_intro2 with s. change !s with (!s[← N]). eapply subst_gen.
apply H. constructor. apply red_refl_lt with N';  trivial.
eauto.
Qed.



End PTS_ATR_mod.

