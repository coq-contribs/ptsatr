(** * Definition of PTS with Judgmental Equality (PTSe)
 Here we will define what is a judgmental equality and some 
 basic results.*)
 (** The main difference between PTS and PTSe is that we do
 not rely here on bare beta-conversion, but we also check that
 every step of the conversion is welltyped.*)
Require Import base.
Require Import ut_term.
Require Import ut_red.
Require Import ut_env.
Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt.
Require Import Plus Minus.
Require Import ut_typ.
Require Import ut_sr.

Module Type ut_typ_eq_mod (X:term_sig) (Y:pts_sig X) (TM:ut_term_mod X) (EM:ut_env_mod X TM) (RM: ut_red_mod X TM)
 (SRM: ut_sr_mod X Y TM EM RM).
 Import X Y TM EM RM SRM.

(** Typing Rules.*)
Reserved Notation "Γ ⊢e t : T" (at level 80, t, T at level 30, no associativity) .
Reserved Notation "Γ ⊢e M = N : T" (at level 80, M, N , T at level 30, no associativity).
Reserved Notation "Γ ⊣e " (at level 80, no associativity).

Inductive wf : Env -> Prop :=
 | wfe_nil : nil ⊣e
 | wfe_cons : forall Γ A s, Γ ⊢e A : !s -> A::Γ ⊣e
where "Γ ⊣e" := (wf Γ) : UT_scope
with typ : Env -> Term -> Term -> Prop :=
 | cSort : forall Γ s t, Ax s t -> Γ ⊣e -> Γ  ⊢e !s : !t
 | cVar : forall  Γ A v, Γ ⊣e -> A ↓ v  ⊂ Γ -> Γ ⊢e #v : A 
 | cPi : forall Γ A B s t u, 
     Rel s t u -> Γ ⊢e A : !s -> A::Γ ⊢e B : !t -> Γ ⊢e  Π(A), B : !u 
 | cLa : forall Γ A b B s1 s2 s3, Rel s1 s2 s3 -> Γ ⊢e  A : !s1 -> A::Γ ⊢e B : !s2 -> 
     A::Γ ⊢e b : B -> Γ ⊢e λ[A], b: Π(A), B
 | cApp : forall Γ a b A B , Γ ⊢e a : Π(A), B -> Γ ⊢e b :  A -> Γ ⊢e a·b : B[←b]
 | Cnv : forall Γ a A B s,
      Γ ⊢e A = B  : !s -> Γ ⊢e a : A -> Γ ⊢e a : B
where "Γ ⊢e t : T" := (typ Γ t T) : UT_scope
with typ_eq : Env -> Term -> Term -> Term -> Prop :=
 |cPi_eq : forall Γ A A' B B' s t u, Rel s t u -> Γ ⊢e A = A' : !s -> (A::Γ)⊢e B = B' : !t ->
   Γ ⊢e Π(A),B = Π(A'),B' : !u
 | cLa_eq : forall Γ A A' B M M' s t u, Rel s t u -> Γ ⊢e A = A' : !s -> (A::Γ) ⊢e M = M' : B ->
   (A::Γ) ⊢e B : !t -> Γ ⊢e λ[A],M = λ[A'],M' : Π(A),B
 | cApp_eq : forall Γ M M' N N' A B, Γ ⊢e M = M' : Π(A),B -> Γ⊢e N = N' : A ->
     Γ ⊢e M·N = M'·N' : B [← N]
 | cRefl : forall Γ M A, Γ ⊢e M : A -> Γ ⊢e M = M : A
 | cSym : forall Γ M N A , Γ ⊢e M = N : A -> Γ ⊢e N = M : A
 | cTrans : forall Γ M N P A, Γ ⊢e M = N : A -> Γ ⊢e N = P : A -> Γ ⊢e M = P : A
 | Cnv_eq : forall Γ M N A B s, Γ ⊢e A = B : !s -> Γ ⊢e M = N : A -> Γ ⊢e M = N : B
 | cBeta : forall Γ A B M N s t u, Rel s t u -> Γ ⊢e A : !s -> (A::Γ) ⊢e B : !t ->
    (A::Γ) ⊢e M : B -> Γ ⊢e N : A -> Γ ⊢e (λ[A],M)·N = M[← N] : B[← N]
where "Γ ⊢e M = N : T":= (typ_eq Γ M N T) : UT_scope.

Hint Constructors wf typ typ_eq.

Open Scope UT_scope.

(* begin hide *)
Scheme typ_ind' := Induction for typ Sort Prop
      with typ_eq_ind' := Induction for typ_eq Sort Prop
      with wf_ind' := Induction for wf Sort Prop.

Combined Scheme typ_induc from typ_ind', typ_eq_ind',  wf_ind'.
(* end hide *)

(** These lemmas are almost the same as for declarative PTS:
  - well formation of contexts
  - weakening
  - substitution
  - type correctness
  - ...
    *)
Lemma wf_typ : forall Γ t T, Γ ⊢e t : T -> Γ ⊣e.
induction 1; intros; intuition.
Qed.

Lemma wf_typ_eq : forall Γ M N T, Γ ⊢e M = N : T -> Γ ⊣e.
induction 1;  intuition.
apply wf_typ in H; trivial.
apply wf_typ in H0; trivial.
Qed.

Hint Resolve wf_typ wf_typ_eq.

Theorem weakening: (forall Δ M T, Δ ⊢e M : T -> forall Γ A s n Δ', ins_in_env Γ A n Δ Δ' ->   Γ ⊢e A :!s -> 
                 Δ' ⊢e M ↑ 1 # n : T ↑ 1 # n ) /\
                (forall Δ M N T, Δ ⊢e M = N : T -> forall Γ A s n Δ', ins_in_env Γ A n Δ Δ' ->   Γ ⊢e A :!s -> 
                 Δ' ⊢e M ↑ 1 # n = N ↑ 1 # n : T ↑ 1 # n ) /\
(forall Γ, Γ ⊣e -> forall Δ Γ' n A , ins_in_env Δ A n Γ Γ' -> forall s, Δ ⊢e A : !s -> Γ' ⊣e).
apply typ_induc; simpl in *; intros.
(*1*)
eauto.
(*2*)
destruct le_gt_dec.
constructor. eapply H;  eauto. destruct i as (AA & ?& ?). exists AA; split. rewrite H2.
change (S (S v)) with (1+ S v). rewrite liftP3; trivial. intuition. simpl; constructor; trivial. eapply ins_item_ge.
apply H0. trivial. trivial. constructor. eapply H; eauto.  eapply ins_item_lift_lt. apply H0. trivial. trivial.
(*3*)
econstructor. apply r. eapply H; eauto. eapply H0. constructor; apply H1. apply H2.
(*4*)
econstructor. apply r. eapply H; eauto. eapply H0; eauto. eapply H1; eauto.
(*5*)
change n with (0+n). rewrite substP1. simpl.
econstructor. eapply H; eauto. eapply H0; eauto.
(*6*)
apply Cnv with (A↑ 1 # n) s; intuition.
eapply H; eauto. eapply H0; eauto. 
(**)
apply cPi_eq with s t. trivial. eapply H; eauto. eapply H0; eauto.
(**)
apply cLa_eq with s t u; trivial. eapply H; eauto. eapply H0; eauto. eapply H1; eauto.
(**)
change n with (0+n). rewrite substP1. simpl.
apply cApp_eq with (A↑ 1 # n). eapply H; eauto. eapply H0; eauto.
(**) constructor; eapply H; eauto. (**) econstructor; eauto. (**) econstructor; eauto. (**) econstructor; eauto.
(**)
change n with (0+n). rewrite 2! substP1. simpl. 
apply cBeta with s t u; eauto.
(* wf *)
inversion H; subst; clear H. eauto.
(**)
inversion  H0; subst; clear H0.
eauto. 
apply wfe_cons with s; trivial. change !s with !s ↑ 1 # n0.
eapply H.  apply H6. apply H1.
Qed.


Theorem thinning :
   forall Γ M T A s,
      Γ ⊢e M  : T -> 
   Γ ⊢e A : !s ->
   A::Γ ⊢e M ↑ 1 : T ↑ 1.
intros.
eapply weakening. apply H. constructor. apply H0.
Qed.

Theorem thinning_n : forall n Δ Δ',
   trunc n Δ Δ' ->
   forall M T , Δ' ⊢e M  : T  -> Δ ⊣e ->
               Δ ⊢e M ↑ n : T ↑ n.
intro n; induction n; intros.
inversion H; subst; clear H.
rewrite ! lift0; trivial.
inversion H; subst; clear H.
change (S n) with (1+n).
replace (M ↑ (1+n)) with ((M ↑ n )↑ 1) by (apply lift_lift).
replace (T ↑ (1+n)) with ((T ↑ n) ↑ 1) by (apply lift_lift).
inversion H1; subst; clear H1.
apply thinning with s; trivial.
eapply IHn. apply H3. trivial. apply wf_typ in H2; trivial.
Qed.

Theorem thinning_eq :
   forall Γ M N T A s,
      Γ ⊢e M = N : T -> 
   Γ ⊢e A : !s ->
   A::Γ ⊢e M ↑ 1 = N ↑ 1 : T ↑ 1.
intros.
eapply weakening. apply H. constructor. apply H0.
Qed.

Theorem thinning_eq_n : forall n Δ Δ',
   trunc n Δ Δ' ->
   forall M N T , Δ' ⊢e M = N : T  -> Δ ⊣e ->
               Δ ⊢e M ↑ n = N ↑ n: T ↑ n.
intro n; induction n; intros.
inversion H; subst; clear H.
rewrite 3! lift0; trivial.
inversion H; subst; clear H.
change (S n) with (1+n).
replace (M ↑ (1+n)) with ((M ↑ n )↑ 1) by (apply lift_lift).
replace (N ↑ (1+n)) with ((N ↑ n )↑ 1) by (apply lift_lift).
replace (T ↑ (1+n)) with ((T ↑ n) ↑ 1) by (apply lift_lift).
inversion H1; subst; clear H1.
apply thinning_eq with s; trivial.
eapply IHn. apply H3. trivial. apply wf_typ in H2; trivial.
Qed.

Lemma conv_in_env_var : forall C n Γ, C ↓ n ∈ Γ ->
  forall Γ1 Γ2 A B s, Γ = Γ2++(A::Γ1) -> Γ1 ⊢e A = B : !s -> n < List.length Γ2 ->
  C ↓ n ∈ Γ2++(B::Γ1).
induction 1; intros.
destruct Γ2; simpl in *. apply lt_n_O in H1; elim H1.
injection H; intros; subst; clear H.
constructor.

destruct Γ2; simpl in *. apply lt_n_O in H2; elim H2.
injection H0; intros; subst; clear H0.
constructor. apply IHitem with A s; trivial.
intuition.
Qed.

Lemma conv_in_env_var2 : forall C n Γ, C ↓ n ∈ Γ ->
  forall Γ1 Γ2 A B s , Γ = Γ2++(A::Γ1) -> Γ1 ⊢e A = B : !s ->
  List.length Γ2 < n ->
  C ↓ n ∈ Γ2++(B::Γ1).
induction 1; intros.
apply lt_n_O in H1; elim H1.
destruct Γ2; simpl in *.
injection H0; intros; subst; clear H0.
constructor. trivial.

destruct Γ2; simpl in *.
constructor. injection H0; intros; subst; clear H0.

inversion H; subst; clear H. apply lt_irrefl in H2; elim H2.
constructor. trivial.
injection H0; intros; subst; clear H0.
constructor. rewrite app_comm_cons. apply IHitem with A s; trivial.
simpl. intuition.
Qed.

Lemma conv_in_env_var3 : forall Γ1 (B:Term) Γ2 , B ↓ (List.length Γ1) ∈ Γ1++(B::Γ2).
induction Γ1; intros.
simpl. constructor.
simpl. constructor. apply IHΓ1.
Qed.

Lemma conv_in_env_var_lift : forall C n Γ, C ↓ n ⊂ Γ ->
  forall Γ1 Γ2 A B s, Γ = Γ2 ++(A::Γ1) -> Γ1 ⊢e A = B : !s -> n < List.length Γ2 ->
  C ↓ n ⊂ Γ2++(B::Γ1).
intros.
destruct H as (u & h1 & h2).
apply (conv_in_env_var u n Γ) with Γ1 Γ2 A B s in h2; trivial.
exists u; intuition.
Qed.

Lemma conv_in_env_var_lift2 : forall C n Γ, C ↓ n ⊂ Γ ->
  forall Γ1 Γ2 A B s, Γ = Γ2++(A::Γ1) -> Γ1 ⊢e A = B : !s ->
  List.length Γ2 < n -> C ↓ n ⊂ Γ2++(B::Γ1).
intros.
destruct H as (u & h1 & h2).
apply (conv_in_env_var2 u n Γ) with Γ1 Γ2 A B s in h2; trivial.
exists u; intuition.
Qed.

Lemma conv_in_env_var_lift3 : forall Γ1 (A:Term) Γ2 ,
  (A ↑ (S (List.length Γ1))) ↓ (List.length Γ1) ⊂ Γ1++(A::Γ2).
induction Γ1; intros.
simpl. exists A; intuition.
simpl.
assert( H := IHΓ1 A Γ2).
destruct H as ( ?& ?& ?).
apply inv_lift in H. subst.
exists x; intuition.
Qed.


Lemma conv_in_env_aux_trunc : forall A (Γ1 Γ2:list A) B ,
  trunc (S (length Γ1)) (Γ1  ++ B :: Γ2) Γ2.
induction Γ1; simpl; intros.
constructor; constructor.
constructor.
apply IHΓ1.
Qed.


(** Conversion is the context is here provable without SR since every reduction
step is checked valid.*)
Theorem conv_in_env : (forall Γ M T, Γ ⊢e  M : T-> forall Γ1 Γ2 A B s, Γ = Γ1++(A::Γ2) -> Γ2 ⊢e A = B : !s -> 
  Γ2 ⊢e B : !s -> (Γ1++(B::Γ2)) ⊢e M : T) /\
 (forall Γ M N T, Γ ⊢e  M = N : T-> forall Γ1 Γ2 A B s, Γ = Γ1++(A::Γ2) -> Γ2 ⊢e A = B : !s -> 
  Γ2 ⊢e B : !s -> (Γ1++(B::Γ2)) ⊢e M = N : T ) /\
 (forall Γ, Γ ⊣e -> forall Γ1 Γ2 A B s, Γ = Γ1++(A::Γ2) -> Γ2 ⊢e A = B : !s -> Γ2 ⊢e B : !s -> Γ1++(B::Γ2) ⊣e).
apply typ_induc; intros; simpl in *.
(**) 
constructor. trivial. apply H with A s0; trivial.
(**)
destruct (lt_eq_lt_dec v (List.length Γ1)) as [ [] | ].
econstructor. apply H with A0 s; trivial. eapply conv_in_env_var_lift. apply i. apply H0. apply H1. trivial.
subst. destruct i as (a & ?& ?). subst. replace a with A0 in *. apply Cnv with (B↑ (S (length Γ1))) s.
change !s with (!s↑ (S (length Γ1))). apply thinning_eq_n with Γ2. apply conv_in_env_aux_trunc. intuition. 
apply H with A0 s; trivial.  constructor. apply H with A0 s; trivial. exists B; intuition.
clear. induction Γ1; simpl in *. constructor. constructor; intuition.
generalize H3; clear. revert Γ2 A0 a. induction Γ1; intros; simpl in *. inversion H3;subst; clear H3. trivial.
inversion H3; subst; clear H3. eapply IHΓ1. apply H0.
econstructor. apply H with A0 s; trivial. eapply conv_in_env_var_lift2. apply i. apply H0. apply H1. trivial.
(**)
apply cPi with s t;trivial. apply H with A0 s0; trivial.
rewrite app_comm_cons. eapply H0. rewrite H1; simpl; reflexivity. apply H2. trivial.
(**)
apply cLa with s1 s2 s3;trivial. apply H with A0 s; trivial.
rewrite app_comm_cons. eapply H0. rewrite H2; simpl; reflexivity. apply H3. trivial.
rewrite app_comm_cons. eapply H1. rewrite H2; simpl; reflexivity. apply H3. trivial.
(**)
apply cApp with A. apply H with A0 s; trivial. apply H0 with A0 s; trivial.
(**)
apply Cnv with A s; trivial. apply H with A0 s0; trivial. apply H0 with A0 s0; trivial.
(**)
apply cPi_eq with s t;trivial. apply H with A0 s0; trivial.
rewrite app_comm_cons. eapply H0. rewrite H1; simpl; reflexivity. apply H2. trivial.
(**)
apply cLa_eq with s t u;trivial. apply H with A0 s0; trivial.
rewrite app_comm_cons. eapply H0. rewrite H2; simpl; reflexivity. apply H3. trivial.
rewrite app_comm_cons. eapply H1. rewrite H2; simpl; reflexivity. apply H3. trivial.
(**)
apply cApp_eq with A. apply H with A0 s; trivial. apply H0 with A0 s; trivial.
(**)
apply cRefl. apply H with A0 s; trivial.
(**)
apply cSym. apply H with A0 s; trivial.
(**)
apply cTrans with N. apply H with A0 s; trivial. apply H0 with A0 s; trivial.
(**)
apply Cnv_eq with A s; trivial. apply H with A0 s0; trivial. apply H0 with A0 s0; trivial.
(**)
apply cBeta with s t u; trivial. apply H with A0 s0; trivial. 
rewrite app_comm_cons. eapply H0. rewrite H3; simpl; reflexivity. apply H4. trivial.
rewrite app_comm_cons. eapply H1. rewrite H3; simpl; reflexivity. apply H4. trivial.
apply H2 with A0 s0; trivial.
(**)
destruct Γ1; simpl in *; discriminate.
(**)
destruct Γ1; simpl in *. injection H0;intros;  subst; clear H0. eauto.
injection H0; intros; subst; clear H0.
econstructor. apply H with A0 s0; trivial.
Qed.

(* The Substitution Lemma: we need to do it in several step because of the sym rule
of equality *)
Lemma substitution : (forall Γ t T , Γ  ⊢e t  : T  -> forall Δ P A, Δ  ⊢e P : A -> 
 forall Γ' n , sub_in_env Δ P A n Γ Γ' ->  Γ' ⊢e t [ n ←P ]  : T [ n ←P ]) /\
(forall Γ M N T , Γ  ⊢e M = N  : T  -> forall Δ P A, Δ  ⊢e P : A -> 
 forall Γ' n , sub_in_env Δ P A n Γ Γ' ->  Γ' ⊢e M [ n ←P ] = N [ n ←P ] : T [ n ←P ]) /\
 (forall Γ ,  Γ ⊣e -> forall Δ P A n Γ' , Δ ⊢e P : A -> 
  sub_in_env  Δ P A n Γ Γ' ->     Γ' ⊣e) .
apply typ_induc; simpl; intros.
(*1*)
constructor. trivial. eapply H. apply H0. apply H1.
(*2*)
destruct lt_eq_lt_dec  as [ [] | ]. 
constructor. eapply H; eauto. eapply nth_sub_item_inf. apply H1. intuition. trivial.
destruct i as (AA & ?& ?). subst. rewrite substP3; trivial.
rewrite <- (nth_sub_eq H1 H3).
eapply thinning_n. eapply sub_trunc. apply H1. trivial. eapply H;  eauto. intuition.
constructor. eapply H; eauto. destruct i as (AA & ? &?). subst.  rewrite substP3; trivial. 
exists AA; split. replace (S (v-1)) with v. trivial. rewrite <- pred_of_minus. rewrite <- (S_pred v n l); trivial.
eapply nth_sub_sup. apply H1. destruct v. apply lt_n_O in l; elim l. replace (S v - 1 ) with v. intuition.
rewrite <- pred_of_minus. simpl.  trivial. replace (S (v-1)) with v. trivial. rewrite <- pred_of_minus. rewrite <- (S_pred v n l); trivial.
intuition.  simpl; intuition. 
(*4*)
econstructor. apply r. eapply H; eauto. eapply H0. apply H1. constructor; apply H2. eauto.
(*5*)
econstructor. apply r. eapply H; eauto. eapply H0; eauto. eapply H1; eauto.
(*6*)
rewrite subst_travers. econstructor.
replace (n+1) with (S n) by (rewrite plus_comm; trivial). eapply H; eauto.
replace (n+1) with (S n) by (rewrite plus_comm; trivial).  eapply H0; eauto.
(*7*)
econstructor. eapply H. apply H1. trivial. eapply H0. apply H1. trivial.
(**)
apply cPi_eq with s t. trivial. eapply H. apply H1. trivial. eapply H0. apply H1. constructor; trivial.
(**)
apply cLa_eq with s t u. trivial. eapply H. apply H2. trivial. eapply H0. apply H2. constructor; trivial.
eapply H1. apply H2. constructor; trivial.
(**)
rewrite subst_travers. apply cApp_eq with (A[n ← P]). replace (Π (A [n ← P]), B [(n + 1) ← P]) with (Π(A),B)[n← P].
eapply H. apply H1. trivial. simpl; replace (n+1) with (S n). trivial. rewrite plus_comm; trivial. 
eapply H0. apply H1. trivial.
(**)
constructor. eapply H. apply H0. trivial.
(**)
constructor.  eapply H. apply H0. trivial.
(**)
apply cTrans with (N[n← P0]). eauto. eauto.
(**)
apply Cnv_eq with (A[n ← P]) s. eapply H. apply H1.  trivial. eapply H0. apply H1. trivial.
(**)
rewrite 2! subst_travers. simpl in *. replace (n+1) with (S n) by (rewrite plus_comm; trivial). apply cBeta with s t u. trivial.
eapply H. apply H3. trivial. eapply H0. apply H3. constructor;  trivial. eapply H1. apply H3. constructor; trivial.
eapply H2. apply H3. trivial.
(* wf *)
inversion H0.
inversion H1; subst; clear H1. apply wf_typ in H0; trivial.
econstructor. eapply H. apply H0. trivial.
Qed.


(** Here is the generalization of the substitution **)
Lemma substitution2 : forall Γ t T , Γ  ⊢e t  : T  -> forall Δ P P' A, Δ  ⊢e P = P': A ->  
  Δ  ⊢e P : A -> forall Γ' n , sub_in_env Δ P A n Γ Γ' ->  Γ' ⊢e t [ n ←P ]  = t [ n ← P'] : T [ n ←P ].
induction 1; intros; simpl in *.
(*1*)
constructor. constructor. trivial. eapply substitution.  apply H0. apply H2. apply H3.
(*2*)
destruct lt_eq_lt_dec as [ [] | ].
constructor. constructor. eapply substitution. apply H. apply H2. apply H3.
eapply nth_sub_item_inf. apply H3. intuition. trivial.
destruct H0 as (AA & ?& ?).
subst. rewrite substP3; intuition. 
rewrite <- (nth_sub_eq H3 H4).
eapply thinning_eq_n. eapply sub_trunc. apply H3. trivial. eapply substitution. apply H. apply H2. apply H3.
constructor. constructor. eapply substitution. apply H. apply H2.  apply H3. destruct H0 as (AA & ? &?). subst.  rewrite substP3; intuition.
exists AA; split. replace (S (v-1)) with v. trivial. rewrite <- pred_of_minus. rewrite <- (S_pred v n l). trivial.
eapply nth_sub_sup. apply H3. intuition. destruct v. apply lt_n_O in l; elim l. rewrite <- pred_of_minus. simpl; trivial.
intuition. replace (S (v-1)) with v. trivial. rewrite <- pred_of_minus. rewrite <- (S_pred v n l). trivial.
(*4*)
apply cPi_eq with s t; trivial.  eapply IHtyp1.  apply H2. trivial.  trivial. eapply IHtyp2. apply H2. trivial. constructor; trivial.
(*5*)
apply cLa_eq with s1 s2 s3; trivial. eapply IHtyp1.  apply H3. trivial.  trivial. eapply IHtyp3. apply H3. trivial. constructor; trivial.
change !s2 with (!s2[(S n)← P]). eapply substitution. apply H1. apply H4. constructor; trivial.
(*6*)
rewrite subst_travers. apply cApp_eq with (A[n← P]).
replace (n+1) with (S n) by (rewrite plus_comm; trivial).  eapply IHtyp1; eauto.
replace (n+1) with (S n) by (rewrite plus_comm; trivial).  eapply IHtyp2; eauto.
(*7*)
apply Cnv_eq with (A[n← P]) s. change !s with (!s[n ← P]). eapply substitution. apply H. apply H2. trivial.
eapply IHtyp. apply H1. trivial. trivial.
Qed.


Lemma wf_item : forall Γ A n, A ↓ n ∈ Γ ->
   forall  Γ', Γ ⊣e ->  trunc (S n) Γ Γ' -> exists s, Γ' ⊢e A : !s.
induction 1; intros.
inversion H0; subst; clear H0.
inversion H5; subst; clear H5.
inversion H; subst.
exists s; trivial.
inversion H1; subst; clear H1.
inversion H0; subst.
apply IHitem; trivial. apply wf_typ in H2; trivial.
Qed.

Lemma wf_item_lift : forall Γ t n ,Γ ⊣e  -> t ↓ n ⊂ Γ ->
  exists s,  Γ ⊢e t  : !s.
intros.
destruct H0 as (u & ? & ?).
subst.
assert (exists Γ' , trunc (S n) Γ Γ') by (apply item_trunc with u; trivial).
destruct H0 as (Γ' & ?).
destruct (wf_item Γ u n H1 Γ' H H0) as (t &  ?).
exists t. change !t with (!t ↑(S n)).
eapply thinning_n. apply H0. trivial. trivial.
Qed.

Lemma wgen_pi : forall Γ A B T, Γ ⊢e Π(A),B : T -> exists s, exists t, exists u, Rel s t u /\ 
 Γ ⊢e A : !s /\ (A::Γ) ⊢e B : !t.
intros. remember (Π(A),B) as P. revert A B HeqP. induction H; intros; subst; try discriminate.
injection HeqP; intros; subst; clear HeqP. exists s; exists t; exists u; split.
trivial. split; trivial.
destruct (IHtyp A0 B0) as (a & b& c & h); trivial. decompose [and] h; clear h.
exists a; exists b; exists c; split; trivial. split; trivial.
Qed.


(** Reflexivity and Type Correctness:
since we have symetry, and we did not check for the well formation of the function type
in the app-eq rule, we need to prove all at once:
 * Type Correctness
 * Left-Hand Reflexivity
 * Right-Hand Reflexivity
**)
Lemma TypeCorrect_Refl : (forall Γ M T, Γ ⊢e M : T -> exists s, T = !s \/ Γ ⊢e T : !s) /\
  (forall Γ M N T, Γ ⊢e M = N : T -> Γ ⊢e M : T /\ Γ ⊢e N : T /\ exists s, T = !s \/ Γ ⊢e T : !s) /\
  (forall Γ, Γ ⊣e -> True).
apply typ_induc; intros; simpl in *.
exists t; left; trivial.
(**)
apply wf_item_lift in i. destruct i.  exists x; right ; trivial. trivial.
(**)
exists u; left; trivial.
(**)
exists s3; right. apply cPi with s1 s2; trivial.
(**)
destruct H. destruct H. discriminate.
apply wgen_pi in H as (s1 & s2 & s3 & h). decompose [and] h; clear h.
exists s2; right. change !s2 with (!s2 [← b]). eapply substitution. apply H3. apply t0. constructor.
(**)
destruct H as (? & ? &?). exists s; right; trivial.
(**)
destruct H as (? & ?& ?), H0 as (? & ?& ?). split.
apply cPi with s t; trivial. split. apply cPi with s t; trivial.
change (A'::Γ) with (nil++A'::Γ). eapply conv_in_env. apply H3. simpl; reflexivity. apply t0. trivial.
exists u; left; trivial.
(**)
destruct H as (? & ?& ?), H0 as (? & ?& ?). split. apply cLa with s t u; trivial. 
split. apply Cnv with (Π(A'),B) u. apply cPi_eq with s t; intuition. change (A'::Γ) with (nil++A'::Γ).
eapply conv_in_env. constructor. apply t2. simpl; reflexivity. apply t0. trivial.
apply cLa with s t u; trivial. change (A'::Γ) with (nil++A'::Γ).
eapply conv_in_env. apply t2. simpl; reflexivity. apply t0. trivial.
change (A'::Γ) with (nil++A'::Γ). eapply conv_in_env. apply H4. simpl; reflexivity. apply t0. trivial.
exists u; right. apply cPi with s t; trivial.
(**)
destruct H as (? & ? & ?), H0 as (? & ?& ?). split. apply cApp with A; trivial. split.
destruct H2 as (s & ?). destruct H2. discriminate. apply wgen_pi in H2 as (a & b & c & h); decompose [and] h ;clear h.
apply Cnv with (B[← N']) b. change !b with (!b[← N]). apply cSym. eapply substitution2.
apply H7. apply t0. trivial. constructor. apply cApp with A; trivial.
destruct H2. destruct H2. discriminate. apply wgen_pi in H2 as (a & b & c & h); decompose [and] h; clear h.
exists b; right. change !b with (!b[←N]). eapply substitution. apply H7. apply H0. constructor.
(**)
intuition.
(**)
intuition.
(**)
destruct H as (? & ?& ?), H0 as (? & ? & ?).
intuition.
(**)
destruct H as (? & ?& ?), H0 as (? & ?& ?).
split. apply Cnv with A s; trivial. split. apply Cnv with A s; trivial.
exists s; right; trivial.
(**)
split. apply cApp with A; trivial. apply cLa with s t u; trivial. split.
eapply substitution. apply t2. apply t3. constructor. exists t; right.
change !t with (!t[← N]). eapply substitution. apply t1. apply t3. constructor.
(**)
trivial. trivial.
Qed.

Lemma TypeCorrect : forall Γ M T, Γ ⊢e M : T -> exists s, T = !s \/ Γ ⊢e T : !s.
apply TypeCorrect_Refl.
Qed.

Lemma TypeCorrect_eq :  forall Γ M N T, Γ ⊢e M = N : T -> exists s, T = !s \/ Γ ⊢e T : !s.
intros. apply TypeCorrect_Refl in H. intuition.
Qed.

Lemma left_reflexivity : forall Γ M N T, Γ ⊢e M = N : T -> Γ ⊢e M : T.
intros. apply TypeCorrect_Refl in H. intuition.
Qed.

Lemma right_reflexivity : forall Γ M N T, Γ ⊢e M = N : T -> Γ ⊢e N : T.
intros. apply TypeCorrect_Refl in H. intuition.
Qed.

(** We can easily prove that every judgement in PTSe is a valid one in PTS.
It's just a matter of "forgetting" typing information during the conversion.*)
Lemma FromPTSe_to_PTS : (forall Γ M T, Γ ⊢e M : T -> Γ ⊢ M : T) /\
  (forall Γ M N T, Γ ⊢e M = N : T -> Γ ⊢ M : T /\ Γ ⊢ N : T /\ M ≡ N) /\
  (forall Γ, Γ ⊣e -> Γ ⊣).
apply typ_induc; intros; simpl in *.
(**)
intuition.
(**)
intuition.
(**)
apply SRM.cPi with s t; trivial.
(**)
apply SRM.cLa with s1 s2 s3; trivial.
(**)
apply SRM.cApp with A; trivial.
destruct H as (? & ? & ?). apply SRM.Cnv with A s; trivial.
(**)
destruct H as (? & ?& ?). destruct H0 as ( ? & ? & ?).
split. apply SRM.cPi with s t; trivial. split. apply SRM.cPi with s t; trivial.
apply Betac_confl in H2 as (Z & ?& ?). apply Betas_env_sound_up with (Z::Γ).
apply Betas_env_sound with (A::Γ). trivial. apply Betas_env_hd; trivial.
econstructor. apply H1. apply Betas_env_hd; trivial. intuition.
(**)
destruct H as (? & ?& ?). destruct H0 as (? & ?& ?).
split. apply SRM.cLa with s t u; trivial. split. apply SRM.Cnv with (Π(A'),B) u.
intuition. apply SRM.cLa with s t u; trivial.
apply Betac_confl in H3 as (Z & ?& ?). apply Betas_env_sound_up with (Z::Γ).
apply Betas_env_sound with (A::Γ). trivial. apply Betas_env_hd; trivial.
econstructor. apply H2. apply Betas_env_hd; trivial.
apply Betac_confl in H3 as (Z & ?& ?). apply Betas_env_sound_up with (Z::Γ).
apply Betas_env_sound with (A::Γ). trivial. apply Betas_env_hd; trivial.
econstructor. apply H2. apply Betas_env_hd; trivial.
apply SRM.cPi with s t; trivial. intuition.
(**)
destruct H as (? & ?& ?). destruct H0 as (? & ?& ?).
split. apply SRM.cApp with A; trivial. split. 
assert (exists s, A::Γ ⊢ B : !s). apply SRM.TypeCorrect in H. destruct H as [ [s ?]| [ s ?] ].
discriminate. apply gen_pi in H as (a & b & c & h);decompose [and] h; clear h. exists b; trivial.
destruct H5 as (b & ?). apply SRM.Cnv with (B[← N']) b. intuition.
apply SRM.cApp with A; trivial. change !b with (!b[← N]). eapply SRM.substitution.
apply H5. apply H0. constructor. apply SRM.wf_typ in H5; trivial. intuition.
(**)
intuition.
(**)
intuition.
(**)
destruct H as (? & ?& ?), H0 as (? & ?& ?). intuition. eauto.
(**)
destruct H as (? & ?& ?). destruct H0 as ( ?& ?& ?).
split. apply SRM.Cnv with A s; trivial. split. apply SRM.Cnv with A s; trivial. trivial.
(**)
split. apply SRM.cApp with A. apply SRM.cLa with s t u; trivial. trivial.
split. eapply SRM.substitution. apply H1. apply H2. constructor. eauto. intuition.
(**)
intuition.
(**)
eauto.
Qed.

End ut_typ_eq_mod.




