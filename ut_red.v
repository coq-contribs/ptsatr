(** * Beta-reduction definition and properties.*)
Require Import base ut_term.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Plus.


Module Type ut_red_mod (X:term_sig)  (TM : ut_term_mod X).
 Import TM.

(** ** Usual Beta-reduction:
 - one step
 - multi step (reflexive, transitive closure)
 - converesion (reflexive, symetric, transitive closure)
 *)
Reserved Notation " A → B " (at level 80).

Inductive Beta : Term -> Term -> Prop :=
 | Beta_head : forall A M  N , (λ[A], M)· N → M [← N]
 | Beta_red1 : forall M M' N , M → M' -> M · N  → M'· N
 | Beta_red2 : forall M N  N', N → N' -> M · N  → M · N'
 | Beta_lam  : forall A M  M', M → M' -> λ[A],M → λ[A ],M'
 | Beta_lam2 : forall A A' M , A → A' -> λ[A],M → λ[A'],M
 | Beta_pi   : forall A B  B', B → B' -> Π(A),B → Π(A ),B'
 | Beta_pi2  : forall A A' B , A → A' -> Π(A),B → Π(A'),B
where "M → N" := (Beta M N) : UT_scope.

Reserved Notation " A →→ B " (at level 80).

Inductive Betas : Term -> Term -> Prop :=
 | Betas_refl  : forall M    , M →→ M
 | Betas_Beta  : forall M N  , M → N  -> M →→ N
 | Betas_trans : forall M N P, M →→ N -> N →→ P -> M →→ P
where  " A →→ B " := (Betas A B) : UT_scope.

Reserved Notation " A ≡ B " (at level 80).

Inductive Betac : Term -> Term -> Prop :=
 | Betac_Betas : forall M N  , M →→ N -> M ≡ N
 | Betac_sym   : forall M N  , M ≡ N  -> N ≡ M
 | Betac_trans : forall M N P, M ≡ N   -> N ≡ P -> M ≡ P
where " A ≡ B " := (Betac A B)  : UT_scope.

Hint Constructors Beta.
Hint Constructors Betas.
Hint Constructors Betac.

(** Facts about [Betas] and [Betac]: Congruence. *)
Lemma Betac_refl : forall M, M ≡ M.
intros; constructor; constructor.
Qed.

Hint Resolve Betac_refl.

Lemma Betas_App : forall M M' N N',M →→ M' -> N →→ N' -> M · N →→ M' · N'.
assert (forall a b c, b →→ c ->  a·b →→ a·c).
induction 1; eauto.
assert (forall a b c, b→→c -> b· a →→ c· a).
induction 1; eauto.
intros; eauto.
Qed.

Hint Resolve Betas_App.

Lemma Betac_App : forall M M' N N' , M ≡ M' -> N ≡ N' -> M · N ≡ M' · N'.
assert (forall a b c, b ≡ c ->  a· b ≡ a· c).
induction 1; eauto.
assert (forall a b c , b ≡ c -> b·a ≡ c·a).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betac_App.

Lemma Betas_La : forall A A' M M', A →→ A' -> M →→ M' -> λ[A],M →→ λ[A'],M'.
assert (forall a b c , a →→ b -> λ[c],  a →→ λ[c], b).
induction 1; eauto.
assert (forall a b c, a →→ b -> λ[a], c →→ λ[b], c).
induction 1; eauto.
eauto.
Qed.


Hint Resolve Betas_La.

Lemma Betac_La: forall A A' M M', A ≡ A' -> M ≡ M' -> λ[A],M ≡ λ[A'],M'.
assert (forall a b c, a ≡ b -> λ[c], a ≡ λ[c], b).
induction 1; eauto.
assert (forall a b c, a ≡ b -> λ[a], c ≡ λ[b], c).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betac_La.

Lemma Betas_Pi : forall A A' B B', A →→ A' -> B →→ B' -> Π(A),B →→ Π(A'),B'.
assert (forall a b c , a →→ b -> Π (c), a →→ Π(c), b).
induction 1; eauto.
assert (forall a b c, a →→ b -> Π(a), c →→ Π(b), c).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betas_Pi.

Lemma Betac_Pi : forall A A' B B', A ≡ A' -> B ≡ B' -> Π(A),B ≡ Π(A'),B'.
assert (forall a b c , a ≡ b -> Π(c), a ≡ Π(c), b).
induction 1; eauto.
assert (forall a b c, a ≡ b -> Π(a), c ≡ Π(b), c).
induction 1; eauto.
eauto.
Qed.

Hint Resolve Betac_Pi.


Lemma Beta_beta : forall M N P n,  M → N ->  M[n←P] → N[n←P] .
intros.
generalize n.
induction H; intros; simpl; intuition.
rewrite (subst_travers).
replace (n0+1) with (S n0).
constructor.
rewrite plus_comm. trivial.
Qed.

(** Some "inversion" lemmas : 
 - a variable/sort cannot reduce at all
 - a pi/lam can only reduce to another pi/lam
 - ...
*)
Lemma Betas_V : forall x N, #x →→ N -> N = #x.
intros. remember #x as X; induction H; trivial.
subst; inversion H.
transitivity N. apply IHBetas2. rewrite <- HeqX; intuition. intuition.
Qed.


Lemma Betas_S : forall s N, !s →→ N -> N = !s.
intros. remember !s as S; induction H; trivial.
subst; inversion H.
transitivity N. apply IHBetas2. rewrite <- HeqS; intuition. intuition.
Qed.


Lemma Betas_Pi_inv : forall A B N, Π(A), B →→ N -> 
  exists C, exists D, N = Π(C), D /\ A →→ C /\ B →→ D.
intros.
remember (Π(A), B) as P. revert A B HeqP; induction H; intros; subst; eauto.
inversion H; subst; clear H.
exists A; exists B'; intuition.
exists A'; exists B; intuition.
destruct (IHBetas1 A B) as (C' & D' & ?); intuition.
destruct (IHBetas2 C' D') as (C'' & D'' &?); intuition.
exists C''; exists D''; eauto.
Qed.


(** Lift properties.*)
Lemma Beta_lift: forall M N  n m, M → N -> M ↑ n # m → N ↑ n # m .
intros.
generalize n m; clear n m.
induction H; intros; simpl; eauto.
change m with (0+m).
rewrite substP1.
constructor.
Qed.


Lemma Betas_lift : forall M N n m , M →→ N -> M ↑ n # m →→ N ↑ n # m .
intros.
induction H.
constructor.
constructor; apply Beta_lift; intuition.
apply Betas_trans with (N:= N ↑ n # m ); intuition.
Qed.



Lemma Betac_lift : forall M N n m, M ≡ N -> M ↑ n # m ≡ N ↑ n # m .
intros.
induction H.
constructor.
apply Betas_lift; trivial.
apply Betac_sym; trivial.
apply Betac_trans with (N ↑ n # m); trivial.
Qed.

Hint Resolve Beta_lift Betas_lift Betac_lift.


(** Subst properties.*)
Lemma Betas_subst : forall M P P' n, P →→ P' -> M [n←P] →→ M[n← P']. 
induction M; intros; simpl; eauto.
destruct (lt_eq_lt_dec v n); intuition.
Qed.

Hint Resolve Betas_subst.

Lemma Betas_subst2 : forall M N P n, M →→ N -> M [n← P] →→ N [n ← P].
induction 1; eauto.
constructor. apply Beta_beta; intuition.
Qed.


Hint Resolve Betas_subst2.

Lemma Betac_subst : forall M P P' n, P ≡ P' -> M[n←P] ≡ M [n←P'].
induction M; simpl; intros; intuition.
destruct (lt_eq_lt_dec v n); intuition.
Qed.

Lemma Betac_subst2 : forall M N P n, 
  M ≡ N -> M[n←P] ≡ N[n← P] .
induction 1; eauto.
Qed.

Hint Resolve Betac_subst Betac_subst2.


(** ** Parallel Reduction
We use the parallel reduction to prove that [Beta] is confluent.*)
Reserved Notation "M →' N" (at level 80).

(** Beta parallel definition. *)
Inductive Betap : Term -> Term -> Prop :=
 | Betap_sort : forall s          , !s →' !s
 | Betap_var  : forall x          , #x →' #x
 | Betap_lam  : forall A A' M M'  , A →' A' -> M →' M' -> λ[A],M →' λ[A'],M'
 | Betap_pi   : forall A A' B B'  , A →' A' -> B →' B' -> Π(A),B →' Π(A'),B'
 | Betap_app  : forall M M' N N'  , M →' M' -> N →' N' -> M · N  →' M' · N'
 | Betap_head : forall A M M' N N', M →' M' -> N →' N' -> (λ[A],M)· N →' M'[← N']
where "M →' N" := (Betap M N) : UT_scope.


Notation "m →' n" := (Betap m n) (at level 80) : UT_scope.

Hint Constructors Betap.

Lemma Betap_refl : forall M, M →' M.
induction M; eauto.
Qed.

Hint Resolve Betap_refl.

(** Lift and Subst property of [Betap].*)
Lemma Betap_lift: forall M N n m, M →' N -> M ↑ n # m →' N ↑ n # m .
intros.
revert n m.
induction H; simpl; intuition.
change m with (0+m).
rewrite substP1.
constructor; intuition.
Qed.

Hint Resolve Betap_lift.

Lemma Betap_subst:forall M M' N N' n, M →' M'  -> N →' N' -> M[n←N] →' M'[n←N'].
intros. revert n.
induction H; simpl; intuition.
destruct lt_eq_lt_dec; intuition.
rewrite subst_travers. replace (S n) with (n+1) by (rewrite plus_comm; trivial). constructor; intuition.
Qed.

Hint Resolve Betap_subst.

(** [Betap] has the diamond property. *)
Lemma Betap_diamond : forall M N P,
   M →' N -> M →' P -> exists Q, N →' Q /\ P →' Q. 
intros.
revert P H0.
induction H; intros.
(**)
exists P; intuition.
(**)
exists P; intuition.
(**)
inversion H1; subst; clear H1.
destruct (IHBetap1 A'0 H4) as (A'' & ? & ?).
destruct (IHBetap2 M'0 H6) as (M'' & ?& ?).
exists (λ[A''],M''); intuition. 
(**)
inversion H1; subst; clear H1.
destruct (IHBetap1 A'0 H4) as (A'' & ? & ?).
destruct (IHBetap2 B'0 H6) as (B'' & ?& ?).
exists (Π(A''), B''); intuition. 
(**)
inversion H1; subst; clear H1.
destruct (IHBetap1 M'0 H4) as (M'' & ?& ?).
destruct (IHBetap2 N'0 H6) as (N'' & ?& ?).
exists (M'' · N''); intuition.
inversion H; subst; clear H.
destruct (IHBetap2 N'0 H6) as (N'' & ?& ?).
destruct (IHBetap1 (λ[A],M'0)) as  (L & ?& ?); intuition.
inversion H2; subst; clear H2; inversion H5; subst; clear H5.
exists ( M' [ ← N'']); intuition.
(**)
inversion H1; subst; clear H1.
destruct (IHBetap2 N'0 H6) as (N'' & ?& ?).
inversion H4; subst; clear H4.
destruct (IHBetap1 M'1 H9) as (M'' & ?& ?).
exists (M''[← N'']); intuition.
destruct (IHBetap2 N'0 H7) as (N'' & ?& ?).
destruct (IHBetap1 M'0 H6) as (M'' & ?& ?).
exists (M''[← N'']); intuition.
Qed.


(** Reflexive Transitive closure of [Betap].*)
Reserved Notation " x  →→' y " (at level 80).

Inductive Betaps : Term -> Term -> Prop :=
 | Betaps_refl  : forall M    , M →→' M
 | Betaps_trans : forall M N P, M  →' N -> N  →→' P -> M  →→' P
where " x  →→' y " := (Betaps x y) : UT_scope.

Hint Constructors Betaps.

(** Closure properties to relate [Betaps] and [Betas].*)
Lemma Betas_Betap_closure : forall M N , M →' N -> M →→ N.
induction 1; eauto.
Qed.

Local Hint Resolve Betas_Betap_closure.


Lemma Betas_Betaps_closure : forall M N,  M →→' N -> M →→  N.
induction 1; eauto.
Qed.

Lemma Betap_Beta_closure : forall M N, M → N -> M →' N.
induction 1; intuition.
Qed.

Local Hint Resolve Betas_Betaps_closure Betap_Beta_closure.

Lemma Betaps_Beta_closure :forall M N, M → N -> M →→' N.
eauto.
Qed.

Local Hint Resolve Betaps_Beta_closure.

Lemma Betaps_trans2 : forall M N P, M →→' N -> N →→' P  -> M →→' P.
intros. revert P H0; induction H; eauto.
Qed.

Local Hint Resolve Betaps_trans2.

Lemma Betaps_Betas_closure : forall M N , M →→ N -> M →→' N.
induction 1; eauto.
Qed.

Local Hint Resolve Betaps_Betas_closure.

(** [Betas] inherites its diamond property from [Betaps].*)
Lemma sub_diamond_Betaps : 
(   forall M N P, M →' N -> M →'  P -> exists Q, N →'  Q /\ P →' Q )
 -> forall M N P, M →' N -> M →→' P -> exists Q, N →→' Q /\ P →' Q .
intros.
revert N H0. induction H1; eauto. 
intros.
destruct (H M N N0 H0 H2) as (Q & ?& ?).
destruct (IHBetaps Q H3) as (Q'' & ? & ?).
exists Q''; eauto.
Qed.



Lemma diamond_Betaps : 
( forall M N P, M →'  N -> M →'  P -> exists Q, N →'  Q /\ P →'  Q)  ->
  forall M N P, M →→' N -> M →→' P -> exists Q, N →→' Q /\ P →→' Q .
intros.  revert P H1.
induction H0; intros; eauto.
destruct (sub_diamond_Betaps H M N P0 H0 H2) as (Q & ? & ?).
destruct (IHBetaps Q H3) as (Q'' & ?& ?). 
exists Q'';eauto.
Qed.


Theorem Betas_diamond: 
  forall M N P, M →→ N -> M →→ P -> exists Q, N →→ Q /\ P →→ Q.
intros.
destruct (diamond_Betaps Betap_diamond M N P) as (Q & ?& ?); intuition.
exists Q; intuition.
Qed.


(** So [Beta] is confluent.*)
Theorem Betac_confl : forall M N, M ≡ N -> exists Q, M →→ Q /\ N →→ Q.
induction 1; eauto. destruct IHBetac as (Q & ? &? ); eauto.
destruct IHBetac1 as (Q1 & ? &? ), IHBetac2 as (Q2 & ? & ?).
destruct (Betas_diamond N Q1 Q2) as (Q'' & ?& ?); trivial.
exists Q''; eauto.
Qed.

(** Some consequences:
 - convertible sorts are equals
 - converitble vars are equals
 - Pi-types are Injective
 - Pi and sorts are not convertible
 *)
Lemma conv_sort : forall s t, !s ≡ !t -> s = t.
intros.
apply Betac_confl in H. destruct H as (z & ?& ?).
apply Betas_S in H.
apply Betas_S in H0.
rewrite H in H0.
injection H0; trivial.
Qed.

Lemma conv_to_sort : forall s T, !s ≡ T ->  T →→ !s.
intros.
apply Betac_confl in H.
destruct H as (z & ?& ?). 
apply Betas_S in H.
subst. trivial.
Qed.

Lemma conv_var : forall x y, #x ≡ #y -> x = y.
intros.
apply Betac_confl in H. destruct H as (z & ?& ?).
apply Betas_V in H. apply Betas_V in H0.
rewrite H in H0.
injection H0; trivial.
Qed.


Lemma conv_to_var : forall x T , #x ≡ T -> T →→ #x.
intros.
apply Betac_confl in H.
destruct H as (z & ?& ?).
apply Betas_V in H.
subst; trivial.
Qed.



(* Pi is injective *)
Theorem PiInj : forall A B C D, Π(A), B ≡ Π(C), D ->  A ≡ C /\ B ≡ D.
intros.
apply Betac_confl in H. destruct H as (z & ? & ?).
apply Betas_Pi_inv in H.
apply Betas_Pi_inv in H0.
destruct H as (c1 & d1 & ? & ? & ?). 
destruct H0 as (c2 & d2 & ? & ?& ?).
rewrite H0 in H; injection H; intros; subst; split; eauto.
Qed.


Lemma Betac_not_Pi_sort : forall A B s, ~ (Π(A), B ≡ !s ).
intros; intro. apply Betac_sym in H. apply conv_to_sort in H.
apply Betas_Pi_inv in H as (C & D & ? & ? & ?). discriminate.
Qed.


End ut_red_mod.
