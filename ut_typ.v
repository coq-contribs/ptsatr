(** Typing rules for standard PTS.*)
Require Import ut_term.
Require Import ut_red.
Require Import ut_env.
Require Import base.
Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt Plus Minus.

Module ut_typ_mod (X:term_sig) (Y:pts_sig X) (TM: ut_term_mod X) (EM: ut_env_mod X TM) (RM: ut_red_mod X TM).
  Import X Y TM EM RM.

(** Typing judgements:*)
Reserved Notation "Γ ⊢ t : T" (at level 80, t, T at level 30, no associativity) .
Reserved Notation "Γ ⊣ " (at level 80, no associativity).

Inductive wf : Env -> Prop :=
 | wf_nil  : nil ⊣
 | wf_cons : forall Γ A s, Γ ⊢ A : !s -> A::Γ ⊣
where "Γ ⊣" := (wf Γ) : UT_scope
with typ : Env -> Term -> Term -> Prop :=
 | cSort : forall Γ s t, Ax s t -> Γ ⊣ -> Γ  ⊢ !s : !t
 | cVar  : forall Γ A v, Γ ⊣ -> A ↓ v  ⊂ Γ -> Γ ⊢ #v : A 
 | cPi   : forall Γ A B s t u, Rel s t u -> Γ ⊢ A : !s -> A::Γ ⊢ B : !t -> 
   Γ ⊢  Π(A), B : !u 
 | cLa   : forall Γ A B M s1 s2 s3, Rel s1 s2 s3 -> Γ ⊢ A : !s1 -> 
   A::Γ ⊢ B : !s2 -> A::Γ ⊢ M : B -> Γ ⊢ λ[A], M : Π(A), B
 | cApp  : forall Γ M N A B , Γ ⊢ M : Π(A), B -> Γ ⊢ N : A -> Γ ⊢ M · N : B[←N]
 | Cnv   : forall Γ M A B s, A ≡ B  -> Γ ⊢ M : A -> Γ ⊢ B : !s -> Γ ⊢ M : B
where "Γ ⊢ t : T" := (typ Γ t T) : UT_scope.

Hint Constructors wf typ.

Open Scope UT_scope.

(* begin hide *)
Scheme typ_ind' := Induction for typ Sort Prop
      with wf_ind' := Induction for wf Sort Prop.

Combined Scheme typ_induc from typ_ind', wf_ind'.
(* end hide *)

(** Basic properties of PTS.
  Context Validity: if a judgment is valid, its context is well-formed.*)
Lemma wf_typ : forall Γ t T, Γ ⊢ t : T -> Γ ⊣.
induction 1; eauto.
Qed.

Hint Resolve wf_typ.

(** Inversion Lemmas , one for each kind of term 
  from a typing derivation of some particular term, we can 
infer informations about its type and subterms.*)

Lemma gen_sort : forall Γ s T, Γ ⊢ !s : T -> exists t, T ≡ !t /\ Ax s t.
intros. remember !s as S. revert s HeqS. induction H; intros; subst; try discriminate.
injection HeqS; intros; subst; clear HeqS. exists t; intuition.
destruct (IHtyp1 s0) as (t & ? & ?); trivial. exists t; split.
eauto. trivial.
Qed.


Lemma gen_var : forall Γ x A, Γ ⊢ #x : A -> exists A', A ≡ A' /\ A' ↓ x ⊂ Γ .
intros. remember #x as X. revert x HeqX. induction H; intros; subst; try discriminate.
injection HeqX; intros; subst; clear HeqX.
exists A; intuition.
destruct (IHtyp1 x) as (A' & ? & ?); trivial. exists A'; split. eauto. trivial.
Qed.

Lemma gen_pi : forall Γ A B T, Γ ⊢ Π(A),B : T -> exists s1, exists s2, exists s3, 
    T ≡ !s3 /\ Rel s1 s2 s3 /\ Γ ⊢ A : !s1  /\ A::Γ ⊢ B : !s2 .
intros. remember (Π(A),B) as P. revert A B HeqP. induction H; intros; subst; try discriminate.
clear IHtyp1 IHtyp2. injection HeqP; intros; subst; clear HeqP.
exists s; exists t; exists u; intuition.
destruct (IHtyp1 A0 B0) as (a & b & c & ? & ? & ? &  ?); trivial. exists a; exists b; exists c; split.
eauto. intuition.
Qed.


Lemma gen_la : forall Γ A M T, Γ ⊢ λ[A],M : T -> exists s1, exists s2, exists s3, exists B, 
    T ≡ Π(A), B /\ Rel s1 s2 s3 /\ Γ ⊢ A : !s1 /\ A::Γ ⊢ M : B /\ A::Γ ⊢ B : !s2.
intros. remember (λ[A],M) as L. revert A M HeqL. induction H; intros ; subst; try discriminate.
clear IHtyp1 IHtyp2 IHtyp3. injection HeqL; intros; subst; clear HeqL.
exists s1; exists s2; exists s3; exists B; intuition.
destruct (IHtyp1 A0 M0) as (a & b & c & D &? &? & ? & ? & ?); trivial.
exists a; exists b; exists c; exists D; split. eauto. intuition.
Qed.

Lemma gen_app : forall Γ M N T, Γ ⊢ M · N : T -> exists A, exists B, T ≡ B[← N] /\ Γ ⊢ M : Π(A),B /\ Γ ⊢ N : A.
intros. remember (M·N) as A. revert M N HeqA. induction H; intros; subst; try discriminate.
clear IHtyp1 IHtyp2. injection HeqA; intros; subst; clear HeqA.
exists A; exists B; intuition.
destruct (IHtyp1 M0 N) as (K & L & ? & ?& ?); trivial. exists K; exists L; split.
eauto. intuition.
Qed.

(** Weakening Property: if a judgement is valid, we can insert a well-typed term
  in the context, it will remain valid. This is where the type checking for 
  inserting items in a context is done.*)
Theorem weakening: (forall Δ M T, Δ ⊢ M : T -> forall Γ A s n Δ', ins_in_env Γ A n Δ Δ' ->   Γ ⊢ A : !s -> 
                 Δ' ⊢ M ↑ 1 # n : T ↑ 1 # n ) /\
(forall Γ, Γ ⊣ -> forall Δ Γ' n A , ins_in_env Δ A n Γ Γ' -> forall s, Δ ⊢ A : !s -> Γ' ⊣).
apply typ_induc; simpl in *; intros.
(*1*)
eauto.
(*2*)
destruct (le_gt_dec n v).
constructor. eapply H; eauto. destruct i as (AA & ?& ?). exists AA; split. rewrite H2.
change (S (S v)) with (1+ S v). rewrite liftP3; simpl; intuition. eapply ins_item_ge. apply H0. trivial. trivial.
constructor. eapply H; eauto.  eapply ins_item_lift_lt. apply H0. trivial. trivial.
(*3*)
econstructor. apply r. eauto. eapply H0. constructor; apply H1. apply H2.
(*4*)
econstructor. apply r. eapply H; eauto. eapply H0; eauto. eapply H1; eauto.
(*5*)
change n with (0+n). rewrite substP1. simpl.
econstructor. eapply H; eauto. eapply H0; eauto.
(*6*)
apply Cnv with (A↑ 1 # n) s; intuition.
eapply H; eauto. eapply H0; eauto.
(* wf *)
inversion H; subst; clear H.
apply wf_cons with s; trivial.
(**)
inversion  H0; subst; clear H0.
apply wf_cons with s0; trivial. 
apply wf_cons with s; trivial. change !s with !s ↑ 1 # n0.
eapply H.  apply H6. apply H1.
Qed.


Theorem thinning :
   forall Γ M T A s,
      Γ ⊢ M : T -> 
   Γ ⊢ A : !s ->
   A::Γ ⊢ M ↑ 1 : T ↑ 1.
intros.
destruct weakening.
eapply H1. apply H. constructor. apply H0.
Qed.

Theorem thinning_n : forall n Δ Δ',
   trunc n Δ Δ' ->
   forall M T , Δ' ⊢ M : T  -> Δ ⊣ ->
               Δ ⊢ M ↑ n : T ↑ n.
intro n; induction n; intros.
inversion H; subst; clear H.
rewrite 2! lift0; trivial.
inversion H; subst; clear H.
change (S n) with (1+n).
replace (M ↑ (1+n)) with ((M ↑ n )↑ 1) by (apply lift_lift).
replace (T ↑ (1+n)) with ((T ↑ n) ↑ 1) by (apply lift_lift).
inversion H1; subst; clear H1.
apply thinning with s; trivial.
eapply IHn. apply H3. trivial. eauto.
Qed.


(** Substitution Property: if a judgment is valid and we replace a variable by a
  well-typed term of the same type, it will remain valid.*)
(* begin hide *)
Lemma sub_trunc : forall Δ a A n Γ Γ', sub_in_env Δ a A n Γ Γ' -> trunc n Γ' Δ.
induction 1.
apply trunc_O.
apply trunc_S. trivial.
Qed.
(* end hide *)

Theorem substitution : (forall Γ M T , Γ  ⊢ M : T  -> forall Δ P A, Δ  ⊢ P : A -> 
 forall Γ' n , sub_in_env Δ P A n Γ Γ' -> Γ ⊣  -> Γ' ⊢ M [ n ←P ]  : T [ n ←P ] ) /\
                       (forall Γ ,  Γ ⊣ -> forall Δ P A n Γ' , Δ ⊢ P : A ->  
  sub_in_env  Δ P A n Γ Γ' ->  Γ' ⊣).
apply typ_induc; simpl; intros.
(*1*)
eauto.
(*2*)
destruct lt_eq_lt_dec as [ [] | ].
constructor. eapply H; eauto. eapply nth_sub_item_inf. apply H1. intuition. trivial.
destruct i as (AA & ?& ?). subst. rewrite substP3; intuition. 
rewrite <- (nth_sub_eq H1 H4). eapply thinning_n. eapply sub_trunc. apply H1. trivial.
eapply H; eauto. constructor. eapply H; eauto. destruct i as (AA & ? &?). subst.
rewrite substP3; intuition. exists AA; split. replace (S (v-1)) with v. trivial.
rewrite minus_Sn_m. intuition. destruct v. apply lt_n_O in l; elim l. intuition.
eapply nth_sub_sup. apply H1. destruct v. apply lt_n_O in l; elim l. simpl. rewrite <- minus_n_O.
intuition. rewrite <- pred_of_minus. rewrite <- (S_pred v n l). trivial.
(*4*)
econstructor. apply r. eapply H; eauto. eapply H0; eauto.
(*5*)
econstructor. apply r. eapply H; eauto. eapply H0; eauto. eapply H1; eauto.
(*6*)
rewrite subst_travers. econstructor.
replace (n+1) with (S n) by (rewrite plus_comm; trivial). eapply H; eauto.
replace (n+1) with (S n) by (rewrite plus_comm; trivial). eapply H0; eauto.
(*7*)
econstructor.  apply Betac_subst2. apply b. eapply H; eauto. eapply H0; eauto.
(* wf *)
inversion H0.
inversion H1; subst; clear H1. eauto.
econstructor. eapply H. apply H0. trivial. eauto. 
Qed.

(** Well-formation of contexts: if a context is valid, every term inside
  is well-typed by a sort.*)
Lemma wf_item : forall Γ A n, A ↓ n ∈ Γ ->
   forall  Γ', Γ ⊣ ->  trunc (S n) Γ Γ' -> exists s, Γ' ⊢ A : !s.
induction 1; intros.
inversion H0; subst; clear H0.
inversion H5; subst; clear H5.
inversion H; subst.
exists s; trivial.
inversion H1; subst; clear H1.
inversion H0; subst.
apply IHitem; trivial. eauto. 
Qed.

Lemma wf_item_lift : forall Γ A n ,Γ ⊣  -> A ↓ n ⊂ Γ ->
  exists s,  Γ ⊢ A  : !s.
intros.
destruct H0 as (u & ? & ?).
subst.
assert (exists Γ' , trunc (S n) Γ Γ') by (apply item_trunc with u; trivial).
destruct H0 as (Γ' & ?).
destruct (wf_item Γ u n H1 Γ' H H0) as (t &  ?).
exists t. change !t with (!t ↑(S n)).
eapply thinning_n. apply H0. trivial. trivial.
Qed.

(** Type Correction: if a judgment is valid, the type is either welltyped
  itself, or syntacticaly a sort. This distinction comes from the fact
  that we abstracted the typing of sorts with [Ax] and that they may be some
  untyped sorts (also called top-sorts).*)
Theorem TypeCorrect : forall Γ M T, Γ ⊢ M : T  -> 
 (exists s, T = !s) \/ (exists s, Γ ⊢ T : !s).
intros; induction H.
(*1*)
left; exists t; reflexivity.
(*2*)
apply wf_item_lift in H0. right; trivial. trivial.
(*4*)
left; exists u; trivial.
(*5*)
right; exists s3; apply cPi with s1 s2; trivial.
(*6*)
destruct IHtyp1. destruct H1; discriminate. destruct H1 as (u & ?).
apply gen_pi in H1 as (s1 & s2 & s3 & h); decompose [and] h; clear h.
right; exists s2.
change (!s2) with (!s2 [← N]). eapply substitution. apply H5. apply H0. constructor.
eauto.
(*8*)
right; exists s; trivial.
Qed.

End ut_typ_mod.
