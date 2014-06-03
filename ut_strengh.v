(** * Strenghthening 
The Strenghthening property is about getting rid of useless hypothesis:
  if [Γ(x:A)Γ' ⊢ M : T] and [x] does not appear in [M] or [T], then 
     [ΓΓ' ⊢ M : T].*)
(** This is true for all PTS, but the proof is quite subtle. This formalization
has been done from a paper for Jutting in 1993.


The following is not usefull for the proof PTS <-> PTSe 
but it's still an interesting part of the metatheory of PTSs 

*)
Require Import base.
Require Import ut_term.
Require Import ut_red.
Require Import ut_env.
Require Import ut_typ.
Require Import ut_sr. 
Require Import List Le Lt Gt.

Unset Standard Proposition Elimination Names.

Module ut_strengh_mod (X:term_sig) (Y:pts_sig X) (TM:ut_term_mod X) (EM:ut_env_mod X TM) (RM: ut_red_mod X TM).
 Include (ut_sr_mod X Y TM EM RM).
  Import X Y TM EM RM.

Open Scope UT_scope.

(**
Tv Ts and Sigma are notation find in Jutting93 


 We do a partition of [Term] in two families, one build around
vars and the other around sorts and Pi-types.*)
Inductive Tv : Term -> Prop :=
 | Tv_intro : forall x, Tv #x
 | Tv_la: forall M A, Tv M -> Tv (λ[A],M)
 | Tv_app :forall M N, Tv M -> Tv (M·N)
.

Inductive Ts : Term -> Prop :=
 | Ts_intro : forall s, Ts !s
 | Ts_pi : forall A B, Ts (Π(A),B)
 | Ts_la : forall A M, Ts M -> Ts (λ[A],M)
 | Ts_app : forall M N, Ts M -> Ts (M·N)
.

(** Telescopes are just a way to talk about n-ary Lam/Pi -terms: *)
(** Tels (A1,...,An)M ::= Π(A1),...,Π(An),M *)
Fixpoint Tels (Γ : Env) (M : Term) {struct Γ } : Term :=
 match Γ with
 | nil => M
 | cons A Δ => Π(A),(Tels Δ M)
end.

Fixpoint Tels' (Γ : Env) (M : Term) {struct Γ } : Term :=
 match Γ with
 | nil => M
 | cons A Δ => λ[A],(Tels' Δ M)
end.


Hint Constructors Tv Ts.

Require Import Compare_dec Peano_dec.
(** Some basic properties of [Tv] and [Ts]. *)
Lemma Tv_lift : forall M n m, Tv M <-> Tv (M ↑ n # m).
induction M; split; simpl in *; intros; intuition.
destruct le_gt_dec; intuition.
inversion  H; subst; clear H. constructor. eapply IHM1. trivial.
inversion  H; subst; clear H. constructor. eapply IHM1. apply H1.
inversion H. inversion H.
inversion  H; subst; clear H. constructor. eapply IHM2. trivial.
inversion  H; subst; clear H. constructor. eapply IHM2. apply H1.
Qed.

Lemma Ts_lift : forall M n m, Ts M <-> Ts (M ↑ n # m).
induction M; split; simpl in *; intros; intuition.
inversion H. destruct le_gt_dec; inversion H.
inversion  H; subst; clear H. constructor. eapply IHM1. trivial.
inversion  H; subst; clear H. constructor. eapply IHM1. apply H1.
inversion  H; subst; clear H. constructor. eapply IHM2. trivial.
inversion  H; subst; clear H. constructor. eapply IHM2. apply H1.
Qed.

Lemma Tx_ok : forall t, Tv t \/ Ts t.
induction t; intros.
left; trivial.
right; trivial.
destruct IHt1.
left; constructor; trivial.  right; constructor; trivial.
right; trivial.
destruct IHt2.
left; constructor; trivial.  right; constructor; trivial.
Qed.


Lemma fun_item_lift : forall A A' v Γ , A ↓ v ⊂ Γ -> A' ↓ v ⊂ Γ -> A = A'.
intros.
destruct H as (x & ?& ?). destruct H0 as (x' & ?& ?).
subst. replace x' with x. trivial. eapply fun_item. apply H1. apply H2.
Qed.

(** First result: if a term is in [Tv], then all of his types are convertible. *)
Theorem Shape_of_Type_Tv : forall Γ M A , Γ ⊢ M : A -> forall A',  Γ ⊢ M : A' -> Tv M ->  A ≡ A'.
induction 1; intros.
inversion H2.
(**)
apply gen_var in H1 as (B & ? &?).
replace A with B. intuition. eapply fun_item_lift. apply H3. trivial.
(**)
inversion H3; subst; clear H3.
(**)
inversion H4; subst; clear H4.
apply gen_la in H3 as (t1 & t2 & t3 & D & h); decompose [and] h;clear h.
eapply Betac_trans. eapply Betac_Pi. apply Betac_refl. eapply IHtyp3. apply H7. trivial.
intuition.
(**)
inversion H2; subst; clear H2.
apply gen_app in H1 as (C & D & ? & ?& ?).
destruct (PiInj A B C D). apply IHtyp1. trivial. trivial.
eapply Betac_trans. eapply Betac_subst2. apply H6. intuition.
(**)
eauto.
Qed.

(** Some properties over [Tels] (reduction, substitutions, ...). *)
Lemma Beta_Tels_inv : forall Γ M N, Tels Γ M  → N -> (exists Γ', N = Tels Γ' M /\ Γ →e Γ') \/ 
  (exists M', N = Tels Γ M' /\ M → M').
induction Γ; intros; simpl in *.
right. exists N; intuition.
inversion H; subst; clear H.
destruct (IHΓ M B' H3). destruct H as (Γ' & -> & ?).
left. exists (a::Γ'); intuition.
destruct H as (M' & -> & ?).
right. exists M'; intuition.

left. exists (A'::Γ); intuition.
Qed.


Lemma Betas_Tels_inv : forall Γ M N, Tels Γ M →→ N -> exists Γ', exists M', N = Tels Γ' M' /\ Γ →→e Γ' /\ M →→ M'.
intros.
remember (Tels Γ M) as MM. revert Γ M HeqMM.
induction H; intros; subst.
exists Γ; exists M0; intuition.
apply Beta_Tels_inv in H.
destruct H. destruct H as (Γ' & -> & ?).
exists Γ'; exists M0; intuition.
destruct H as (M0' & -> & ?).
exists Γ; exists M0'; intuition.
destruct (IHBetas1 Γ M0) as (Γ' & M' & -> & ?& ?); trivial.
destruct (IHBetas2 Γ' M') as (Γ'' & M'' & -> & ?& ?); trivial.
exists Γ''; exists M''; eauto.
Qed.


Lemma Betas_Tels : forall Γ Γ' M M', Γ →→e Γ' -> M →→ M' -> Tels Γ M →→ Tels Γ' M'.
assert (forall l l', l →→e l' -> forall t ,  Tels l t →→ Tels l' t).
induction 1; intros; eauto.
induction H; simpl; eauto.
assert (forall t t', t →→ t' -> forall l ,  Tels l t →→ Tels l t').
induction 1; intros; eauto.
induction l; simpl; eauto.
intros.
eauto.
Qed.

Lemma Betas_not_Pi_to_Sort : forall A B s,  ~ (Π (A), B →→ !s).
intros; intro. eapply Betac_not_Pi_sort. constructor. apply H.
Qed.


Fixpoint env_subst Γ n N {struct Γ} := match Γ with
 | nil => nil 
 | A::Γ' => (A[n ← N]) :: (env_subst Γ' (S n) N)
end.

Notation "E  [[ n ← N ]]" := (env_subst E n N) (at level 80).

Lemma Tels_subst : forall Γ M n N, (Tels Γ M) [n ← N] = Tels (Γ [[n ← N]]) (M [(length Γ + n) ← N]).
induction Γ; simpl; intros.
trivial.
rewrite IHΓ.
rewrite plus_n_Sm. trivial.
Qed.


Lemma Tels'_subst : forall Γ M n N, (Tels' Γ M) [n ← N] = Tels' (Γ [[n ← N]]) (M [(length Γ + n) ← N]).
induction Γ; simpl; intros.
trivial.
rewrite IHΓ.
rewrite plus_n_Sm. trivial.
Qed.

(** Second Results: if a term is in [Ts], then all of its types are almost
  convertible: they all reduce to a telescope that ends with a sort, 
  and the body of the telescope is the same for everyone (but not the final
  sort.*)
Theorem Shape_of_Type_Ts : forall Γ M T,  Γ ⊢ M : T -> forall T', Γ ⊢ M : T' -> Ts M -> 
  exists s, exists s', exists Γ,  T →→ (Tels Γ !s) /\ T' →→ (Tels Γ !s').
induction 1; intros.
apply gen_sort in H1 as (s' & ?& ?).
apply Betac_sym in H1. apply conv_to_sort in H1.
exists t; exists s'; exists nil; simpl; intuition.
(**)
inversion H2.
(**)
clear IHtyp1 IHtyp2.
apply gen_pi in H2 as (s1 & s2 & s3 & h); decompose [and] h; clear h.
apply Betac_sym in H2. apply conv_to_sort in H2.
exists u; exists s3; exists nil; simpl; intuition.
(**)
inversion H4; subst; clear H4.
apply gen_la in H3 as (t1 & t2 & t3 & D & h); decompose [and] h; clear h.
destruct (IHtyp3 D H7 H6) as (u & v & l & ?& ?).
apply Betac_confl in H3 as (Z & ? &?).
apply Betas_Pi_inv in H11 as (K & L & -> & ? & ?).
destruct (Betas_diamond  D L (Tels l !v)) as ( Z & ?& ?); trivial.
apply Betas_Tels_inv in H14 as (l'' & ? & -> & ? &?).
apply Betas_S in H15; subst.
exists u; exists v; exists (K::l''); split.
apply Betas_trans with (Tels (A::l) !u). simpl. eauto. simpl.
apply Betas_Pi. trivial. apply Betas_Tels; trivial.
simpl. eauto.
(**)
inversion H2; subst; clear H2. clear IHtyp2.
apply gen_app in H1 as (C & D & ? & ?&  ?). destruct (IHtyp1 ( Π (C),D) ) as (u & v & l & ? & ?); trivial.
clear IHtyp1. destruct l; simpl in *. apply Betas_not_Pi_to_Sort in H5; elim H5.
apply Betas_Pi_inv in H5 as (B0 & A0 & ? & ?& ?). injection H5; intros;subst; clear H5.
apply Betas_Pi_inv in H6 as (D0 & C0 & ? & ?& ?). injection H5; intros;subst; clear H5.
apply Betac_confl in H1 as (Z & ?& ?).
destruct (Betas_diamond (D[←N]) Z ((Tels l !v)[←N]) H5) as (ZZ & ?& ?).
apply Betas_subst2; trivial.  rewrite Tels_subst in H11. simpl in H11.
apply Betas_Tels_inv in H11. destruct H11 as (l' & x & -> & ?& ?). apply Betas_S in H12. subst.
exists u ; exists v; exists l'; split. eapply Betas_trans. apply Betas_subst2.  apply H8.
rewrite Tels_subst. eapply Betas_Tels. trivial. simpl; trivial.
eauto.
(**)
destruct (IHtyp1 T' H2 H3) as (u & v & l & ? & ?).
apply Betac_confl in H as (Z & ? & ?). destruct (Betas_diamond A (Tels l !u) Z H4 H) as (ZZ & ?& ?).
apply Betas_Tels_inv in H7 as (l' & ? & -> & ? & ?). apply Betas_S in H9; subst.
exists u; exists v; exists l'; split.
apply Betas_trans with Z; trivial. apply Betas_trans with (Tels l !v); trivial.
apply Betas_Tels; trivial.
Qed.

(** Definition of the set [Sigma] for terms in [Ts]. It's almost the set
of all possible sorts that may appear at the end of the telescope, but 
that not totally true, just a hint.*)
Inductive Sigma : Env -> Term -> Sorts -> Prop :=
 | Sigma_sorts : forall Γ s s', Ax s s' -> Sigma Γ !s s'
 | Sigma_pi : forall Γ A B s t u, Rel s t u ->
   ( Tv A -> Γ ⊢ A : !s) -> (Ts A -> Sigma Γ A s) ->
   ( Tv B -> A::Γ ⊢ B : !t) -> (Ts B -> Sigma (A::Γ) B t) -> Sigma Γ (Π(A),B) u
 | Sigma_la : forall Γ A M s, Sigma (A::Γ) M s -> Sigma Γ (λ[A],M) s
 | Sigma_app : forall Γ M N s, Sigma Γ M s -> Sigma Γ (M· N) s.

Hint Constructors Sigma.
(** Some handy functions.*)
Lemma Tels_tool : forall Γ Γ' s t, Tels Γ !s →→ Tels Γ' !t -> s = t /\ length Γ = length Γ'.
induction Γ; destruct Γ'; simpl in *; intros.
apply Betas_S in H. injection H; intros; subst; intuition.
apply Betas_S in H; discriminate.
apply Betas_not_Pi_to_Sort in H; elim H.
apply Betas_Pi_inv in H as ( C & D & ? & ? & ?). injection H ; intros; subst; clear H.
destruct (IHΓ Γ' s t0 H1). subst; intuition. 
Qed.

Lemma ins_in_env_Sigma : forall a T Δ A n Γ Γ' sa, Γ ⊢ a : T -> Δ ⊢ A : !sa -> Ts a -> ins_in_env Δ A n Γ Γ' -> 
  forall s , Sigma Γ a s <-> Sigma Γ' (a↑1#n) s.
induction a; intros; simpl in *.
(**)
inversion H1.
(**)
split; intros. inversion H3; subst; clear H3. intuition. inversion H3; subst; clear H3. intuition.
(**)
inversion H1; subst; clear H1. apply gen_app in H  as ( C & D & ? & ?& ?). 
destruct (IHa1 (Π(C),D) Δ A n Γ Γ' sa H1 H0 H4 H2 s).
split; intros. inversion H7; subst; clear H7. intuition.  inversion H7; subst; clear H7. intuition.
(**)
apply gen_pi in H as (u & v & w & ? & ? & ? & ?).
split; intros. inversion H6; subst; clear H6. econstructor. apply H9. 
intros. apply Tv_lift in H6. change !s0 with (!s0 ↑ 1 # n). eapply weakening. apply (H10 H6). apply H2. apply H0. 
intros. apply Ts_lift in H6. eapply IHa1. apply H4. apply H0. trivial. apply H2. intuition.
intros. apply Tv_lift in H6. change !t with (!t ↑ 1 # (S n)). eapply weakening. apply (H13 H6). constructor; apply H2. apply H0.
intros. apply Ts_lift in H6. eapply IHa2. apply H5. apply H0. trivial. constructor; apply H2. intuition.

inversion H6; subst; clear H6. econstructor. apply H9.
intros. replace u with s0 in *. trivial. apply conv_sort. eapply Shape_of_Type_Tv. apply H10. apply Tv_lift. trivial. change !u with (!u ↑ 1 # n).
eapply weakening. apply H4. apply H2. apply H0. apply Tv_lift; trivial.
intros. eapply IHa1. apply H4. apply H0. trivial. apply H2. apply H11. apply Ts_lift; trivial.
intros. replace v with t in *. trivial. apply conv_sort. eapply Shape_of_Type_Tv. apply H13. apply Tv_lift. trivial. change !v with (!v ↑ 1 # (S n)).
eapply weakening. apply H5. constructor; apply H2. apply H0. apply Tv_lift; trivial.
intros. eapply IHa2. apply H5. apply H0. trivial. constructor; apply H2. apply H15. apply Ts_lift; trivial.
(**)
inversion H1; subst; clear H1. apply gen_la  in H as ( u & v & w &  D & ? & ?& ? & ? & ?). 
destruct (IHa2 D Δ A (S n) (a1::Γ) (a1↑1#n :: Γ') sa H5 H0 H4) with (s := s). constructor; trivial.
split; intros. inversion H9; subst; clear H9. intuition.  inversion H9; subst; clear H9. intuition.
Qed.

Lemma In_Sigma_tool : forall Γ a A, Γ ⊢ a : A -> forall Δ s, Ts a -> A →→ Tels Δ !s -> Sigma Γ a s.
induction 1; intros.
(**)
apply Betas_S in H2. destruct Δ; simpl in H2; try discriminate. injection H2; intros; subst; clear H2.
intuition.
(**)
inversion H1.
(**)
apply Betas_S in H3. destruct Δ; simpl in H3; try discriminate. injection H3; intros; subst; clear H3.
apply Sigma_pi with s t; intros; trivial.
apply IHtyp1 with nil; simpl; intuition. apply IHtyp2 with nil; simpl; intuition.
(**)
inversion H3; subst; clear H3.
apply Betas_Pi_inv in H4 as (A' & ? & ? & ?& ?).
destruct Δ; simpl in H3. discriminate. injection H3; intros; subst; clear H3.
constructor. apply IHtyp3 with Δ; trivial.
(**)
inversion H1; subst; clear H1.
destruct (Shape_of_Type_Ts Γ M (Π(A),B) H (Π(A),B) H H4) as (s' & _ & Θ & ? & _ ).
apply Betas_Pi_inv in H1 as (A' & ? & ? & ?& ?).
destruct Θ; simpl in H1. discriminate. injection H1; intros; subst; clear H1.
replace s with s' in *.
constructor. apply IHtyp1 with (A::Θ); simpl; intuition.
destruct (Betas_diamond (B[← N]) (Tels Δ !s) (Tels Θ !s')[← N] H2) as (Z & ?& ?).
intuition. apply Betas_Tels_inv in H1 as (Δ' & ? & -> & ? & ?).
rewrite Tels_subst in H6. apply Betas_S in H7; subst. simpl in H6.
apply Tels_tool in H6; intuition.
(**)
destruct (Betac_confl A B H) as ( Z  & ?& ?). destruct (Betas_diamond B Z (Tels Δ !s0) H5 H3) as (ZZ & ?& ?).
apply Betas_Tels_inv in H7 as (Θ & ? & -> & ? & ?). apply Betas_S in H8; subst.
eauto.
Qed.

Lemma In_Sigma : forall Γ A s, Γ ⊢ A : !s -> Ts A -> Sigma Γ A s.
intros. apply In_Sigma_tool with !s nil; simpl; trivial.
Qed.


Lemma env_subst_tool : forall Γ n M, length (Γ[[n ← M]]) = length Γ.
induction Γ; simpl in *; intros; intuition.
Qed.


Fixpoint env_subst_down Γ N n {struct Γ } := match Γ with
 | nil => nil 
 | A::Γ' => (A[length Γ' + n ← N]) :: (env_subst_down Γ' N n)
end.

Lemma env_subst_down_app :forall Γ Γ' t n,  env_subst_down (Γ++Γ') t n = (env_subst_down Γ t (length Γ' + n))++(env_subst_down Γ' t n).
induction Γ; simpl in *; intros. trivial.
replace (length (Γ++Γ')+n) with (length Γ + (length Γ' + n)).
rewrite IHΓ. trivial. rewrite app_length. intuition.
Qed.

Lemma env_subst_down_rev : forall Θ t n, rev (Θ [[n ← t]]) = env_subst_down (rev Θ) t n.
induction Θ; simpl in *; intros. trivial.
rewrite env_subst_down_app. rewrite IHΘ. simpl. trivial.
Qed.

Lemma env_subst_down_sub_in_env : forall Θ Γ t A, sub_in_env Γ t A (length Θ) (Θ ++ A :: Γ) (env_subst_down Θ t 0 ++ Γ).
induction Θ; simpl in * ;intros. constructor.
replace (length Θ+0) with (length Θ) by intuition. apply sub_S. trivial.
Qed.

Lemma sub_in_env_rev_append : forall Θ Γ t A ,  sub_in_env Γ t A (length Θ) (rev (A :: Θ) ++ Γ) (rev (Θ [[0 ←t]]) ++ Γ).
intros. rewrite env_subst_down_rev. simpl. rewrite <- app_assoc;  simpl. rewrite <- rev_length. apply env_subst_down_sub_in_env.
Qed.

Lemma Betas_env_length : forall Γ Γ', Γ →→e Γ' -> length Γ = length Γ'.
induction 1; intuition. induction H; simpl; intuition.
rewrite IHBetas_env1. trivial.
Qed.

(** Terms in [Ts] have a particular shape: they are build around sorts and
pi-types, two families of terms that cannot be type by a pi-type. Hence, if an
  application is in [Ts], it will reduce to some lambda-telescope whose head 
is a sort or a pi-team.*)
(** (we don't talk of weak head normal form since not all PTS are normalizing
and we still want to be fully general.*)
Lemma Shape_of_Ts_Term : forall Γ a A, Γ ⊢ a : A -> forall Δ s s1, Ts a -> A →→ Tels Δ !s1 -> Sigma Γ a s -> 
  exists Δ', exists a1, length Δ = length Δ' /\ a →→ Tels' Δ' a1 /\ rev Δ'++Γ ⊢ a1 : !s.
induction 1; intros.
(**)
exists nil; exists !s; simpl; intuition.
destruct Δ; simpl in H2. trivial. apply Betas_S in H2; discriminate.
inversion H3; subst; clear H3. intuition.
(**)
inversion H1.
(**)
replace Δ with (@nil Term) in *. simpl in *.
inversion H4; subst; clear H4.
destruct (Tx_ok A).
  destruct (Tx_ok B).
    exists nil; exists (Π(A),B); simpl; intuition. econstructor. apply H7. trivial. trivial.
    
    destruct (IHtyp2 nil t0 t H5 ) as (Δ' & b & ? & ? & ?). simpl; trivial. intuition.
    replace Δ' with (@nil Term) in *; simpl in *. exists nil; exists (Π(A), b); simpl; intuition.
    econstructor. apply H7. trivial. trivial. destruct Δ'. trivial. discriminate.
  destruct (IHtyp1 nil s2 s) as (Δ' & a & ? & ?& ?). trivial. simpl; trivial. intuition.
  replace Δ' with (@nil Term) in *; simpl in *. destruct (Tx_ok B).
    exists nil; exists (Π(a),B); simpl; intuition. econstructor. apply H7. trivial.
    eapply Betas_env_sound. apply H9. apply Betas_env_comp; intuition.

    destruct (IHtyp2 nil t0 t H12) as (Δ'' & b & ? & ? & ?). simpl; trivial. intuition.
    replace Δ'' with (@nil Term) in *; simpl in *. exists nil; exists (Π(a),b); simpl; intuition.
    econstructor. apply H7. trivial. eapply Betas_env_sound. apply H16. apply Betas_env_comp; intuition.
    destruct Δ''. trivial. discriminate.     destruct Δ'. trivial. discriminate.
    apply Betas_S in H3. destruct Δ. trivial. discriminate.
(**)
inversion H3; subst; clear H3. inversion H5; subst; clear H5. apply Betas_Pi_inv in H4 as (A' & B' & ? & ?& ?).
destruct Δ. discriminate. injection H3; intros; subst; clear H3.
destruct (IHtyp3 Δ s s0 H7 H5 H10) as (Δ' & b' & ? & ? & ?).
exists (A::Δ'); exists b'; simpl; intuition. rewrite <- app_assoc. simpl. trivial.
(**)
inversion H3; subst; clear H3. inversion H1; subst; clear H1.
destruct (Shape_of_Type_Ts Γ M (Π(A),B) H (Π(A),B) H H4) as ( sa & _ & Θ & ? & _ ).
apply Betas_Pi_inv in H1 as (A' & B' & ? & ?& ?). destruct Θ. discriminate.
injection H1; intros; subst; clear H1. replace sa with s1 in *.
destruct (IHtyp1 (A::Θ) s s1 H4) as ( Θ' & m & ? & ? &?). simpl; intuition. trivial.
destruct Θ' as [ | A'' Θ']. discriminate. simpl in H1. injection H1; intros; subst; clear H1.
exists (Θ'[[ 0 ← N]]); exists (m[ (length Θ' )← N]); repeat split.
rewrite env_subst_tool.   destruct (Betas_diamond (B[← N]) (Tels Δ !s1) (Tels Θ !s1)[← N] H2 ) as (Z & ?& ?).
intuition. apply Betas_Tels_inv in H1 as (? & ?& -> & ?& ?).
rewrite Tels_subst in H10. apply Betas_S in H11; subst.
apply Tels_tool in H10 as ( _ & ?). replace (length Δ) with (length x).
rewrite env_subst_tool in H10. rewrite <- H9; intuition. apply Betas_env_length in H1. intuition. apply Betas_trans with ((λ[A''],Tels' Θ' m)· N).
intuition. replace (length Θ') with (length Θ' + 0). rewrite <- Tels'_subst. constructor.
constructor. intuition. assert (A≡ A'' /\ exists s, Γ ⊢ A'' : !s).
assert ( Γ ⊢ λ[A''],Tels' Θ' m : Π(A),B). eapply SubjectRed. apply H. trivial.
  apply gen_la in H1 as ( ss & ? & ? & ? & ? & _ & ? & _ ). split.
  apply PiInj in H1; intuition. exists ss; trivial.
change !s with (!s[ (length Θ') ← N]).   destruct H1 as (? & ss & ?). eapply substitution. apply H7.  eapply Cnv. apply H1. apply H0.
apply H10. apply sub_in_env_rev_append. apply wf_typ in H7; trivial.  destruct (Betas_diamond (B[← N]) (Tels Δ !s1) (Tels Θ !sa)[← N] H2) as (Z & ?& ?).
intuition. apply Betas_Tels_inv in H1 as (Δ' & ? & -> & ? & ?).
rewrite Tels_subst in H6. apply Betas_S in H7; subst. simpl in H6.
apply Tels_tool in H6; intuition.
(**)
destruct (Betac_confl A B H) as (Z & ? & ?). destruct (Betas_diamond B (Tels Δ !s1) Z H3 H6) as (ZZ & ? &?).
apply Betas_Tels_inv in H7 as (? & ? & -> & ? & ?). apply Betas_S in H9; subst.
destruct (IHtyp1 x s0 s1 H2) as ( Δ' & a1 & ? & ? & ?). eauto. trivial.
exists Δ'; exists a1; intuition. rewrite <- H9. apply Betas_env_length in H7. trivial.
Qed.

Lemma Ts_Sigma_Shape : forall Γ A s, Γ ⊢ A : !s -> forall s', Ts A -> Sigma Γ A s' -> exists A', A →→ A' /\ Γ ⊢ A' : !s'.
intros.
destruct (Shape_of_Ts_Term Γ A !s H nil s' s H0) as ( ? & a & ? & ? & ?). simpl; trivial. trivial.
replace x with (@nil Term) in *; simpl in *.
exists a; intuition. destruct x. trivial. discriminate.
Qed.

(* begin hide *)
Lemma L1 : forall Δ Z n Γ0 Γ, ins_in_env Δ Z n Γ0 Γ -> forall v a, n <= v -> a ↓ S v ∈ Γ ->
  a ↓ v ∈ Γ0.
induction 1; intros. inversion H0; subst; clear H0. trivial.
inversion H1; subst; clear H1. destruct v. apply le_Sn_O in H0. contradict H0; intuition.
apply le_S_n in H0. constructor. intuition.
Qed.


Lemma L2 : forall Δ Z n Γ0 Γ, ins_in_env Δ Z n Γ0 Γ -> forall v a, n > v ->  a ↓ v ∈ Γ ->
 exists b, b ↓ v ∈ Γ0 /\ b↑1# (n-S v) = a.
induction 1; intros. unfold gt in H. apply lt_n_O in H; elim H. inversion H1; subst; clear H1.
exists d; intuition. replace (S n - 1) with n by intuition. trivial.
apply lt_S_n in H0. destruct (IHins_in_env n0 a) as ( b & ? & ?). intuition. trivial.
exists b; split. intuition. replace (S n - S (S n0)) with (n - S n0) by intuition.
trivial.
Qed.


Lemma ins_in_env_wf : forall Δ A n Γ Γ', ins_in_env Δ A n Γ Γ' -> Γ' ⊣ -> exists s, Δ ⊢ A : !s.
induction 1; intros.
inversion H; subst; clear H. exists s; trivial.
inversion H0; subst; clear H0. apply wf_typ in H2. intuition.
Qed.
(* \end *)
Lemma Beta_lift_inv : forall a b n m , a ↑ n # m → b -> exists a', a → a' /\  b = a' ↑ n # m .
induction a; intros; simpl in *.
destruct le_gt_dec. inversion H. inversion H. inversion H.
inversion H; subst; clear H. destruct a1; simpl in H1; try discriminate. destruct le_gt_dec ; discriminate.
injection H1; intros; subst; clear H1. exists (a1_2 [ ← a2]); intuition.
change m with (0+m). rewrite <- substP1. simpl; trivial.
apply IHa1 in H3 as ( a' & ?& ->). exists (App a' a2); intuition.
apply IHa2 in H3 as ( a' & ?& ->). exists (App a1 a'); intuition.
inversion H; subst; clear H. apply IHa2 in H3 as (a' & ? & ->). exists (Pi a1 a'); intuition.
apply IHa1 in H3 as (a' & ? & ->). exists (Pi a' a2); intuition.
inversion H; subst; clear H. apply IHa2 in H3 as (a' & ? & ->). exists (La a1 a'); intuition.
apply IHa1 in H3 as (a' & ? & ->). exists (La a' a2); intuition.
Qed.

Lemma Betas_lift_inv : forall a b n m , a ↑ n # m →→ b -> exists a', a →→ a' /\  b = a' ↑ n # m .
intros. remember (lift_rec n m a) as A. revert n m a HeqA.
induction H; intros; subst. exists a; intuition.
apply Beta_lift_inv in H as ( b & ? & ->). exists b; intuition.
destruct (IHBetas1 n m a) as (b & ? & -> ); trivial.
destruct (IHBetas2 n m b) as (c & ? & -> ); trivial.
exists c; intuition; eauto.
Qed.

(* end hide *)
(** To prove strenghthening, we will first prove that if the hypothesis is not
  used in the term, we can safely remove it, but we may need to beta reduce the
term in order to be still valid. *)
Theorem WeakStrenghthening : (forall Γ' M T, Γ' ⊢ M : T -> forall m n Δ A Γ, M = m ↑ 1 # n -> 
  ins_in_env Δ A n Γ Γ' ->  exists T', T →→ T'↑ 1 # n /\ Γ ⊢ m : T' ) /\
  (forall Γ', Γ' ⊣ -> forall n Δ A Γ, ins_in_env Δ A n Γ Γ' -> Γ ⊣).
apply typ_induc; intros.
(**)
destruct m; simpl in H0; try discriminate. destruct le_gt_dec; discriminate. injection H0; intros; subst; clear H0.
exists !t; split; trivial. constructor. trivial. eauto.
(**)
destruct m; simpl in H0; try discriminate. destruct le_gt_dec; injection H0; intros; subst; clear H0.
destruct i as ( a & ? & ?).   exists (a ↑ (S v0)); split. rewrite liftP3; subst; intuition. simpl. constructor; trivial.
constructor. eauto. exists a; intuition. eapply L1. apply H1. trivial. trivial.

destruct i as (a & ? & ?). destruct (L2 Δ A0 n Γ0 Γ H1 v0 a g H2) as ( b& ? & ?). exists (b ↑ (S v0)); split.
replace n with (S v0 + (n - S v0)) by intuition. rewrite liftP2; intuition. rewrite H4. rewrite H0. intuition.
constructor. eauto. exists b; intuition.
(**)
destruct m; simpl in H1; try discriminate. destruct le_gt_dec; discriminate. injection H1; intros; subst; clear H1.
destruct (H m1 n Δ A0 Γ0) as (A' & ? & ?); trivial. replace A' with !s in *. clear H1; simpl in *. clear H.
destruct (H0 m2 (S n) Δ A0 (m1::Γ0)) as (B' & ? & ?); trivial. constructor. trivial. replace B' with !t in *. clear H; simpl in *. clear H0.
exists !u; intuition. apply cPi with s t; trivial.
apply Betas_S in H. destruct B'; try discriminate. unfold lift_rec in H; destruct le_gt_dec; discriminate. intuition.
apply Betas_S in H1. destruct A'; try discriminate. unfold lift_rec in H1; destruct le_gt_dec; discriminate. intuition.
(**)
destruct m; simpl in H2; try discriminate. destruct le_gt_dec; discriminate. injection H2; intros; subst; clear H2.
destruct (H m1 n Δ A0 Γ0) as (A' & ? & ?); trivial. replace A' with !s1 in *; simpl in *. clear H2. clear H.
destruct (H1 m2 (S n) Δ A0 (m1::Γ0)) as (M & ? & ?); trivial. constructor; trivial. clear H1.
assert (m1↑1#n::Γ ⊢ M ↑ 1 # (S n) : !s2). eapply SubjectRed. apply t0. trivial.
destruct (TypeCorrect (m1::Γ0) m2 M H2) as [ [w ?] | [w ?] ]. 
  subst; simpl in H1. apply gen_sort in H1 as (ss & ?  & ?). assert (m1::Γ0 ⊢ !w : !s2).
  apply conv_sort in H1. subst. constructor. trivial. apply wf_typ in H2; trivial.
  exists (Π(m1),!w);simpl; intuition. apply cLa with s1 s2 s3; trivial.

  assert (m1 ↑ 1 # n :: Γ ⊢ M ↑ 1 # (S n) : !w). change !w with (!w↑ 1 # (S n)). destruct (ins_in_env_wf Δ A0 n Γ0 Γ H3) as (a & ? ).
  apply wf_typ in t; trivial. eapply weakening. apply H5. constructor. apply H3. apply H6.
  destruct (Tx_ok (M↑ 1 # (S n))). replace w with s2 in *. exists (Π(m1),M); simpl; intuition.
  apply cLa with s1 s2 s3; trivial. apply conv_sort. eapply Shape_of_Type_Tv. apply H1. trivial. trivial. 
  destruct (Ts_Sigma_Shape (m1::Γ0) M w H5 s2) as ( M' & ? & ?). apply Ts_lift in H7; trivial.
  destruct (ins_in_env_wf Δ A0 (S n) (m1::Γ0) (m1↑1#n::Γ)) as (d & ?). constructor; trivial. apply wf_typ in H1; trivial.
  eapply ins_in_env_Sigma. apply H5. apply H8. apply Ts_lift in H7; trivial. constructor. apply H3. apply In_Sigma; trivial.
  exists (Π(m1),M'); simpl; split. eauto. apply cLa with s1 s2 s3; trivial. eauto.
  apply Betas_S in H2. destruct A'; try discriminate. unfold lift_rec in H2; destruct le_gt_dec; discriminate. intuition.
(**)
destruct m; simpl in H1; try discriminate. destruct le_gt_dec; discriminate. injection H1; intros; subst; clear H1.
destruct (H m1 n Δ A0 Γ0) as (P & ? & ?); trivial. apply Betas_Pi_inv in H1 as (C & D & ? & ?& ?). 
destruct P; try discriminate. unfold lift_rec in H1; destruct le_gt_dec; discriminate. injection H1; intros; subst; clear H1.
destruct (H0 m2 n Δ A0 Γ0) as (A' & ? & ?); trivial. destruct (Betas_diamond A (P1 ↑ 1 # n) (A' ↑ 1 # n) H4 H1) as ( Z & ?& ?).
apply Betas_lift_inv in H7. destruct H7 as (ZZ & ? & -> ).
apply Betas_lift_inv in H8. destruct H8 as (? & ? & ?). apply inv_lift in H9. subst.
exists (P2 [← m2 ]); split. change n with (0+n). rewrite substP1. intuition. apply cApp with x.
eapply Betas_typ_sound. apply H3. intuition. eapply Betas_typ_sound. apply H6. intuition.
(**)
destruct (H m n Δ A0 Γ0 H1 H2) as (a' & ? & ?).
destruct (Betac_confl A B b) as ( Z & ? &?). destruct (Betas_diamond A (a'↑ 1 # n) Z H3 H5) as (ZZ & ?& ?).
apply Betas_lift_inv in H7. destruct H7 as (aa & ? & -> ). exists aa; split. eauto.
eapply Betas_typ_sound. apply H4. trivial.
(* wf *)
inversion H.
(**)
inversion H0; subst; clear H0.
apply wf_typ in t; trivial.
destruct (H d n0 Δ A0 Δ0) as (? & ? & ?); trivial.
apply Betas_S in H0. destruct x; try discriminate. unfold lift_rec in H0; destruct le_gt_dec; discriminate.
eauto.
Qed.

(** With the previous lemma and Type Correctness, we can prove the full lemma:
if an hypothesis is not used in the term and it's type, we can simply remove
  it.*)
Theorem Strenghthening: forall Γ' M n T, Γ' ⊢ M ↑ 1 # n: T ↑ 1 # n -> forall Δ A Γ, ins_in_env Δ A n Γ Γ' ->  
 Γ ⊢ M : T.
intros. destruct WeakStrenghthening as ( ? & _ ). destruct (H1 Γ' (M↑ 1 # n) (T↑ 1 # n) H M n Δ A Γ) as (T' & ? & ?); trivial.
apply Betas_lift_inv in H2 as ( ? & ?& ?). apply inv_lift in H4; subst.
apply TypeCorrect in H as [ [ w ?]|[ w ?] ]. destruct T ; try discriminate. unfold lift_rec in H; destruct le_gt_dec; discriminate.
apply Betas_S in H2; subst. trivial. destruct (H1 Γ' (T↑1#n) !w H T n Δ A Γ) as (T'' & ? & ?); trivial. apply Betas_S in H4. 
destruct T'' ; try discriminate. unfold lift_rec in H4; destruct le_gt_dec; discriminate. eauto.
Qed.
  
  
End ut_strengh_mod.
