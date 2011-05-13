(** * Annotated Terms syntax 
In this file, we describe a slightly different syntax for terms: we add two
annotations to applications. If the head of an application if a function from
  [A] to [B], we had both informations in the application, in order to keep
track of the conversion during the typing that would be impossible to rebuild
after.
*)
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt.
Require Import Le.
Require Import Gt.
Require Import Plus.
Require Import Minus.
Require Import Bool.
Require Import base.

(** Term syntax. Notice the two additional [Term] in the application.*)
Module Type term_mod (X:term_sig).
Import X.

Inductive Term : Set:=
 | Var : Vars -> Term
 | Sort : Sorts -> Term
 | App : Term -> Term -> Term -> Term -> Term
 | Pi : Term -> Term -> Term
 | La :Term -> Term -> Term
.

(** this notation means that the product x y is annotated by the function space
A -> B.**)
Notation "x ·( A , B ) y" := (App x A B y) (at level 15, left associativity) : Typ_scope.
Notation "! s" := (Sort s) (at level 1) : Typ_scope.
Notation "# v" := (Var v) (at level 1) : Typ_scope.
Notation "'Π' ( U ) , V " := (Pi U V) (at level 20, U, V at level 30) : Typ_scope.
Notation "'λ' [ U ] , v " := (La U v) (at level 20, U , v at level 30) : Typ_scope.


Reserved Notation " t ↑ x # n " (at level 5, x at level 0, left associativity).

Delimit Scope Typ_scope with Typ. 

(** Same as for usual terms, we need lift and subst functions, with the very
same properties. They are just extended to deal with the two annotations.*)

Open Scope Typ_scope.

(* lift c n times *)
Fixpoint lift_rec (n:nat) (k:nat) (T:Term) {struct T} := match T with
   | # x =>  if le_gt_dec k x then Var (n+x) else Var x
   | ! s => Sort s
   | M ·(A, B) N=>  App (M ↑ n # k) (A↑ n # k) (B ↑ n # (S k)) (N ↑ n # k)
   | Π ( A ), B => Π (A ↑ n # k), (B ↑ n # (S k))
   | λ [ A ], M => λ [A ↑ n # k], (M ↑ n # (S k)) 
 end  
   where "t ↑ n # k" := (lift_rec n k t) : Typ_scope.

Notation " t ↑ n " := (lift_rec n 0 t) (at level 5, n at level 0, left associativity) : Typ_scope.


Lemma inv_lift : forall M N n m , M ↑ n # m = N ↑ n # m -> M = N.
intros M; induction M; destruct N; intros;
simpl in *; try (discriminate || intuition); (try (destruct (le_gt_dec m v) ; discriminate)).
destruct (le_gt_dec m v); destruct (le_gt_dec m v0) ; injection H; intros; subst; intuition.
apply plus_reg_l in H0; rewrite H0; trivial. 
elim (lt_irrefl m). apply le_lt_trans with v. trivial. induction n; intuition.
elim (lt_irrefl v0). apply lt_le_trans with m. induction n; intuition. trivial.
injection H; intros; subst; clear H. rewrite (IHM1 N1 n m H3); rewrite (IHM2 N2 n m H2); 
  rewrite (IHM3 N3 n (S m) H1); rewrite (IHM4 N4 n m H0); reflexivity.
injection H; intros; rewrite (IHM1 N1 n m H1); rewrite (IHM2 N2 n (S m) H0); reflexivity.
injection H; intros; rewrite (IHM1 N1 n m H1); rewrite (IHM2 N2 n (S m) H0); reflexivity.
Qed.

Lemma lift_rec0 : forall M n, M ↑ 0 # n = M.
induction M; intros; simpl.
destruct (le_gt_dec n v); reflexivity.
reflexivity.
rewrite IHM1; rewrite IHM2; rewrite IHM3; rewrite IHM4; reflexivity.
rewrite IHM1; rewrite IHM2; reflexivity.
rewrite IHM1; rewrite IHM2; reflexivity. 
Qed.

Lemma lift0 : forall M, M ↑ 0 = M .
intros; apply lift_rec0.
Qed.

Lemma liftP1 : forall M i j  k, (M ↑ j # i) ↑ k # (j+i) = M ↑ (j+k) # i.
intros M; induction M; intros;simpl.
destruct (le_gt_dec i v); simpl.
destruct (le_gt_dec (j+i) (j+v)); simpl. 
rewrite plus_assoc. replace (k+j) with (j+k) by (apply plus_comm).  trivial. 
apply plus_gt_reg_l in g. elim (lt_irrefl v).
apply lt_le_trans with i; intuition.
simpl; destruct (le_gt_dec (j+i)); intuition.
elim (lt_irrefl v).
apply lt_le_trans with i; intuition. induction j; intuition.
reflexivity.
rewrite IHM1. rewrite IHM2. rewrite IHM4. rewrite <- IHM3.
replace (j+S i) with (S(j+i)) by intuition. trivial.
rewrite IHM1; rewrite <-IHM2 ;replace (j+S i) with (S(j+i)) by intuition; reflexivity.
rewrite IHM1; rewrite <- IHM2 ;replace (j+S i) with (S(j+i)) by intuition; reflexivity.
Qed.

Lemma liftP2: forall M i j k n, i <= n ->
  (M ↑ j # i) ↑ k # (j+n) = (M ↑ k # n) ↑ j # i.
intro M; induction M; intros; simpl.
destruct (le_gt_dec i v); destruct (le_gt_dec n v).
simpl.
destruct le_gt_dec. destruct le_gt_dec.
rewrite 2! plus_assoc. replace (k+j) with (j+k) by (apply plus_comm).  trivial. 
elim (lt_irrefl v). apply lt_le_trans with i. induction k; intuition. trivial.
apply plus_gt_reg_l in g. elim (lt_irrefl v).
apply lt_le_trans with n; intuition.
simpl.
destruct le_gt_dec. apply plus_le_reg_l in l0. elim (lt_irrefl v).
apply lt_le_trans with n; intuition. destruct le_gt_dec. trivial.
elim (lt_irrefl v). apply lt_le_trans with i; intuition.
simpl. destruct le_gt_dec. elim (lt_irrefl n). apply lt_le_trans with i.
apply le_lt_trans with v; intuition. trivial. elim (lt_irrefl v).
apply lt_le_trans with n. apply lt_le_trans with i; intuition. trivial.
simpl. destruct le_gt_dec. elim (lt_irrefl v). apply lt_le_trans with n.
intuition. induction j; intuition. destruct le_gt_dec. elim (lt_irrefl i).
apply le_lt_trans with v; intuition. trivial.
trivial.

rewrite IHM1; intuition. replace (S(j+n)) with (j+S n) by intuition.
rewrite IHM2; intuition. rewrite IHM3; intuition. rewrite IHM4; intuition.
rewrite IHM1; intuition.
replace (S(j+n)) with (j+S n) by intuition.
rewrite (IHM2 (S i) j k (S n)); intuition.
rewrite IHM1; intuition.
replace (S(j+n)) with (j+S n) by intuition.
rewrite (IHM2 (S i) j k (S n) ); intuition.
Qed.

Lemma liftP3 : forall M i k j n , i <= k -> k <= (i+n) ->
  (M ↑ n # i) ↑ j # k = M ↑ (j+n) # i.
intro M; induction M; intros; simpl.
destruct (le_gt_dec i v); simpl.
destruct (le_gt_dec k (n+v)); intuition.
elim (lt_irrefl (i+n)). apply lt_le_trans with k.
apply le_lt_trans with (n+v). rewrite plus_comm. intuition. intuition. trivial.
destruct (le_gt_dec k v); intuition. elim (lt_irrefl k).
apply lt_le_trans with i.  apply le_lt_trans with v. trivial. intuition. trivial.
reflexivity.
rewrite IHM1; intuition. rewrite IHM2; intuition. rewrite IHM3; intuition. rewrite IHM4; intuition.
 change (S i + n) with (S (i+n)). intuition.
rewrite IHM1; intuition;rewrite IHM2; intuition. change (S i + n) with (S (i+n)). intuition.
rewrite IHM1; intuition; rewrite IHM2; intuition. change (S i + n) with (S (i+n)). intuition.
Qed.


Lemma lift_lift : forall M n m, (M ↑ m) ↑ n  = M ↑ (n+m).
intros.
apply liftP3; intuition.
Qed.



(* i = index to replace
  t = term we are replacing
 k = limit between free and bound indices
*)
Reserved Notation "M [ n ← N ]" (at level 5, n at level 0, left associativity).

Fixpoint subst_rec U T n {struct T} :=
 match T with
  | # x => match (lt_eq_lt_dec x n) with
      | inleft (left _) => # x (* x < n *)
      | inleft (right _) => U ↑ n  (* x = n *)
      | inright _ => # (x - 1) (* x > n *)
      end
  | ! s => ! s
  | M ·(A,B) N => (M [ n ← U ]) ·(A[n← U], B [ S n ← U]) ( N [ n ← U ]) 
  | Π ( A ), B => Π ( A [ n ← U ] ), (B [ S n ← U ]) 
  | λ [ A ], M => λ [ A [ n ← U ] ], (M [ S n ← U ]) 
end
    where " t [ n ← w ] " := (subst_rec w t n) : Typ_scope.


Notation " t [ ← w ] " := (subst_rec w t 0) (at level 5) : Typ_scope.


Lemma expand_term_with_subst : forall M n, (M ↑ 1 # (S n)) [ n ← #0 ] = M.
induction M; intros.
unfold lift_rec.
destruct (le_gt_dec (S n) v). unfold subst_rec.
destruct (lt_eq_lt_dec (1+v) n) as [[] | ].
apply le_not_lt in l. elim l. intuition.
elim (lt_irrefl v). apply lt_le_trans with (S (S v)). intuition. subst; trivial.
change (1+v) with (S v). destruct v; simpl; trivial.
simpl.
destruct (lt_eq_lt_dec v n) as [[] | ].
trivial.
simpl; subst; trivial.
rewrite <- plus_n_O. trivial.
elim (lt_irrefl n). apply lt_le_trans with v; intuition.
simpl; trivial.
simpl. rewrite IHM1. rewrite IHM2. rewrite IHM3. rewrite IHM4. reflexivity.
simpl. rewrite IHM1. rewrite IHM2. reflexivity.
simpl. rewrite IHM1. rewrite IHM2. reflexivity.
Qed.


Lemma substP1: forall M N i j k , 
  ( M [ j ← N] ) ↑ k # (j+i) = (M ↑ k # (S (j+i))) [ j ← (N ↑ k # i ) ].
intros M; induction M; intros.
simpl (#v [j ← N] ↑ k # (j+i)).
change (#v ↑ k # (S (j+i))) with  (if le_gt_dec (S (j+i)) v then #(k+v) else #v).
destruct (lt_eq_lt_dec v j) as [[] | ].
destruct (le_gt_dec (S (j+i)) v).
elim (lt_irrefl v). apply lt_le_trans with j; intuition.
apply le_trans with (S (j+i)); intuition.
simpl.
destruct (le_gt_dec (j+i) v).
elim (lt_irrefl v). apply lt_le_trans with j; intuition. apply le_trans with (j+i); intuition.
destruct (lt_eq_lt_dec v j) as [[] | ]. trivial.
subst. elim (lt_irrefl j);trivial.
elim (lt_irrefl j); apply lt_trans with v; trivial.
destruct (le_gt_dec (S(j+i)) v). subst.
elim (lt_irrefl j). apply lt_le_trans with (S (j+i)). intuition. trivial.
simpl. destruct (lt_eq_lt_dec v j) as [[] | ].
subst. elim (lt_irrefl j); trivial.
apply liftP2; intuition.
subst. elim (lt_irrefl j); trivial.
destruct (le_gt_dec (S (j+i)) v).
simpl.
destruct (le_gt_dec (j+i) (v-1)). destruct (lt_eq_lt_dec (k+v) j) as [[] | ].
elim (lt_irrefl j). apply lt_le_trans with v. trivial. induction k; intuition.
subst. elim (lt_irrefl v). apply lt_le_trans with (S(k+v+i)). intuition. trivial.
destruct v. apply lt_n_O in l; elim l. rewrite <- 2! pred_of_minus. replace (k+ S v) with (S (k+v)) by intuition.
simpl. trivial.
elim (lt_irrefl v). apply lt_le_trans with (S (j+i)). destruct v. apply lt_n_O in l; elim l. 
rewrite <- pred_of_minus in g. simpl in g. intuition. trivial.
simpl.
destruct (le_gt_dec (j+i) (v-1)). destruct (lt_eq_lt_dec v j) as [[] | ].
elim (lt_irrefl j); apply lt_trans with v; trivial.
subst. elim (lt_irrefl j); trivial.
elim (lt_irrefl v). apply lt_le_trans with (S (j+i)). intuition. 
destruct v. apply lt_n_O in l; elim l. rewrite <- pred_of_minus in l0. simpl in l0. intuition.
destruct (lt_eq_lt_dec) as [[] | ]. elim (lt_irrefl j); apply lt_trans with v; trivial.
subst. elim (lt_irrefl j); trivial. trivial.
simpl; trivial.
simpl. rewrite IHM1; intuition; rewrite IHM2; intuition. rewrite IHM4; intuition.
replace (S(S(j+i))) with (S((S j)+i)) by intuition.
rewrite <- (IHM3 N i (S j)  k ); intuition.
simpl; rewrite IHM1; intuition.
replace (S(S(j+i))) with (S((S j)+i)) by intuition.
rewrite <- (IHM2 N i (S j)  k ); intuition.
simpl; rewrite IHM1; intuition.
replace (S(S(j+i))) with ((S ((S j)+i))) by intuition.
rewrite <- (IHM2 N i (S j)  k ); intuition.
Qed.

Lemma substP2: forall M N i j n, i <= n ->
  (M ↑ j # i ) [ j+n ← N ] = ( M [ n ← N]) ↑ j # i .
intro M; induction M; intros; simpl.
destruct (le_gt_dec i v); destruct (lt_eq_lt_dec v n) as [[] | ].
simpl.
destruct (le_gt_dec i v).  destruct (lt_eq_lt_dec (j+v) (j+n)) as [[] | ].
reflexivity.
apply plus_reg_l in e. subst. elim (lt_irrefl n); trivial.
apply plus_lt_reg_l in l2. elim (lt_asym v n); trivial.
elim (lt_irrefl i). apply le_lt_trans with v; intuition. subst.
simpl.
destruct (lt_eq_lt_dec (j+n) (j+n)) as [[] | ].
apply lt_irrefl in l0; elim l0.
symmetry.
apply liftP3; intuition.
apply lt_irrefl in l0; elim l0.
simpl.
destruct (le_gt_dec i (v-1)). destruct (lt_eq_lt_dec (j+v) (j+n))as [[] | ].
apply plus_lt_reg_l in l2. elim (lt_asym  v n ); trivial.
apply plus_reg_l in e; subst. elim (lt_irrefl n); trivial.
destruct v. apply lt_n_O in l0; elim l0. rewrite <- 2! pred_of_minus. replace (j+ S v) with (S (j+v)) by intuition.
simpl. trivial.
unfold gt in g. unfold lt in g. rewrite <- pred_of_minus in g. 
rewrite <- (S_pred  v n l0) in g.
elim (lt_irrefl n). apply lt_le_trans with v; trivial. apply le_trans with i; trivial.
simpl. 
destruct (le_gt_dec i v).  elim (lt_irrefl i). apply le_lt_trans with v; trivial.
destruct (lt_eq_lt_dec v (j+n)) as [[] | ]. reflexivity.
subst. elim (lt_irrefl n). apply le_lt_trans with (j+n); intuition. 
elim (lt_irrefl n). apply lt_trans with v.  apply le_lt_trans with (j+n); intuition. trivial.
simpl. subst. 
elim (lt_irrefl n). apply lt_le_trans with i; intuition.
simpl. elim (lt_irrefl n). apply lt_le_trans with v; intuition.
apply le_trans with i; intuition.
trivial.

rewrite IHM1; intuition. replace (S(j+n)) with (j+(S n)) by intuition. rewrite IHM3; intuition.
rewrite IHM2; intuition; rewrite IHM4; intuition.
replace (S(j+n)) with (j+(S n)) by intuition.
rewrite IHM1; intuition;
rewrite <- (IHM2 N (S i) j (S n)); intuition.
replace (S(j+n)) with (j+(S n)) by intuition.
rewrite IHM1; intuition;
rewrite <- (IHM2 N (S i) j (S n)); intuition.
Qed.


Lemma substP3: forall M N i  k n, i <= k -> k <= i+n ->
  (M↑ (S n) # i) [ k← N] = M ↑ n # i.
intro M; induction M; intros; simpl.
destruct (le_gt_dec i v).
unfold subst_rec.
destruct (lt_eq_lt_dec (S(n+v)) k) as [[] | ].
elim (lt_irrefl (i+n)). apply lt_le_trans with k; intuition.
apply le_lt_trans with (v+n). intuition. rewrite plus_comm; intuition.
subst. replace (i+n) with (n+i) in H0 by (apply plus_comm) . replace (S (n+v)) with (n + S v) in H0 by intuition. 
apply plus_le_reg_l in H0. elim (lt_irrefl i). apply le_lt_trans with v; intuition.
simpl. rewrite <- minus_n_O. trivial.
simpl. destruct (lt_eq_lt_dec v k) as [[] | ].
reflexivity. subst. elim (lt_irrefl i). apply le_lt_trans with k; intuition.
elim (lt_irrefl k). apply lt_trans with v; trivial. apply lt_le_trans with i; intuition.

reflexivity.
rewrite IHM1; intuition;rewrite IHM4; intuition.
rewrite IHM2; intuition. change (S i + n) with (S (i+n)). rewrite IHM3; intuition.
change (S i + n) with (S (i+n)). intuition.
rewrite IHM1; intuition; rewrite <- (IHM2 N (S i) (S k) n); intuition.
change (S i + n) with (S (i+n)). intuition.
rewrite IHM1; intuition; rewrite <- (IHM2 N (S i) (S k) n); intuition.
change (S i + n) with (S (i+n)). intuition.
Qed.

Lemma substP4: forall M N P i j, 
   (M [ i← N]) [i+j ← P] = (M [S(i+j) ← P]) [i← N[j← P]].
intro M; induction M; intros; simpl.
destruct (lt_eq_lt_dec v i) as [[] | ] ; destruct (lt_eq_lt_dec v (S(i+j))) as [[] | ].
simpl.
destruct (lt_eq_lt_dec v (i+j)) as [[] | ]. destruct (lt_eq_lt_dec v i) as [[] | ].
trivial.
subst. apply lt_irrefl in l; elim l. elim ( lt_asym v i); trivial.
subst. rewrite plus_comm in l. elim (lt_irrefl i). induction j; simpl in *; intuition.
elim (lt_irrefl i). apply le_lt_trans with v;intuition. rewrite plus_comm in l1; intuition.  induction j; simpl in *; intuition.
subst. elim (lt_irrefl i). apply lt_trans with (S (i+j)); intuition.
elim (lt_irrefl i). apply lt_trans with (S (i+j)); intuition. apply lt_trans with v; trivial.
simpl. subst. destruct (lt_eq_lt_dec i i) as [[] | ].
elim (lt_irrefl i); trivial. apply substP2; intuition.
elim (lt_irrefl i); trivial.
subst. rewrite plus_comm in e0. apply succ_plus_discr in e0. elim e0.
subst. elim (lt_irrefl i). apply le_lt_trans with (i+j); intuition.
simpl.
destruct (lt_eq_lt_dec (v-1) (i+j)) as  [[] | ]. destruct (lt_eq_lt_dec v i) as [[] | ].
elim (lt_asym v i); trivial. subst. elim (lt_irrefl i); trivial.
trivial. rewrite <- e in l0. rewrite <- pred_of_minus in l0.
rewrite <- (S_pred  v i l) in l0. elim (lt_irrefl v); trivial.
apply lt_n_S in l1. elim (lt_irrefl v).
apply lt_trans with (S(i+j)); trivial.
rewrite <- pred_of_minus in l1. rewrite <- (S_pred  v i l) in l1. trivial. 
subst. simpl. rewrite <- minus_n_O.
destruct (lt_eq_lt_dec (i+j) (i+j)) as [[] | ].
elim (lt_irrefl (i+j)) ; trivial.
symmetry. apply substP3; intuition.
elim (lt_irrefl (i+j)) ; trivial.
simpl.
destruct (lt_eq_lt_dec (v-1) (i+j)) as  [[] | ].
elim (lt_irrefl v). apply lt_trans with (S (i+j)) ;trivial.
apply lt_n_S in l1. rewrite <- pred_of_minus in l1. rewrite <- (S_pred v i l) in l1. trivial.
apply eq_S in e. rewrite <- pred_of_minus in e. rewrite <- (S_pred v i l) in e.
subst. elim (lt_irrefl (S(i+j))); trivial.
destruct (lt_eq_lt_dec (v-1) i) as [[] | ].
elim (lt_irrefl v). apply le_lt_trans with i; trivial. destruct v. apply lt_n_O in l; elim l.
rewrite <- pred_of_minus in l2. simpl in l2. trivial.
destruct v. elim (lt_n_O i); trivial. rewrite <- pred_of_minus in e. simpl in e. subst.
rewrite <- pred_of_minus in l1. simpl in l1. elim (lt_irrefl i).
apply le_lt_trans with (i+j); intuition.
trivial.
trivial.
rewrite IHM1; rewrite IHM4; intuition. rewrite IHM2; intuition.
replace (S(S(i+j))) with (S((S i)+ j)) by intuition. rewrite <- IHM3; intuition.
rewrite IHM1; replace (S(S(i+j))) with (S((S i)+ j)) by intuition;
  rewrite <- (IHM2 N P (S i)); replace (S(i+j)) with ((S i)+ j) by intuition; intuition.
rewrite IHM1; replace (S(S(i+j))) with (S((S i)+j)) by intuition;
  rewrite <- (IHM2 N P (S i)); replace (S(i+j)) with ((S i)+ j) by intuition; intuition.
Qed.

Lemma subst_travers : 
 forall  M N P n, (M [← N]) [n ← P] = (M [n+1 ← P])[← N[n← P]].
intros.
rewrite plus_comm. change n with (O+n). apply substP4.
Qed.


End term_mod.
