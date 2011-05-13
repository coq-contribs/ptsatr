(** * Typing Environment for annotated terms .
  As for Terms, we define contexts of "Annotated" terms, with the very 
  safe function and tools as for the usual one.*)
Require Import base term.
Require Import List.
Require Import Peano_dec.
Require Import Compare_dec.
Require Import Lt Le Gt.

Module Type env_mod (X:term_sig) (TM:term_mod X).
Import TM.
(** Very naive definition of environment : list of term 

 be carefull, the usual written env Γ(x:A) is encoded in 
  A::Γ
**)

Definition Env := list Term.

Set Implicit Arguments.
(* General list manipulation, thanks to Bruno Barras *)
Inductive item (A:Type) (x:A): list A ->nat->Prop :=
  | item_hd: forall l:list A, (item x (cons x l) O)
  | item_tl: forall (l:list A)(n:nat)(y:A), item x l n -> item x (cons y l) (S n).

Hint Constructors item.

(* in the list Γ, the nth item is exactly x *)
Notation " x ↓ n ∈ Γ " := (item x Γ n) (at level 80, no associativity) : Typ_scope.


Lemma fun_item: forall A (u v:A)(Γ:list A)(n:nat), 
  u ↓ n ∈ Γ -> v ↓ n ∈ Γ -> u=v.
intros A u v e n;
generalize A u v e; clear A u v e.
induction n; intros.
inversion H; inversion H0.
rewrite <- H2 in H1; injection H1; trivial.
inversion H; inversion H0; subst.
injection H5; intros; subst.
apply IHn with (e:=l); trivial.
Qed.


(* cut a list by n *)
Inductive trunc (A:Type) : nat->list A ->list A->Prop :=
     trunc_O: forall (Γ:list A) , (trunc O Γ Γ)
   | trunc_S: forall (k:nat)(Γ Γ':list A)(x:A), trunc k Γ Γ' 
                -> trunc (S k) (cons x Γ) Γ'.

Hint Constructors trunc.

(* if there is a nth item in Γ, Γ is at least of size n+1 *)
Lemma item_trunc: forall (A:Type) (n:nat) (Γ:list A) (t:A), 
  t ↓ n ∈ Γ -> exists f , trunc (S n) Γ f.
intros A n; induction n; intros.
inversion H.
exists l.
apply trunc_S; apply trunc_O.
inversion H; subst.
destruct (IHn l t H2).
exists x.
apply trunc_S.
apply H0.
Qed.


(** insert a type d1 in an env Γ : BE CAREFULL d1 is not checked to be a valid type in Γ 
  it takes care of the DeBruijn lift when need **)
Inductive ins_in_env (Γ:Env ) (d1:Term): nat->Env -> Env  ->Prop :=
  | ins_O: ins_in_env Γ d1 O Γ (d1::Γ)
  | ins_S: forall (n:nat)(Δ Δ':Env )(d:Term), (ins_in_env Γ d1 n Δ Δ')
    -> ins_in_env Γ d1 (S n) (d::Δ) ( (d ↑ 1 # n)::Δ' ).

Hint Constructors ins_in_env.

Lemma ins_item_ge: forall (d':Term) (n:nat) (Γ Δ Δ':Env), 
  ins_in_env Γ d' n Δ Δ' -> 
  forall (v:nat), n<=v -> 
 forall (d:Term),  d ↓ v ∈ Δ  -> d ↓ (S v) ∈ Δ'.
induction n; intros.
inversion H; subst.
apply item_tl. exact H1.
inversion H; subst.
apply item_tl.
destruct v.
elim (le_Sn_O n H0).
apply IHn with (Γ:=Γ) (Δ:=Δ0).
trivial.
apply le_S_n ; trivial.
inversion H1.
exact H4.
Qed.

Lemma gt_O: forall v, ~ 0 > v.
intros; intro.
unfold gt in H. apply lt_n_O in H; trivial.
Qed.


Lemma ins_item_lt: forall (d':Term)(n:nat)(Γ Δ Δ':Env),
 ins_in_env Γ d' n Δ Δ' ->
 forall (v:nat), n > v ->
 forall (d:Term), d ↓ v ∈ Δ -> (d ↑ 1 # (n-S v)) ↓ v ∈ Δ' .
induction n; intros.
elim (gt_O H0).
inversion H; subst.
destruct v.
inversion H1; subst.
replace (S n -1) with n by intuition.
apply item_hd.
apply item_tl.
replace (S n - S (S v)) with (n -S v) by intuition. 
apply IHn with (Γ:=Γ) (Δ:=Δ0).
exact H3.
intuition.
inversion H1.
exact H4.
Qed.



Definition item_lift (t:Term) (Γ:Env) (n:nat) :=
     exists u ,  t= u ↑ (S n) /\  u ↓ n ∈ Γ .

Hint Unfold item_lift.
(* lifted version of item 
main use : if t ↓ n ⊂ Γ and we insert something in Γ, then 
we can still speak about t without think of the lift hidden by the insertion *)
Notation " t ↓ n ⊂ Γ " := (item_lift t Γ n) (at level 80, no associativity): Typ_scope.


Lemma ins_item_lift_lt: forall  (d':Term)(n:nat)(Γ Δ Δ':Env ),
 ins_in_env Γ d' n Δ Δ' ->
 forall (v:nat),  n>v ->
 forall (t:Term), t ↓ v ⊂ Δ  -> (t ↑ 1 # n) ↓ v ⊂ Δ'.
intros.
destruct H1 as [u [ P Q]].
rewrite P.
exists (u ↑ 1 # (n - S v) ); split.
replace n with ( S v + (n -  S v))  by intuition.
rewrite liftP2.
replace (S v+(n-S v)-S v) with (n-S v) by intuition.
reflexivity.
intuition.
clear t P.
inversion H; subst.
elim (gt_O H0).
inversion Q; subst.
replace (S n0 -1) with n0 by intuition.
apply item_hd.
apply item_tl.
replace (S n0 - S (S n)) with (n0 -S n) by intuition.
apply ins_item_lt with d' Γ Δ0; trivial.
intuition.
Qed.


(* substitute types in an env *)
(** if Γ == Γ1 (x:T) Γ2   and Γ1 ⊢ t:T  and Γ1 as size n 
   then Γ[n← t] = Γ1 (Γ2[x ← t])
**)

Inductive sub_in_env (Γ : Env) (t T:Term):
  nat -> Env -> Env -> Prop :=
    | sub_O :  sub_in_env Γ t T 0 (T :: Γ) Γ
    | sub_S :
        forall Δ Δ' n  B,
        sub_in_env Γ t T n Δ Δ' ->
        sub_in_env Γ t T (S n) (B :: Δ) ( B [n← t]  :: Δ').

Hint Constructors sub_in_env.


(* some item / subst related facts *)
(* move by one the position of the substitued part *)
Lemma nth_sub_sup :
   forall n Γ Δ Δ' t T,
   sub_in_env Γ t T n Δ Δ' ->
   forall v : nat, n <= v -> 
   forall d , d ↓ (S v) ∈ Δ -> d ↓ v ∈ Δ'.
intros n Γ Δ Δ' t T H; induction H; intros.
inversion H0; subst. trivial.
inversion H1; subst.
destruct v.
elim (le_Sn_O n H0).
apply item_tl.
apply le_S_n in H0.
apply IHsub_in_env; trivial.
Qed.

(* "partial" inversion : 
 if subs at the nth position of e, then we are going to substitute by
 the nth elem of e*)
Lemma nth_sub_eq :
   forall t T n Γ Δ Δ',
   sub_in_env Γ t T n Δ Δ' -> 
  forall d , d↓ n ∈ Δ -> T = d.
intros  t T n Γ Δ Δ' H; induction H; intros.
inversion H; trivial.
inversion H0; subst.
apply IHsub_in_env; trivial.
Qed.

(* if we subst at the nth position, 
 every item of e with ndx < n is n-lifted in f
*)
Lemma nth_sub_inf :
   forall t T n Γ Δ Δ',
   sub_in_env Γ t T n Δ Δ' ->
   forall v : nat,
   n > v ->
   forall d , d ↓ v ∈ Δ ->  ( d [n - S v ← t] )↓ v ∈ Δ' .
intros t T n Γ Δ Δ' H; induction H; intros.
elim (gt_O  H).
destruct v.
inversion H1; subst.
replace (S n -1) with n by intuition.
apply item_hd.
replace (S n - S (S v)) with (n - S v) by intuition.
inversion H1; subst.
apply item_tl.
apply gt_S_n in H0.
apply IHsub_in_env; trivial.
Qed.

(* same with item lift *)
Lemma nth_sub_item_inf :
   forall t T n g e f , sub_in_env g t T n e f ->
   forall v : nat, n > v ->
   forall u , item_lift u e v -> item_lift (subst_rec t u n) f v.
intros.
destruct H1 as [y [K L]].
exists (subst_rec t y (n-S v)); split.
rewrite K; clear u K.
pattern n at 1 .
replace n with (S v + ( n - S v)) by intuition.
apply substP2; intuition.
apply nth_sub_inf with T g  e; trivial.
Qed.

End env_mod.
